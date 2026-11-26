/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/HypothesisTesting.lean: the single-alternative Rényi converse bound.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.Attainment

/-!
# A Rényi bound on quantum hypothesis testing

A two-outcome measurement records acceptance and rejection in orthogonal basis states.
Data processing for the sandwiched trace functional bounds the contribution of the acceptance
outcome. This gives a finite-block upper bound on the negative logarithm of the type II error.
-/

@[expose] public noncomputable section

open scoped ENNReal

namespace Qudit.Density

variable {H : Qudit}

private def testPOVM (T : Set.Icc (0 : Operator H) 1) : POVM H (Fin 2) where
  op := ![T.val, 1 - T.val]
  positive i := by
    fin_cases i
    · exact LinearMap.nonneg_iff_isPositive.mp T.2.1
    · exact LinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr T.2.2)
  sum_op := by simp [Fin.sum_univ_two]

private def testChannel (T : Set.Icc (0 : Operator H) 1) : QuantumChannel H (std 2) :=
  (testPOVM T).measurePrepare fun i => pure (UnitState.ofBasis (ZBasis 2) i)

private lemma testChannel_eigen (T : Set.Icc (0 : Operator H) 1) (ρ : Density H) (i : Fin 2) :
    ((testChannel T).map ρ).op (ZBasis 2 i) =
      (((testPOVM T).probability ρ i : ℝ) : ℂ) • ZBasis 2 i := by
  rw [testChannel, POVM.map_measurePrepare]
  exact Ensemble.op_mix_ofPure_ofBasis_apply (ZBasis 2)
    ((testPOVM T).prepareEnsemble (fun j => pure (UnitState.ofBasis (ZBasis 2) j)) ρ).distribution i

private lemma acceptance_rpow_le_sandwichedTraceFunctional (ρ σ : Density H)
    (T : Set.Icc (0 : Operator H) 1) {α : ℝ} (hα : 1 < α) (h : ρ.AbsolutelyContinuous σ) :
    ρ.expectation T ^ α * σ.expectation T ^ (1 - α) ≤ ρ.sandwichedTraceFunctional σ α := by
  let Φ := testChannel T
  let p := fun i => (testPOVM T).probability ρ i
  let q := fun i => (testPOVM T).probability σ i
  have hs := Φ.sandwichedTraceFunctional_map_le ρ σ hα h
  rw [sandwichedTraceFunctional_eq_rpow_sum_of_common_eigenbasis _ _ hα (ZBasis 2) p q
    (testChannel_eigen T ρ) (testChannel_eigen T σ)
    ((testPOVM T).probability_nonneg ρ) ((testPOVM T).probability_nonneg σ)] at hs
  exact (Finset.single_le_sum (f := fun i : Fin 2 => p i ^ α * q i ^ (1 - α))
    (fun i _ => mul_nonneg (Real.rpow_nonneg ((testPOVM T).probability_nonneg ρ i) _)
      (Real.rpow_nonneg ((testPOVM T).probability_nonneg σ i) _)) (Finset.mem_univ 0)).trans hs

/-- The negative log of the optimal type II error in nats, with infinity for zero error. -/
def hypothesisTestingRelativeEntropy (ρ : Density H) (ε : unitInterval) (S : Set (Density H)) :
    ℝ≥0∞ :=
  if ρ.optimalTypeIIError ε S = 0 then ⊤ else ENNReal.ofReal (-Real.log (ρ.optimalTypeIIError ε S))

/-- For a positive optimal type II error the hypothesis-testing divergence is finite. -/
lemma hypothesisTestingRelativeEntropy_eq_of_pos (ρ : Density H) (ε : unitInterval)
    (S : Set (Density H)) (h : 0 < ρ.optimalTypeIIError ε S) :
    ρ.hypothesisTestingRelativeEntropy ε S =
      ENNReal.ofReal (-Real.log (ρ.optimalTypeIIError ε S)) :=
  ite_eq_right h.ne'

/-- Enlarging the alternative set cannot increase the testing divergence. -/
lemma hypothesisTestingRelativeEntropy_antitone (ρ : Density H) (ε : unitInterval) :
    Antitone (ρ.hypothesisTestingRelativeEntropy ε) := by
  intro S U hSU
  have he := ρ.optimalTypeIIError_mono ε hSU
  by_cases hS : ρ.optimalTypeIIError ε S = 0
  · simp [hypothesisTestingRelativeEntropy, hS]
  have hp : 0 < ρ.optimalTypeIIError ε S := lt_of_le_of_ne bot_le (Ne.symm hS)
  rw [hypothesisTestingRelativeEntropy_eq_of_pos _ _ _ hp,
    hypothesisTestingRelativeEntropy_eq_of_pos _ _ _ (hp.trans_le he)]
  exact ENNReal.ofReal_le_ofReal (neg_le_neg (Real.log_le_log hp he))

/-- For a supported singleton alternative, the negative log of the optimal type II error is
at most the sandwiched Rényi divergence plus the correction for the type I error budget. -/
theorem neg_log_optimalTypeIIError_singleton_le_sandwichedRenyi (ρ σ : Density H)
    (ε : unitInterval) (hε : ε < 1) (α : Set.Ioi (1 : ℝ)) (h : ρ.AbsolutelyContinuous σ) :
    -Real.log (ρ.optimalTypeIIError ε {σ}) ≤
      (ρ.sandwichedRenyiRelativeEntropy σ α).toReal +
        (α.val / (α.val - 1)) * (-Real.log (1 - ε.val)) := by
  obtain ⟨T, hT, hmin⟩ := ρ.exists_test_attaining_optimalTypeIIError ε {σ}
  rw [expectation_sub, expectation_one] at hT
  rw [worstCaseTypeIIError_singleton] at hmin
  have hp : ρ.expectation T = 1 - ε.val := by linarith
  have hq : σ.expectation T = (ρ.optimalTypeIIError ε {σ} : ℝ) := congrArg Subtype.val hmin
  have hp₀ : 0 < 1 - ε.val := sub_pos.mpr (unitInterval.coe_lt_one.mpr hε)
  have hq₀ : 0 < σ.expectation T := by
    rw [hq]
    exact ρ.optimalTypeIIError_pos_of_absolutelyContinuous hε (Set.mem_singleton _) h
  have hα := α.property
  have hQ := ρ.one_le_sandwichedTraceFunctional σ hα h
  have hl := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos (hp ▸ hp₀) _) (Real.rpow_pos_of_pos hq₀ _))
    (acceptance_rpow_le_sandwichedTraceFunctional ρ σ T hα h)
  rw [Real.log_mul (Real.rpow_pos_of_pos (hp ▸ hp₀) _).ne'
    (Real.rpow_pos_of_pos hq₀ _).ne', Real.log_rpow (hp ▸ hp₀), Real.log_rpow hq₀, hp] at hl
  rw [sandwichedRenyiRelativeEntropy, ite_eq_left h,
    ENNReal.toReal_ofReal (div_nonneg (Real.log_nonneg hQ) (sub_nonneg.mpr hα.le))]
  rw [← hq, div_mul_eq_mul_div, ← add_div]
  apply (le_div_iff₀ (sub_pos.mpr hα)).mpr
  linarith

end Qudit.Density
