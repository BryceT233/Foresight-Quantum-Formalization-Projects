/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.HypothesisTesting
public import FQFP.CQM.Qudit.State.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Attainment in composite quantum hypothesis testing

For an arbitrary set of alternative states the worst-case false acceptance probability is
lower semicontinuous in the test. Compactness of the feasible effects gives a minimizer.
Scaling its acceptance effect gives a minimizer with exactly the prescribed type I error.
These are the attainment and support-positivity results of physlib's `OptimalHypothesisRate`.
-/

@[expose] public section

open scoped ComplexOrder

namespace Qudit.Density

variable {H : Qudit}

private lemma continuous_expectation (ρ : Density H) :
    Continuous (fun A : Operator H => ρ.expectation A) :=
  Complex.continuous_re.comp <| LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℂ H.state) ∘ₗ LinearMap.mulRight ℂ ρ.op)

private lemma exists_minimizing_effect (ρ : Density H) (ε : unitInterval) (S : Set (Density H)) :
    ∃ T : Set.Icc (0 : Operator H) 1, ρ.expectation (1 - T.val) ≤ ε ∧
      worstCaseTypeIIError T S = ρ.optimalTypeIIError ε S := by
  let B := Set.Icc (0 : Operator H) 1
  have : ProperSpace (Operator H) := FiniteDimensional.proper ℂ _
  have hB : IsCompact B := Metric.isCompact_of_isClosed_isBounded isClosed_Icc
    (CStarAlgebra.isBounded_of_bddAbove_of_bddBelow ⟨1, fun _ h => h.2⟩ ⟨0, fun _ h => h.1⟩)
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let F := {T : B | ρ.expectation (1 - T.val) ≤ ε}
  have hF : IsCompact F := by
    apply IsClosed.isCompact
    simp only [F, expectation_sub, expectation_one]
    exact isClosed_le (continuous_const.sub
      ((continuous_expectation ρ).comp continuous_subtype_val)) continuous_const
  have hne : F.Nonempty := by
    refine ⟨⟨1, LinearMap.nonneg_iff_isPositive.mpr LinearMap.isPositive_one, le_rfl⟩, ?_⟩
    change ρ.expectation (1 - 1) ≤ ε
    rw [expectation_sub, expectation_one, sub_self]
    exact ε.2.1
  have hsc : LowerSemicontinuous fun T : B => worstCaseTypeIIError T S := by
    apply lowerSemicontinuous_biSup
    intro σ _
    exact (((continuous_expectation σ).comp continuous_subtype_val).subtype_mk
      (fun T => σ.expectation_mem_Icc T.2.1 T.2.2)).lowerSemicontinuous
  obtain ⟨T, hT, hmin⟩ := (hsc.lowerSemicontinuousOn F).exists_isMinOn hne hF
  refine ⟨T, hT, le_antisymm ?_ (ρ.optimalTypeIIError_le ε S _ hT)⟩
  apply le_iInf
  rintro ⟨U, hU⟩
  exact isMinOn_iff.mp hmin U hU

/-- An optimal test exists and can use the entire type I error budget. -/
theorem exists_test_attaining_optimalTypeIIError (ρ : Density H) (ε : unitInterval)
    (S : Set (Density H)) :
    ∃ T : Set.Icc (0 : Operator H) 1, ρ.expectation (1 - T.val) = ε ∧
      worstCaseTypeIIError T S = ρ.optimalTypeIIError ε S := by
  obtain ⟨T, hT, hmin⟩ := exists_minimizing_effect ρ ε S
  rcases hT.eq_or_lt with he | hlt
  · exact ⟨T, he, hmin⟩
  rw [expectation_sub, expectation_one] at hlt
  have htarget := sub_nonneg.mpr ε.2.2
  have hpos : 0 < ρ.expectation T := by linarith
  let c := (1 - ε.val) / ρ.expectation T
  have hc₀ : 0 ≤ c := div_nonneg htarget hpos.le
  have hc₁ : c ≤ 1 := (div_le_one hpos).mpr (by linarith)
  have hle : (c : ℂ) • T.val ≤ T.val := smul_le_of_le_one_left T.2.1 (by exact_mod_cast hc₁)
  let U : Set.Icc (0 : Operator H) 1 :=
    ⟨(c : ℂ) • T.val, smul_nonneg (by exact_mod_cast hc₀) T.2.1, hle.trans T.2.2⟩
  have hU : ρ.expectation (1 - U.val) = ε := by
    rw [expectation_sub, expectation_one]
    change 1 - ρ.expectation ((c : ℂ) • T.val) = ε
    have hs : (c : ℂ) • T.val = c • T.val := (RCLike.real_smul_eq_coe_smul (K := ℂ) c T.val).symm
    rw [hs, expectation_smul]
    exact (congrArg (1 - ·) (div_mul_cancel₀ (1 - ε.val) hpos.ne')).trans (sub_sub_cancel _ _)
  exact ⟨U, hU, le_antisymm ((worstCaseTypeIIError_mono_effect S hle).trans_eq hmin)
    (ρ.optimalTypeIIError_le ε S U hU.le)⟩

/-- Zero optimal error is equivalent to a feasible effect killing every alternative support. -/
theorem optimalTypeIIError_eq_zero_iff (ρ : Density H) (ε : unitInterval) (S : Set (Density H)) :
    ρ.optimalTypeIIError ε S = 0 ↔ ∃ T : Set.Icc (0 : Operator H) 1,
      ρ.expectation (1 - T.val) ≤ ε ∧ ∀ σ ∈ S, σ.support ≤ LinearMap.ker T.val := by
  constructor
  · intro hz
    obtain ⟨T, hT, hmin⟩ := ρ.exists_test_attaining_optimalTypeIIError ε S
    refine ⟨T, hT.le, fun σ hσ => ?_⟩
    have hσT : (⟨σ.expectation T, σ.expectation_mem_Icc T.2.1 T.2.2⟩ : unitInterval) ≤
        worstCaseTypeIIError T S := le_iSup_of_le σ (le_iSup_of_le hσ le_rfl)
    rw [hmin, hz] at hσT
    have hp := LinearMap.nonneg_iff_isPositive.mp T.2.1
    exact (σ.expectation_eq_zero_iff hp).mp (le_antisymm hσT (σ.expectation_nonneg hp))
  · rintro ⟨T, hT, hk⟩
    apply le_antisymm ((ρ.optimalTypeIIError_le ε S T hT).trans ?_) bot_le
    exact iSup_le fun σ => iSup_le fun hσ =>
      ((σ.expectation_eq_zero_iff (LinearMap.nonneg_iff_isPositive.mp T.2.1)).mpr (hk σ hσ)).le

/-- Below unit type I error, an alternative supporting the null forces positive type II error. -/
theorem optimalTypeIIError_pos_of_absolutelyContinuous (ρ : Density H) {ε : unitInterval}
    (hε : ε < 1) {S : Set (Density H)} {σ : Density H} (hσ : σ ∈ S)
    (hac : ρ.AbsolutelyContinuous σ) : 0 < ρ.optimalTypeIIError ε S := by
  apply lt_of_le_of_ne bot_le
  intro hz
  obtain ⟨T, hT, hk⟩ := (ρ.optimalTypeIIError_eq_zero_iff ε S).mp hz.symm
  have hr := ((ρ.absolutelyContinuous_iff_support_le σ).mp hac).trans (hk σ hσ)
  rw [expectation_sub, expectation_one,
    (ρ.expectation_eq_zero_iff (LinearMap.nonneg_iff_isPositive.mp T.2.1)).mpr hr, sub_zero] at hT
  exact (unitInterval.coe_lt_one.mpr hε).not_ge hT

end Qudit.Density
