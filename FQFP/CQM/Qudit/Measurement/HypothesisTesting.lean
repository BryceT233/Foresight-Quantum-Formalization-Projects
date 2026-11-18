/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Dual
public import FQFP.CQM.Qudit.Measurement.Support
public import Mathlib.Topology.UnitInterval

/-!
# Composite quantum hypothesis testing

A test accepts the null state with effect `T` and rejects it with effect `1 - T`.
At type I error tolerance `ε`, minimize the worst-case acceptance probability on the
alternative set over all feasible effects. Both extrema are taken in the unit interval.
This is physlib's `OptimalHypothesisRate` on the existing qudit state and operator spaces.
-/

@[expose] public section

open scoped ComplexOrder

namespace Qudit

variable {H K : Qudit}

/-- Supremum of the false-acceptance probabilities over the alternative states. -/
noncomputable def worstCaseTypeIIError (T : Set.Icc (0 : Operator H) 1) (S : Set (Density H)) :
    unitInterval :=
  ⨆ σ ∈ S, (⟨σ.expectation T, σ.expectation_mem_Icc T.2.1 T.2.2⟩ : unitInterval)

/-- For a single alternative the worst-case error is its acceptance probability. -/
lemma worstCaseTypeIIError_singleton (T : Set.Icc (0 : Operator H) 1) (σ : Density H) :
    worstCaseTypeIIError T {σ} = ⟨σ.expectation T, σ.expectation_mem_Icc T.2.1 T.2.2⟩ :=
  iSup_singleton

/-- A larger acceptance effect increases the worst-case false-acceptance probability. -/
lemma worstCaseTypeIIError_mono_effect (S : Set (Density H)) :
    Monotone (fun T => worstCaseTypeIIError T S) := by
  intro T U h
  apply iSup_mono
  intro σ
  apply iSup_mono
  intro _
  change σ.expectation T.val ≤ σ.expectation U.val
  simpa only [Density.expectation_sub, sub_nonneg] using
    σ.expectation_nonneg (LinearMap.le_def.mp h)

namespace Density

/-- Infimum of worst-case type II errors subject to a type I error budget. -/
noncomputable def optimalTypeIIError (ρ : Density H) (ε : unitInterval) (S : Set (Density H)) :
    unitInterval :=
  ⨅ T : {T : Set.Icc (0 : Operator H) 1 // ρ.expectation (1 - T.val) ≤ ε},
    worstCaseTypeIIError T.val S

/-- Any feasible test gives an upper bound on the optimal error. -/
lemma optimalTypeIIError_le (ρ : Density H) (ε : unitInterval) (S : Set (Density H))
    (T : Set.Icc (0 : Operator H) 1) (hT : ρ.expectation (1 - T.val) ≤ ε) :
    ρ.optimalTypeIIError ε S ≤ worstCaseTypeIIError T S := by
  exact iInf_le (fun U : {U : Set.Icc (0 : Operator H) 1 // ρ.expectation (1 - U.val) ≤ ε} =>
    worstCaseTypeIIError U.val S) ⟨T, hT⟩

/-- Enlarging the alternative set can only increase the optimal worst-case error. -/
lemma optimalTypeIIError_mono (ρ : Density H) (ε : unitInterval) :
    Monotone (ρ.optimalTypeIIError ε) := by
  intro S S' h
  exact iInf_mono fun _ => iSup_le_iSup_of_subset h

/-- Relaxing the type I error budget can only decrease the optimal type II error. -/
lemma optimalTypeIIError_antitone (ρ : Density H) (S : Set (Density H)) :
    Antitone (fun ε => ρ.optimalTypeIIError ε S) := by
  intro ε δ h
  exact le_iInf fun T => ρ.optimalTypeIIError_le δ S T.1 (T.2.trans h)

/-- A state-independent randomized test rejects with probability exactly `ε`. -/
theorem optimalTypeIIError_le_one_sub (ρ : Density H) (ε : unitInterval) (S : Set (Density H)) :
    ρ.optimalTypeIIError ε S ≤ unitInterval.symm ε := by
  let p := unitInterval.symm ε
  have hI : (0 : Operator H) ≤ 1 := LinearMap.nonneg_iff_isPositive.mpr LinearMap.isPositive_one
  let T : Set.Icc (0 : Operator H) 1 :=
    ⟨(p : ℂ) • 1, smul_nonneg (by exact_mod_cast p.2.1) hI,
      smul_le_of_le_one_left hI (by exact_mod_cast p.2.2)⟩
  have he (τ : Density H) : τ.expectation T = p := by
    change τ.expectation ((p.val : ℂ) • 1) = p.val
    simp only [expectation, expectationComplex, smul_mul_assoc, one_mul, map_smul,
      smul_eq_mul, τ.trace_one, mul_one, Complex.ofReal_re]
  apply (ρ.optimalTypeIIError_le ε S T (by
    rw [expectation_sub, expectation_one, he, unitInterval.coe_symm_eq, sub_sub_cancel])).trans
  exact iSup_le fun σ => iSup_le fun _ => (he σ).le

/-- When the null state is among the alternatives the randomized test is optimal. -/
theorem optimalTypeIIError_eq_one_sub_of_mem (ρ : Density H) (ε : unitInterval)
    {S : Set (Density H)} (hρ : ρ ∈ S) : ρ.optimalTypeIIError ε S = unitInterval.symm ε := by
  apply le_antisymm (ρ.optimalTypeIIError_le_one_sub ε S)
  apply le_iInf
  intro T
  unfold worstCaseTypeIIError
  apply le_iSup_of_le ρ
  apply le_iSup_of_le hρ
  change 1 - ε.val ≤ ρ.expectation T.val
  have ht := T.property
  rw [expectation_sub, expectation_one] at ht
  linarith

/-- The effect accepting precisely the subspace supporting the null state. -/
noncomputable def supportEffect (ρ : Density H) : Set.Icc (0 : Operator H) 1 :=
  let M := POVM.ofSubmodule ρ.support
  ⟨M.op true, M.op_nonneg true, M.op_le_one true⟩

/-- Every test accepting the null state with certainty dominates its support projection. -/
lemma supportEffect_le_of_expectation_eq_one (ρ : Density H) (T : Set.Icc (0 : Operator H) 1)
    (h : ρ.expectation T = 1) : ρ.supportEffect ≤ T := by
  let P : Operator H := ρ.support.starProjection.toLinearMap
  have hP : P.adjoint = P := ρ.support.starProjection_isSymmetric.adjoint_eq
  have hT := LinearMap.nonneg_iff_isPositive.mp T.2.1
  have hTP : T.val * P = P := by
    ext x
    have hx := (ρ.expectation_eq_one_iff T.2.2).mp h (ρ.support.starProjection_apply_mem x)
    exact (sub_eq_zero.mp (show P x - T.val (P x) = 0 from hx)).symm
  have hPT : P * T.val = P := by
    simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hP, hT.adjoint_eq] using
      congrArg LinearMap.adjoint hTP
  have hPP : P * P = P :=
    LinearMap.ext fun x => Submodule.starProjection_eq_self_iff.mpr
      (ρ.support.starProjection_apply_mem x)
  change (T.val - P).IsPositive
  have hc := hT.conj_adjoint (1 - P)
  change ((1 - P) * (T.val * (1 - P).adjoint)).IsPositive at hc
  simpa only [map_sub, LinearMap.adjoint_one, hP, mul_sub, mul_one, hTP, sub_mul, one_mul,
    hPT, hPP, sub_self, sub_zero] using hc

/-- At zero type I error the support projection is optimal for every alternative set. -/
theorem optimalTypeIIError_zero (ρ : Density H) (S : Set (Density H)) :
    ρ.optimalTypeIIError 0 S = worstCaseTypeIIError ρ.supportEffect S := by
  have hc : ρ.expectation ρ.supportEffect = 1 :=
    (POVM.probability_ofSubmodule_eq_one_iff _ _).mpr le_rfl
  apply le_antisymm (ρ.optimalTypeIIError_le 0 S _ (by
    rw [expectation_sub, expectation_one, hc, sub_self]
    exact le_rfl))
  apply le_iInf
  intro T
  apply worstCaseTypeIIError_mono_effect S (ρ.supportEffect_le_of_expectation_eq_one T.val ?_)
  have ht := T.property
  rw [expectation_sub, expectation_one] at ht
  exact le_antisymm (ρ.expectation_le_one T.val.2.2) (sub_nonpos.mp ht)

/-- The support projection of the null state rejects every orthogonally supported alternative. -/
theorem optimalTypeIIError_eq_zero_of_isOrtho (ρ : Density H) (ε : unitInterval)
    {S : Set (Density H)} (h : ∀ σ ∈ S, σ.support ⟂ ρ.support) :
    ρ.optimalTypeIIError ε S = 0 := by
  apply le_antisymm _ bot_le
  apply (ρ.optimalTypeIIError_antitone S (show (0 : unitInterval) ≤ ε from bot_le)).trans
  change ρ.optimalTypeIIError 0 S ≤ 0
  rw [optimalTypeIIError_zero]
  exact iSup_le fun σ => iSup_le fun hσ =>
    ((POVM.probability_ofSubmodule_eq_zero_iff _ _).mpr (h σ hσ)).le

/-- With no alternatives there are no false acceptances. -/
lemma optimalTypeIIError_empty (ρ : Density H) (ε : unitInterval) :
    ρ.optimalTypeIIError ε ∅ = 0 :=
  ρ.optimalTypeIIError_eq_zero_of_isOrtho ε (by simp)

end Density

/-- Processing both hypotheses through a quantum channel cannot lower the optimal error. -/
theorem QuantumChannel.optimalTypeIIError_le_map (Φ : QuantumChannel H K) (ρ : Density H)
    (ε : unitInterval) (S : Set (Density H)) :
    ρ.optimalTypeIIError ε S ≤ (Φ.map ρ).optimalTypeIIError ε (Φ.map '' S) := by
  let D := Φ.toCPMap.dual.toSuperoperator
  have h1 : D 1 = 1 := Φ.toCPMap.isTracePreserving_iff_dual_one.mp Φ.tracePreserving
  have he (τ : Density H) (A : Operator K) : τ.expectation (D A) = (Φ.map τ).expectation A :=
    congrArg Complex.re (Φ.toCPMap.trace_dual τ.op A)
  apply le_iInf
  rintro ⟨T, hT⟩
  have hp (A : Operator K) (hA : 0 ≤ A) : 0 ≤ D A :=
    LinearMap.nonneg_iff_isPositive.mpr (Φ.toCPMap.dual.completelyPositive.isPositive A
      (LinearMap.nonneg_iff_isPositive.mp hA))
  let U : Set.Icc (0 : Operator H) 1 := ⟨D T.val, hp _ T.2.1, by
    simpa only [map_sub, h1, sub_nonneg] using hp (1 - T.val) (sub_nonneg.mpr T.2.2)⟩
  apply (ρ.optimalTypeIIError_le ε S U (by
    change ρ.expectation (1 - D T.val) ≤ ε
    rwa [← h1, ← map_sub, he])).trans
  apply le_of_eq
  simp only [worstCaseTypeIIError, iSup_image, U, he]

end Qudit
