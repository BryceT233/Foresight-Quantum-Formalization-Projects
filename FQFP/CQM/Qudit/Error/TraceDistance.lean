/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for trace distance and its spectral formula.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/TraceDistance.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.InnerProductSpace.TraceNorm
public import FQFP.CQM.Qudit.Measurement.POVM
public import FQFP.CQM.Qudit.State.OperatorNorm

/-!
# Trace distance and measurement errors

The trace distance is half the trace norm of the difference of density operators.
The trace norm is defined by operator-norm duality and agrees, on self-adjoint operators,
with the sum of absolute eigenvalues. In particular the normalization here agrees with
physlib's `TrDistance`, without importing its matrix/Schatten hierarchy.

Every operator effect and every event in a finite POVM has probability difference at most
the trace distance. These estimates include singular states and zero-probability outcomes.

## Main definitions and results

* `Qudit.Density.traceDistance`: half the trace norm of the difference of density operators.
* `Qudit.Density.traceDistance_triangle`: the triangle inequality for trace distance.
* `Qudit.Density.abs_expectation_sub_le_traceDistance`: trace distance bounds bounded-effect error.
* `Qudit.POVM.abs_sum_probability_sub_le_traceDistance`: trace distance bounds outcome-event error.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory
open scoped BigOperators ComplexOrder

namespace Qudit

noncomputable section

namespace Density

variable {H : Qudit}

/-- A density operator has trace norm one. -/
lemma traceNorm_op (ρ : Density H) : LinearMap.traceNorm ρ.op = 1 := by
  rw [ρ.positive.traceNorm_eq_re_trace]
  change ρ.op.trace.re = 1
  rw [ρ.trace_one, Complex.one_re]

/-- Trace distance, with the standard factor of one half. -/
def traceDistance (ρ σ : Density H) : ℝ := LinearMap.traceNorm (ρ.op - σ.op) / 2

/-- Trace distance is nonnegative. -/
lemma traceDistance_nonneg (ρ σ : Density H) : 0 ≤ traceDistance ρ σ :=
  div_nonneg (LinearMap.traceNorm_nonneg _) (by norm_num)

/-- A state has zero distance from itself. -/
lemma traceDistance_self (ρ : Density H) : traceDistance ρ ρ = 0 := by
  simp only [traceDistance, sub_self, LinearMap.traceNorm_zero, zero_div]

/-- Trace distance is symmetric. -/
lemma traceDistance_comm (ρ σ : Density H) : traceDistance ρ σ = traceDistance σ ρ := by
  rw [traceDistance, ← LinearMap.traceNorm_neg, neg_sub, traceDistance]

/-- Trace distance separates density operators. -/
lemma traceDistance_eq_zero_iff (ρ σ : Density H) : traceDistance ρ σ = 0 ↔ ρ = σ := by
  rw [traceDistance, div_eq_zero_iff, or_iff_left (by norm_num : (2 : ℝ) ≠ 0),
    LinearMap.traceNorm_eq_zero_iff, sub_eq_zero, Density.ext_iff]

/-- The triangle inequality for density-state trace distance. -/
lemma traceDistance_triangle (ρ σ τ : Density H) :
    traceDistance ρ τ ≤ traceDistance ρ σ + traceDistance σ τ := by
  have h := LinearMap.traceNorm_add_le (ρ.op - σ.op) (σ.op - τ.op)
  rw [sub_add_sub_cancel] at h
  dsimp [traceDistance]
  linarith

/-- Trace distance between density states is at most one. -/
lemma traceDistance_le_one (ρ σ : Density H) : traceDistance ρ σ ≤ 1 := by
  have h := LinearMap.traceNorm_add_le ρ.op (-σ.op)
  rw [LinearMap.traceNorm_neg, ρ.traceNorm_op, σ.traceNorm_op, ← sub_eq_add_neg] at h
  dsimp [traceDistance]
  linarith

/-- Spectral formula for trace distance, independent of a choice of coordinates. -/
lemma traceDistance_eq_sum_abs_eigenvalues (ρ σ : Density H) :
    traceDistance ρ σ =
      (∑ i, |(ρ.positive.isSymmetric.sub σ.positive.isSymmetric).eigenvalues rfl i|) / 2 := by
  rw [traceDistance,
    (ρ.positive.isSymmetric.sub σ.positive.isSymmetric).traceNorm_eq_sum_abs_eigenvalues]

/-- The probability difference of any operator effect is bounded by trace distance. -/
lemma abs_expectation_sub_le_traceDistance (ρ σ : Density H) {E : Operator H}
    (hE₀ : 0 ≤ E) (hE₁ : E ≤ 1) :
    |ρ.expectation E - σ.expectation E| ≤ traceDistance ρ σ := by
  have htr : LinearMap.trace ℂ H.state (ρ.op - σ.op) = 0 := by
    change (ρ.op - σ.op).trace = 0
    simp
  simpa only [expectation, expectationComplex, traceDistance, mul_sub, map_sub,
    Complex.sub_re] using LinearMap.abs_re_trace_mul_le_half_traceNorm htr
      (LinearMap.nonneg_iff_isPositive.mp hE₀) hE₁

/-- Mixing both inputs with the same weights is jointly convex for trace distance. -/
lemma traceDistance_mix_le (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ₁ ρ₂ σ₁ σ₂ : Density H) :
    traceDistance (mix p hp₀ hp₁ ρ₁ ρ₂) (mix p hp₀ hp₁ σ₁ σ₂) ≤
      p * traceDistance ρ₁ σ₁ + (1 - p) * traceDistance ρ₂ σ₂ := by
  have heq : (mix p hp₀ hp₁ ρ₁ ρ₂).op - (mix p hp₀ hp₁ σ₁ σ₂).op =
      (p : ℂ) • (ρ₁.op - σ₁.op) + ((1 - p : ℝ) : ℂ) • (ρ₂.op - σ₂.op) := by
    simp only [op_mix, smul_sub]
    abel
  have h := LinearMap.traceNorm_add_le ((p : ℂ) • (ρ₁.op - σ₁.op))
    (((1 - p : ℝ) : ℂ) • (ρ₂.op - σ₂.op))
  rw [LinearMap.traceNorm_smul, LinearMap.traceNorm_smul, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp₀,
    abs_of_nonneg (sub_nonneg.mpr hp₁)] at h
  simp only [traceDistance, heq]
  linarith

/-- Isometric endomorphisms with nearby operators produce nearby density operators. -/
lemma traceNorm_map_sub_le (ρ : Density H) (U V : H ⟶ H) [IsIsometry U] [IsIsometry V] :
    LinearMap.traceNorm ((ρ.map U).op - (ρ.map V).op) ≤
      2 * ‖U.hom - V.hom‖ := by
  have hU : ‖U.hom‖ ≤ 1 :=
    (LIOfIsIsometry U).norm_toContinuousLinearMap_le
  have hV : ‖V.hom‖ ≤ 1 :=
    (LIOfIsIsometry V).norm_toContinuousLinearMap_le
  simp only [op_map]
  simpa only [ρ.traceNorm_op, mul_one, Module.End.mul_eq_comp, LinearMap.comp_assoc,
    Operator.norm_toContinuousLinearMap] using
    LinearMap.traceNorm_conjugate_sub_le ρ.op U.hom V.hom hU hV

/-- Operator-norm error bounds trace distance for isometric, in particular unitary, evolution. -/
lemma traceDistance_map_le_opNorm (ρ : Density H) (U V : H ⟶ H)
    [IsIsometry U] [IsIsometry V] :
    traceDistance (ρ.map U) (ρ.map V) ≤ ‖U.hom - V.hom‖ := by
  have h := ρ.traceNorm_map_sub_le U V
  unfold traceDistance
  linarith

/-- An explicit operator error bound transfers to density-state trace distance. -/
lemma traceDistance_map_le (ρ : Density H) (U V : H ⟶ H)
    [IsIsometry U] [IsIsometry V] {ε : ℝ}
    (hε : ‖U.hom - V.hom‖ ≤ ε) :
    traceDistance (ρ.map U) (ρ.map V) ≤ ε :=
  (ρ.traceDistance_map_le_opNorm U V).trans hε

end Density

namespace POVM

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- Every POVM outcome has probability error at most the trace distance. -/
lemma abs_probability_sub_le_traceDistance (M : POVM H ι) (ρ σ : Density H) (i : ι) :
    |M.probability ρ i - M.probability σ i| ≤ ρ.traceDistance σ :=
  ρ.abs_expectation_sub_le_traceDistance σ (M.op_nonneg i) (M.op_le_one i)

/-- Operator error bounds every outcome-probability error after unitary evolution. -/
lemma abs_probability_map_sub_le (M : POVM H ι) (ρ : Density H) (U V : H ⟶ H)
    [IsIsometry U] [IsIsometry V] {ε : ℝ}
    (hε : ‖U.hom - V.hom‖ ≤ ε) (i : ι) :
    |M.probability (ρ.map U) i - M.probability (ρ.map V) i| ≤ ε :=
  (M.abs_probability_sub_le_traceDistance _ _ i).trans (ρ.traceDistance_map_le U V hε)

/-- Every event, including the empty event, has probability error at most trace distance. -/
lemma abs_sum_probability_sub_le_traceDistance (M : POVM H ι) (ρ σ : Density H)
    (s : Finset ι) : |(∑ i ∈ s, M.probability ρ i) - ∑ i ∈ s, M.probability σ i| ≤
      ρ.traceDistance σ := by
  have h₀ : 0 ≤ ∑ i ∈ s, M.op i := Finset.sum_nonneg fun i _ => M.op_nonneg i
  have h₁ : ∑ i ∈ s, M.op i ≤ 1 := by
    rw [← M.sum_op]
    exact Finset.sum_le_univ_sum_of_nonneg fun i => M.op_nonneg i
  simpa only [probability, ← Density.expectation_sum] using
    ρ.abs_expectation_sub_le_traceDistance σ h₀ h₁

end POVM

end

end Qudit
