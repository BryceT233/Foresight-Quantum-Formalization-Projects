/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.InnerProductSpace.TraceNorm

/-!
# Spectral bounds for the trace norm

Diagonal matrix coefficients give lower bounds on the trace norm. Applied in an
eigenbasis of the difference of two positive operators, this gives the square-root
estimate used in the Fuchs–van de Graaf inequalities (Watrous, Lemma 3.34).

## Main results

* `LinearMap.IsPositive.re_trace_sub_mul_self_le_traceNorm` bounds the squared Hilbert–Schmidt
  distance between positive operators by the trace norm of the difference of their squares.
* `LinearMap.IsSymmetric.traceNorm_mul_eq_re_trace_sq` evaluates the real trace of the square of a
  self-adjoint operator satisfying a cubic identity.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

namespace LinearMap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The real trace of the square of a self-adjoint operator is the sum of squared eigenvalues. -/
lemma IsSymmetric.re_trace_mul_self_eq_sum_sq {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    (trace ℂ E (A * A)).re = ∑ i, (hA.eigenvalues rfl i) ^ 2 := by
  rw [trace_eq_sum_inner _ (hA.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Module.End.mul_apply, hA.apply_eigenvectorBasis, map_smul,
    inner_smul_right, (hA.eigenvectorBasis rfl).inner_eq_ite, ite_true, mul_one]
  simp [Complex.mul_re, pow_two]

/-- For positive operators, the squared Hilbert–Schmidt distance is bounded by the
trace norm of the difference of their squares. No invertibility is required. -/
lemma IsPositive.re_trace_sub_mul_self_le_traceNorm {A B : E →ₗ[ℂ] E}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    (trace ℂ E ((A - B) * (A - B))).re ≤ traceNorm (A * A - B * B) := by
  let hC := hA.isSymmetric.sub hB.isSymmetric
  let b := hC.eigenvectorBasis rfl
  rw [hC.re_trace_mul_self_eq_sum_sq]
  apply le_trans _ (sum_abs_re_inner_le_traceNorm b (A * A - B * B))
  apply Finset.sum_le_sum
  intro i _
  let c := hC.eigenvalues rfl i
  have he : (A - B) (b i) = (c : ℂ) • b i := hC.apply_eigenvectorBasis rfl i
  have hd : (inner ℂ (b i) ((A * A - B * B) (b i))).re =
      c * ((inner ℂ (b i) (A (b i))).re + (inner ℂ (b i) (B (b i))).re) := by
    have hop : A * A - B * B = (A - B) * A + B * (A - B) := by noncomm_ring
    rw [hop, add_apply, inner_add_right, Module.End.mul_apply,
      ← hC _ _, he, inner_smul_left, Module.End.mul_apply, he, map_smul,
      inner_smul_right]
    simp [Complex.mul_re, mul_add]
  have hc : (inner ℂ (b i) (A (b i))).re - (inner ℂ (b i) (B (b i))).re = c := by
    have h := congrArg (fun x ↦ (inner ℂ (b i) x).re) he
    simpa only [sub_apply, inner_sub_right, inner_smul_right, b.inner_eq_ite,
      ite_true, mul_one, Complex.sub_re, Complex.ofReal_re] using h
  have ha : 0 ≤ (inner ℂ (b i) (A (b i))).re := (hA.inner_nonneg_right _).1
  have hb : 0 ≤ (inner ℂ (b i) (B (b i))).re := (hB.inner_nonneg_right _).1
  change c ^ 2 ≤ _
  rw [hd]
  rcases le_total 0 c with h | h
  · exact le_trans (by nlinarith) (le_abs_self _)
  · exact le_trans (by nlinarith) (neg_le_abs _)

/-- A self-adjoint operator satisfying `A³ = s² A` has absolute eigenvalues zero or `s`.
Consequently its trace norm times `s` equals the real trace of its square. -/
lemma IsSymmetric.traceNorm_mul_eq_re_trace_sq {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric)
    {s : ℝ} (hs : 0 ≤ s) (hc : A * A * A = (s ^ 2 : ℂ) • A) :
    traceNorm A * s = (trace ℂ E (A * A)).re := by
  rw [hA.traceNorm_eq_sum_abs_eigenvalues, hA.re_trace_mul_self_eq_sum_sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  let c := hA.eigenvalues rfl i
  have he := congrArg (fun T : E →ₗ[ℂ] E ↦
    (inner ℂ (hA.eigenvectorBasis rfl i) (T (hA.eigenvectorBasis rfl i))).re) hc
  have hp : c * c * c = s ^ 2 * c := by
    simp only [Module.End.mul_apply, hA.apply_eigenvectorBasis, map_smul, smul_apply,
      inner_smul_right, (hA.eigenvectorBasis rfl).inner_eq_ite, ite_true, mul_one] at he
    simpa [Complex.mul_re, c, mul_assoc, pow_two] using he
  change |c| * s = c ^ 2
  rcases eq_or_ne c 0 with h | h
  · simp [h]
  · have hsq : c ^ 2 = s ^ 2 := by
      have : (c ^ 2 - s ^ 2) * c = 0 := by nlinarith [hp]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h)
    have habs : |c| = s := (sq_eq_sq₀ (abs_nonneg c) hs).mp (by simpa using hsq)
    rw [habs, ← pow_two, ← hsq]

end

end LinearMap
