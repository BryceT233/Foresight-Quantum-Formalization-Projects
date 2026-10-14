/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Limits of ideal truncation and infinite coordinate evolution -/

@[expose] public section
noncomputable section

namespace Polynomial

lemma derivative_X_pow_not_mem_span (n : ℕ) (hn : 0 < n) :
    derivative (X ^ n : Polynomial ℝ) ∉
      Ideal.span ({X ^ n} : Set (Polynomial ℝ)) := by
  intro h
  have hdvd := Ideal.mem_span_singleton.mp h
  have hne : derivative (X ^ n : Polynomial ℝ) ≠ 0 := by
    rw [derivative_X_pow]
    exact mul_ne_zero (by simpa using (Nat.cast_ne_zero.mpr hn.ne' : (n : ℝ) ≠ 0))
      (pow_ne_zero _ X_ne_zero)
  have hle := natDegree_le_of_dvd hdvd hne
  have hlt := natDegree_derivative_lt (p := (X ^ n : Polynomial ℝ)) (by simpa using hn.ne')
  lia

end Polynomial

namespace Carleman

/-- Polynomials encoding successive normalized derivatives of a flat smooth function. -/
private def flatLiftPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => (k + 1 : ℝ)⁻¹ •
      (Polynomial.X ^ 2 * (flatLiftPolynomial k - Polynomial.derivative (flatLiftPolynomial k)))

/-- A nonzero smooth coordinate trajectory with zero initial data.
This proves that the infinite coordinate ODE alone does not imply uniqueness. -/
lemma exists_nonzero_zero_initial_coordinate_trajectory :
    ∃ y : ℕ → ℝ → ℝ,
      (∀ k, y k 0 = 0) ∧
      (∀ k t, HasDerivAt (y k) ((k + 1 : ℕ) * y (k + 1) t) t) ∧
      (∃ t, y 0 t ≠ 0) := by
  refine ⟨fun k t => (flatLiftPolynomial k).eval t⁻¹ * expNegInvGlue t, ?_, ?_, ?_⟩
  · intro k
    simp
  · intro k t
    convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (flatLiftPolynomial k) t using 1
    simp only [flatLiftPolynomial, Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Nat.cast_add, Nat.cast_one]
    have hk : (k + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  · refine ⟨1, ?_⟩
    simp [flatLiftPolynomial, (expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1)).ne']

end Carleman
