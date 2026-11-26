/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.Basic
public import FQFP.Analysis.Normed.Algebra.ExponentialProduct

/-!
# Error of the homogeneous BCH truncation

On the ball `‖a‖ + ‖b‖ < 1 / 10`, the finite logarithm error and the exponential tail
give an explicit remainder bound at every truncation order.
A bound for the preceding order extends a local remainder estimate to `s < log 2`.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] [NormOneClass A]

/-- Bound the error after retaining the homogeneous BCH terms of degree strictly below `n`. -/
theorem norm_bch_sub_sum_positivePowerTrunc_le (a b : A) (n : ℕ) {K : ℝ}
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs : ‖a‖ + ‖b‖ < 1 / 10)
    (hK : (1 + 1 / 10 : ℝ) ^ n + (∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) ≤ K) :
    ‖bch a b - ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulTerm a b) k n‖ ≤
      K * (‖a‖ + ‖b‖) ^ n / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_bch_sub_le_div_of_logPartialSum a b _ n hab (by positivity)
    (norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted a b hs n)
    (real_exp_sub_one_pow_le_of_le (add_nonneg (norm_nonneg a) (norm_nonneg b)) hs.le
      (by norm_num) n) hK

/-- Extend a local remainder estimate to the BCH convergence ball by subtracting the next
homogeneous term from a remainder of order `n` outside the local radius `r`. -/
theorem norm_sub_le_succ_pow_div_of_lt_log_two {E : Type*} [SeminormedAddCommGroup E]
    {x y : E} (n : ℕ) {s r K M L : ℝ} (hs : 0 ≤ s) (hlog : s < Real.log 2)
    (hx : ‖x‖ ≤ K * s ^ n / (2 - Real.exp s)) (hy : ‖y‖ ≤ s ^ n)
    (hsmall : s < r → ‖x - y‖ ≤ M * s ^ (n + 1) / (2 - Real.exp s))
    (hML : M ≤ L) (hlarge : r ≤ s → K + 1 ≤ L * s) :
    ‖x - y‖ ≤ L * s ^ (n + 1) / (2 - Real.exp s) := by
  obtain ⟨hd, hd1⟩ := exp_log_two_denominator_bounds hs hlog
  rcases lt_or_ge s r with h | h
  · exact (hsmall h).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hML (pow_nonneg hs _)) hd.le)
  · exact norm_sub_le_succ_pow_div x y n hs hd hd1 hx hy (hlarge h)

end FQFP.BCH
