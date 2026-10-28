/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Choose.Cast
public import FQFP.RingTheory.PowerSeries.Noncommutative.Coefficients
public import FQFP.Analysis.Normed.Algebra.Exponential
public import FQFP.Analysis.Normed.Algebra.Logarithm
public import FQFP.Analysis.Normed.Algebra.PowerTruncation

/-!
# Exponential product series and truncation bounds

Cauchy products give one analytic tail estimate for every truncation degree.

## Main results

* `FQFP.norm_expMulTerm_le`.
* `FQFP.hasSum_expMulTerm`.
* `FQFP.norm_exp_mul_exp_sub_sum_le`.
* `FQFP.norm_exp_mul_exp_sub_quadratic_le`.
* `FQFP.norm_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le`.
* `FQFP.norm_logPartialSum_sub_sum_positivePowerTrunc_le`.
* `FQFP.norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted`.
-/

@[expose] public noncomputable section
open Finset Finset.Nat NormedSpace
namespace FQFP

/-- The scalar factorial convolution is the coefficient of the exponential at a sum. -/
lemma factorial_convolution (x y : ℝ) (n : ℕ) :
    (∑ ij ∈ antidiagonal n, (x ^ ij.1 / Nat.factorial ij.1) *
      (y ^ ij.2 / Nat.factorial ij.2)) = (x + y) ^ n / Nat.factorial n := by
  rw [(Commute.all x y).add_pow' n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := mem_antidiagonal.mp hij
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul, ← h, Nat.cast_add_choose]
  field_simp

/-- Uniform power-truncation errors control the corresponding finite logarithm. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow
    {B : Type*} [NormedRing B] [NormedAlgebra ℚ B]
    (y : B) (u : ℕ → B) (n : ℕ) {M : ℝ}
    (h : ∀ k < n, ‖y ^ k - positivePowerTrunc u k n‖ ≤ M) :
    ‖logPartialSum B n y - ∑ k ∈ range n, logCoeff k • positivePowerTrunc u k n‖ ≤
      (∑ k ∈ range n, ‖logCoeff k‖) * M := by
  rw [logPartialSum, ← sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ k ∈ range n, ‖logCoeff k • (y ^ k - positivePowerTrunc u k n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ range n, ‖logCoeff k‖ * M := by
      apply sum_le_sum
      intro k hk
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (h k (mem_range.mp hk)) (norm_nonneg _))
    _ = _ := (sum_mul ..).symm

/-- The absolute coefficient sum of a finite logarithm is at most its cutoff. -/
lemma sum_norm_logCoeff_le (n : ℕ) : (∑ k ∈ range n, ‖logCoeff k‖) ≤ (n : ℝ) := by
  calc
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := sum_le_sum fun k _ ↦ norm_logCoeff_le_one k
    _ = _ := by simp

section Norm
variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- A homogeneous exponential product term is bounded by the corresponding scalar term. -/
lemma norm_expMulTerm_le (a b : A) (n : ℕ) :
    ‖expMulTerm a b n‖ ≤ (‖a‖ + ‖b‖) ^ n / Nat.factorial n := by
  unfold expMulTerm
  refine (norm_sum_le _ _).trans ?_
  rw [← factorial_convolution]
  exact Finset.sum_le_sum fun ij _ ↦
    norm_mul_le_of_le (norm_exp_term_le a ij.1) (norm_exp_term_le b ij.2)

/-- Dropping the factorial gives a convenient homogeneous power bound. -/
lemma norm_expMulTerm_le_pow (a b : A) (n : ℕ) :
    ‖expMulTerm a b n‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  have hf : (1 : ℝ) ≤ Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  exact (norm_expMulTerm_le a b n).trans
    (div_le_self (pow_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)) n) hf)

variable [CompleteSpace A]

/-- The homogeneous factorial convolution sums to the ordered exponential product. -/
lemma hasSum_expMulTerm (a b : A) : HasSum (expMulTerm a b) (exp a * exp b) := by
  have ha : Summable fun i : ℕ ↦ ‖(Nat.factorial i : ℚ)⁻¹ • a ^ i‖ :=
    (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (norm_exp_term_le a)
  have hb : Summable fun i : ℕ ↦ ‖(Nat.factorial i : ℚ)⁻¹ • b ^ i‖ :=
    (Real.summable_pow_div_factorial ‖b‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (norm_exp_term_le b)
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb
  unfold expMulTerm
  rw [hs.of_norm.hasSum_iff]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb).symm.trans
    (by simp only [exp_eq_tsum_rat])

/-- Every exponential product truncation is bounded by the real exponential tail. -/
lemma norm_exp_mul_exp_sub_sum_le (a b : A) (n : ℕ) :
    ‖exp a * exp b - ∑ i ∈ range n, expMulTerm a b i‖ ≤
      Real.exp (‖a‖ + ‖b‖) - ∑ i ∈ range n,
        (‖a‖ + ‖b‖) ^ i / Nat.factorial i :=
  norm_sub_sum_le_real_exp_tail _ _ _ (hasSum_expMulTerm a b) (norm_expMulTerm_le a b) n

/-- The error after the quadratic part of an exponential product is bounded by the real tail. -/
lemma norm_exp_mul_exp_sub_quadratic_le (a b : A) :
    ‖exp a * exp b - 1 - (a + b) -
      (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2)‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) - (‖a‖ + ‖b‖) ^ 2 / 2 := by
  simpa [sum_range_succ, expMulTerm_two, Nat.factorial, sub_eq_add_neg,
    div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
      norm_exp_mul_exp_sub_sum_le a b 3

/-- In the small-norm region, every tail of order at least two is bounded by its power. -/
lemma norm_exp_mul_exp_sub_sum_le_pow (a b : A) (n : ℕ) (hn : 2 ≤ n)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖exp a * exp b - ∑ i ∈ range n, expMulTerm a b i‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  exact (norm_exp_mul_exp_sub_sum_le a b n).trans
    (real_exp_sub_sum_le_pow (by positivity) (by linarith only [hab]) n hn)

/-- Every power of the positive exponential product has a uniform homogeneous tail bound. -/
lemma norm_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (k n : ℕ) (hkn : k < n) :
    ‖(exp a * exp b - 1) ^ k - positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hy : ‖exp a * exp b - 1‖ ≤ 2 * s := by
    have ht := norm_exp_mul_exp_sub_one_le a b
    have he := real_exp_sub_one_sub_id_le_sq hs (show s ≤ 1 by linarith only [hab])
    have hs2 : s ^ 2 ≤ s := by nlinarith only [hs, hab]
    linarith only [ht, he, hs2]
  apply norm_pow_sub_positivePowerTrunc_le _ _ hs hy k n hkn
    (fun i _ _ ↦ norm_expMulTerm_le_pow a b i)
  intro j hj _
  have hsum : (∑ i ∈ range j, expMulTerm a b i) =
      1 + ∑ i ∈ range (j - 1), expMulTerm a b (i + 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by lia]
    rw [sum_range_succ', expMulTerm_zero, add_comm]
  have h := norm_exp_mul_exp_sub_sum_le_pow a b j hj hab
  simpa only [hsum, sub_add_eq_sub_sub] using h

/-- Retaining coefficient norms gives a weighted bound for the finite logarithm error. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (∑ k ∈ range n, ‖logCoeff k‖) * 2 ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  simpa only [mul_assoc] using
    norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow
      (exp a * exp b - 1) (expMulTerm a b) n
      (fun k hk ↦ norm_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le a b hab k n hk)

/-- The finite logarithm error is controlled uniformly by homogeneous power tails. -/
lemma norm_logPartialSum_sub_sum_positivePowerTrunc_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < 1 / 10) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulTerm a b) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (‖a‖ + ‖b‖) ^ n := by
  exact (norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted a b hab n).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sum_norm_logCoeff_le n) (by positivity)) (by positivity))

end Norm
end FQFP
