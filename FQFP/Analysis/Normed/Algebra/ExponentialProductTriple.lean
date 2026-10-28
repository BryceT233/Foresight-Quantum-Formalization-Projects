/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.PowerSeries.Noncommutative.ExponentialProductCoefficients
public import FQFP.Analysis.Normed.Algebra.ExponentialProduct

/-!
# Ordered products of three exponentials

The factorial convolution controls every homogeneous coefficient and tail of an ordered
three-factor exponential product. Positive-degree power truncations then give finite
logarithm approximations on a common input ball of radius `1/4`.

## Main results

* `norm_expMulMulTerm_le`, `hasSum_expMulMulTerm`: factorial coefficient bounds and summation.
* `norm_exp_mul_exp_mul_exp_sub_sum_le`: analytic tails of the product.
* `norm_log_exp_mul_exp_mul_exp_sub_sum_le`: finite homogeneous logarithm approximation.
-/

@[expose] public noncomputable section

open Finset Finset.Nat NormedSpace

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- Each homogeneous term of a three-factor product has the scalar factorial bound. -/
lemma norm_expMulMulTerm_le (a b c : A) (n : ℕ) :
    ‖expMulMulTerm a b c n‖ ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ n / Nat.factorial n := by
  unfold expMulMulTerm
  refine (norm_sum_le _ _).trans ?_
  rw [← factorial_convolution]
  exact sum_le_sum fun ij _ ↦
    norm_mul_le_of_le (norm_expMulTerm_le a b ij.1) (norm_exp_term_le c ij.2)

/-- Dropping the factorial gives a homogeneous power majorant. -/
lemma norm_expMulMulTerm_le_pow (a b c : A) (n : ℕ) :
    ‖expMulMulTerm a b c n‖ ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  have hf : (1 : ℝ) ≤ Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  exact (norm_expMulMulTerm_le a b c n).trans
    (div_le_self (by positivity) hf)

variable [CompleteSpace A]

/-- The convolution sums to the ordered product of three exponentials. -/
lemma hasSum_expMulMulTerm (a b c : A) :
    HasSum (expMulMulTerm a b c) (exp a * exp b * exp c) := by
  have hab : Summable fun i : ℕ ↦ ‖expMulTerm a b i‖ :=
    (Real.summable_pow_div_factorial (‖a‖ + ‖b‖)).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (norm_expMulTerm_le a b)
  have hc : Summable fun i : ℕ ↦ ‖(Nat.factorial i : ℚ)⁻¹ • c ^ i‖ :=
    (Real.summable_pow_div_factorial ‖c‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (norm_exp_term_le c)
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hab hc
  unfold expMulMulTerm
  rw [hs.of_norm.hasSum_iff]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hab hc).symm.trans
    (by
      rw [(hasSum_expMulTerm a b).tsum_eq]
      simp only [exp_eq_tsum_rat])

/-- Every truncation tail is bounded by the corresponding real exponential tail. -/
lemma norm_exp_mul_exp_mul_exp_sub_sum_le (a b c : A) (n : ℕ) :
    ‖exp a * exp b * exp c - ∑ i ∈ range n, expMulMulTerm a b c i‖ ≤
      Real.exp (‖a‖ + ‖b‖ + ‖c‖) -
        ∑ i ∈ range n, (‖a‖ + ‖b‖ + ‖c‖) ^ i / Nat.factorial i :=
  norm_sub_sum_le_real_exp_tail _ _ _ (hasSum_expMulMulTerm a b c)
    (norm_expMulMulTerm_le a b c) n

/-- The distance of the three-factor product from one is controlled by the scalar exponential. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_le (a b c : A) :
    ‖exp a * exp b * exp c - 1‖ ≤ Real.exp (‖a‖ + ‖b‖ + ‖c‖) - 1 := by
  simpa only [sum_range_one, expMulMulTerm_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] using norm_exp_mul_exp_mul_exp_sub_sum_le a b c 1

/-- On the quarter-radius ball, every product tail of degree at least two is bounded by a power. -/
lemma norm_exp_mul_exp_mul_exp_sub_sum_le_pow (a b c : A) (n : ℕ) (hn : 2 ≤ n)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) :
    ‖exp a * exp b * exp c - ∑ i ∈ range n, expMulMulTerm a b c i‖ ≤
      (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  exact (norm_exp_mul_exp_mul_exp_sub_sum_le a b c n).trans
    (real_exp_sub_sum_le_pow (by positivity) (by linarith only [habc]) n hn)

/-- The positive part of a small exponential product has norm at most twice the input scale. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_le_two_mul (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) :
    ‖exp a * exp b * exp c - 1‖ ≤ 2 * (‖a‖ + ‖b‖ + ‖c‖) := by
  let s := ‖a‖ + ‖b‖ + ‖c‖
  have hs : 0 ≤ s := by positivity
  have ht := norm_exp_mul_exp_mul_exp_sub_one_le a b c
  have he := real_exp_sub_one_sub_id_le_sq hs (show s ≤ 1 by linarith only [habc])
  have hs2 : s ^ 2 ≤ s := by nlinarith only [hs, habc]
  linarith only [ht, he, hs2]

/-- Every power of the positive product has the common homogeneous truncation bound. -/
lemma norm_exp_mul_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (k n : ℕ) (hkn : k < n) :
    ‖(exp a * exp b * exp c - 1) ^ k - positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  let s := ‖a‖ + ‖b‖ + ‖c‖
  have hs : 0 ≤ s := by positivity
  apply norm_pow_sub_positivePowerTrunc_le _ _ hs
    (norm_exp_mul_exp_mul_exp_sub_one_le_two_mul a b c habc) k n hkn
    (fun i _ _ ↦ norm_expMulMulTerm_le_pow a b c i)
  intro j hj _
  have hsum : (∑ i ∈ range j, expMulMulTerm a b c i) =
      1 + ∑ i ∈ range (j - 1), expMulMulTerm a b c (i + 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by lia]
    rw [sum_range_succ', expMulMulTerm_zero, add_comm]
  have h := norm_exp_mul_exp_mul_exp_sub_sum_le_pow a b c j hj habc
  simpa only [hsum, sub_add_eq_sub_sub] using h

/-- The finite logarithm of the product is approximated by its homogeneous power truncations. -/
lemma norm_logPartialSum_exp_mul_exp_mul_exp_sub_sum_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (n : ℕ) :
    ‖logPartialSum A n (exp a * exp b * exp c - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  have h := norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow
    (exp a * exp b * exp c - 1) (expMulMulTerm a b c) n
    (fun k hk ↦ norm_exp_mul_exp_mul_exp_sub_one_pow_sub_positivePowerTrunc_le a b c habc k n hk)
  apply h.trans
  exact le_trans (mul_le_mul_of_nonneg_right (sum_norm_logCoeff_le n) (by positivity))
    (by rw [mul_assoc])

/-- The logarithm of a small three-factor product has a uniform finite homogeneous approximation. -/
theorem norm_log_exp_mul_exp_mul_exp_sub_sum_le (a b c : A)
    (habc : ‖a‖ + ‖b‖ + ‖c‖ < 1 / 4) (n : ℕ) :
    ‖log (exp a * exp b * exp c) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulMulTerm a b c) k n‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (‖a‖ + ‖b‖ + ‖c‖) ^ n := by
  let s := ‖a‖ + ‖b‖ + ‖c‖
  let y := exp a * exp b * exp c - 1
  have hs : 0 ≤ s := by positivity
  have hy : ‖y‖ ≤ 2 * s := norm_exp_mul_exp_mul_exp_sub_one_le_two_mul a b c habc
  have htail : ‖log (exp a * exp b * exp c) - logPartialSum A n y‖ ≤
      2 ^ (n + 1) * s ^ n := by
    rw [show exp a * exp b * exp c = 1 + y by dsimp [y]; abel]
    exact norm_log_one_add_sub_logPartialSum_le_two_mul y n hs habc hy
  have hfinite := norm_logPartialSum_exp_mul_exp_mul_exp_sub_sum_le a b c habc n
  calc
    _ ≤ ‖log (exp a * exp b * exp c) - logPartialSum A n y‖ +
        ‖logPartialSum A n y -
          ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expMulMulTerm a b c) k n‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 ^ (n + 1) * s ^ n + (n : ℝ) * 2 ^ (n - 1) * s ^ n :=
      add_le_add htail hfinite
    _ = _ := by ring

end FQFP
