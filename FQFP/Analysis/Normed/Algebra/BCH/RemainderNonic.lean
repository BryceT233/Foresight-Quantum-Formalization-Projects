/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.RemainderOctic

/-!
# Ninth-order BCH remainder

The truncation through degree eight retains the source constants and hypotheses.
Here `s = ‖a‖ + ‖b‖`.

## Main results

* `norm_bch_nonic_remainder_small_s_le`: constant `1000` for `s < 1/10`.
* `norm_bch_nonic_remainder_le`: constant `100001110` for `s < log 2`.
-/

@[expose] public noncomputable section

open NormedSpace Finset

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The ninth-order BCH remainder has constant `1000` for `‖a‖ + ‖b‖ < 1/10`. -/
theorem norm_bch_nonic_remainder_small_s_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - bchCubicTerm a b -
      bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b -
      bchSepticTerm a b - bchOcticTerm a b‖ ≤
      1000 * (‖a‖ + ‖b‖) ^ 9 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  let y := exp a * exp b - 1
  let C := (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b +
    bchQuarticTerm a b + bchQuinticTerm a b + bchSexticTerm a b +
    bchSepticTerm a b + bchOcticTerm a b
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hpoly : ‖logPartialSum A 9 y - C‖ ≤ 768 * s ^ 9 := by
    rw [show C = ∑ k ∈ range 9,
      logCoeff k • positivePowerTrunc (expMulTerm a b) k 9 from bch_octic_truncation_eq a b]
    have hc : (∑ k ∈ range 9, ‖logCoeff k‖) ≤ (3 : ℝ) := by
      norm_num [sum_range_succ]
    calc
      _ ≤ (∑ k ∈ range 9, ‖logCoeff k‖) * 2 ^ (9 - 1) * s ^ 9 :=
        norm_logPartialSum_sub_sum_positivePowerTrunc_le_weighted a b hs_small 9
      _ ≤ 3 * 2 ^ (9 - 1) * s ^ 9 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by positivity)) (pow_nonneg hs 9)
      _ = _ := by norm_num
  have hexp : (Real.exp s - 1) ^ 9 ≤ 3 * s ^ 9 := by
    calc
      _ ≤ (1 + 1 / 10 : ℝ) ^ 9 * s ^ 9 :=
        real_exp_sub_one_pow_le_of_le hs hs_small.le (by norm_num) 9
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hs 9)
  simpa only [C, sub_add_eq_sub_sub] using
    norm_bch_sub_le_div_of_logPartialSum (B := 768) (E := 3) (K := 1000)
      a b C 9 hab (by norm_num) hpoly hexp (by norm_num)

/-- The ninth-order BCH remainder has constant `100001110` for `‖a‖ + ‖b‖ < log 2`. -/
theorem norm_bch_nonic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - bchCubicTerm a b -
      bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b -
      bchSepticTerm a b - bchOcticTerm a b‖ ≤
      100001110 * (‖a‖ + ‖b‖) ^ 9 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  obtain ⟨hd, hd1⟩ := exp_log_two_denominator_bounds hs hab
  by_cases hlarge : 1 / 10 ≤ s
  · exact norm_sub_le_succ_pow_div _ (bchOcticTerm a b) 8 hs hd hd1
      (norm_bch_octic_remainder_le a b hab) (norm_bchOcticTerm_le a b)
      (show 10000110 + 1 ≤ (100001110 : ℝ) * s by linarith only [hlarge])
  · have hsmall : s < 1 / 10 := lt_of_not_ge hlarge
    exact (norm_bch_nonic_remainder_small_s_le a b hab hsmall).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (1000 : ℝ) ≤ 100001110)
          (pow_nonneg hs 9)) hd.le)

end FQFP.BCH
