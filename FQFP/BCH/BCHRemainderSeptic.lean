/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHRemainderSextic

/-!
# Seventh-order BCH remainder

The truncation through degree six retains the source constants and hypotheses.
Here `s = ‖a‖ + ‖b‖`.

## Main results

* `norm_bch_septic_remainder_small_s_le`: constant `1000` for `s < 1/10`.
* `norm_bch_septic_remainder_le`: constant `1000010` for `s < log 2`.
-/

@[expose] public noncomputable section
open NormedSpace Finset
namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The seventh-order BCH remainder has constant `1000` for `‖a‖ + ‖b‖ < 1/10`. -/
theorem norm_bch_septic_remainder_small_s_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b‖ ≤
      1000 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  let y := exp a * exp b - 1
  let C := (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b +
    bchQuarticTerm a b + bchQuinticTerm a b + bchSexticTerm a b
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hpoly : ‖logPartialSum A 7 y - C‖ ≤ 448 * s ^ 7 := by
    have hC : C = ∑ k ∈ range 7,
        logCoeff k • positivePowerTrunc (expMulTerm a b) k 7 :=
      bch_sextic_truncation_eq a b
    rw [hC]
    simpa only [Nat.cast_ofNat, show (7 : ℝ) * 2 ^ (7 - 1) = 448 by norm_num] using
      norm_logPartialSum_sub_sum_positivePowerTrunc_le a b hs_small 7
  have hexp : (Real.exp s - 1) ^ 7 ≤ 2 * s ^ 7 := by
    calc
      _ ≤ (1 + 1 / 10 : ℝ) ^ 7 * s ^ 7 :=
        real_exp_sub_one_pow_le_of_le hs hs_small.le (by norm_num) 7
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hs 7)
  simpa only [C, sub_add_eq_sub_sub] using
    norm_bch_sub_le_div_of_logPartialSum (B := 448) (E := 2) (K := 1000)
      a b C 7 hab (by norm_num) hpoly hexp (by norm_num)

/-- The seventh-order BCH remainder has constant `1000010` for `‖a‖ + ‖b‖ < log 2`. -/
theorem norm_bch_septic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b‖ ≤
      1000010 * (‖a‖ + ‖b‖) ^ 7 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have he : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
         _ = 2 := Real.exp_log (by norm_num)
  have hd : 0 < 2 - Real.exp s := by linarith only [he]
  have hd1 : 2 - Real.exp s ≤ 1 := by linarith only [Real.add_one_le_exp s, hs]
  by_cases hlarge : 1 / 10 ≤ s
  · exact norm_sub_le_succ_pow_div _ (bchSexticTerm a b) 6 hs hd hd1
      (norm_bch_sextic_remainder_le a b hab) (norm_bchSexticTerm_le a b)
      (show 100000 + 1 ≤ (1000010 : ℝ) * s by linarith only [hlarge])
  · have hsmall : s < 1 / 10 := lt_of_not_ge hlarge
    exact (norm_bch_septic_remainder_small_s_le a b hab hsmall).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (1000 : ℝ) ≤ 1000010)
          (pow_nonneg hs 7)) hd.le)

end FQFP.BCH
