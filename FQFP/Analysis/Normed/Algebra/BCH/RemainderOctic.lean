/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.RemainderSeptic

/-!
# Eighth-order BCH remainder

The truncation through degree seven retains the source constants and hypotheses.
Here `s = ‖a‖ + ‖b‖`.

## Main results

* `norm_bch_octic_remainder_small_s_le`: constant `1000` for `s < 1/10`.
* `norm_bch_octic_remainder_le`: constant `10000110` for `s < log 2`.
-/

@[expose] public noncomputable section
open NormedSpace Finset
namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The eighth-order BCH remainder has constant `1000` for `‖a‖ + ‖b‖ < 1/10`. -/
theorem norm_bch_octic_remainder_small_s_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - bchCubicTerm a b -
      bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b - bchSepticTerm a b‖ ≤
      1000 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  simpa only [← bch_septic_truncation_eq a b, sub_add_eq_sub_sub] using
    norm_bch_sub_sum_positivePowerTrunc_le a b 8 (K := 1000) hab hs_small
      (by norm_num [sum_range_succ])

/-- The eighth-order BCH remainder has constant `10000110` for `‖a‖ + ‖b‖ < log 2`. -/
theorem norm_bch_octic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - bchCubicTerm a b -
      bchQuarticTerm a b - bchQuinticTerm a b - bchSexticTerm a b - bchSepticTerm a b‖ ≤
      10000110 * (‖a‖ + ‖b‖) ^ 8 / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_sub_le_succ_pow_div_of_lt_log_two 7 (by positivity) hab
    (norm_bch_septic_remainder_le a b hab) (norm_bchSepticTerm_le a b)
    (norm_bch_octic_remainder_small_s_le a b hab) (by norm_num)
    (by intro hs; linarith only [hs])

end FQFP.BCH
