/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.Truncation
public import FQFP.Analysis.Normed.Algebra.BCH.Truncation
public import FQFP.Analysis.Normed.Algebra.Power
public import FQFP.Analysis.Normed.Algebra.BCH.RemainderQuintic

/-!
# Sixth-order BCH remainder

The fifth-degree BCH truncation has remainder bounded by the source constants.
Here `s = ‖a‖ + ‖b‖`.

## Main results

* `norm_bch_sextic_remainder_small_s_le`: constant `100` for `s < 1/10`.
* `norm_bch_sextic_remainder_le`: constant `100000` for `s < log 2`.
-/

@[expose] public noncomputable section
open Finset
namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The sixth-order BCH remainder has constant `100` for `‖a‖ + ‖b‖ < 1/10`. -/
theorem norm_bch_sextic_remainder_small_s_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b‖ ≤
      100 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  simpa only [← bch_quintic_truncation_eq_sum_positivePowerTrunc a b, sub_add_eq_sub_sub] using
    norm_bch_sub_sum_positivePowerTrunc_le a b 6 (K := 100) hab hs_small
      (by norm_num [sum_range_succ])

/-- The sixth-order BCH remainder has constant `100000` for `‖a‖ + ‖b‖ < log 2`. -/
theorem norm_bch_sextic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b‖ ≤
      100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_sub_le_succ_pow_div_of_lt_log_two 5 (by positivity) hab
    (norm_bch_quintic_remainder_le a b hab) (norm_bchQuinticTerm_le a b)
    (norm_bch_sextic_remainder_small_s_le a b hab) (by norm_num)
    (by intro hs; linarith only [hs])

end FQFP.BCH
