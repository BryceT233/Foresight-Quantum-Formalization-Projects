/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.RemainderQuartic
public import FQFP.Analysis.Normed.Algebra.BCH.TermBounds
public import FQFP.Algebra.Lie.BCH.Associative.DynkinReeToolbox
import FQFP.Algebra.Lie.BCH.Compatibility.LowDegree

/-!
# Fifth-order BCH remainder

The quartic truncation has error at most `3000 s⁵ / (2 - exp s)`.

## Main results

* `norm_bch_quintic_remainder_small_s_le`: constant `40` for `s < 1/10`.
* `norm_bch_quintic_remainder_le`: the bound throughout `s < log 2`.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The order-5 BCH remainder on the ball of radius `1/10`. -/
theorem norm_bch_quintic_remainder_small_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b‖ ≤
      40 * (‖a‖ + ‖b‖) ^ 5 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  simpa only [← bch_quartic_truncation_eq_sum_positivePowerTrunc a b, sub_add_eq_sub_sub] using
    norm_bch_sub_sum_positivePowerTrunc_le a b 5 (K := 40) hab hs (by norm_num [sum_range_succ])

/-- The BCH remainder after the quartic term, with constant `3000` on `s < log 2`,
where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bch_quintic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b‖ ≤
      3000 * (‖a‖ + ‖b‖) ^ 5 / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_sub_le_succ_pow_div_of_lt_log_two 4 (by positivity) hab
    (norm_bch_quartic_remainder_le a b hab) (norm_bchQuarticTerm_le a b)
    (norm_bch_quintic_remainder_small_s_le a b hab) (by norm_num)
    (by intro hs; linarith only [hs])

end FQFP.BCH
