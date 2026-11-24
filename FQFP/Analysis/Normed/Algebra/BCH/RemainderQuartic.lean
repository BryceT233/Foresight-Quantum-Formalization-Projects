/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.Terms
public import FQFP.Analysis.Normed.Algebra.BCH.Truncation
public import FQFP.Analysis.Normed.Algebra.BCH.TermBounds
public import FQFP.Analysis.Normed.Algebra.BCH.Commutator
import FQFP.Algebra.Lie.BCH.Compatibility.LowDegree

/-!
# Fourth-order BCH remainder

The cubic truncation has error at most `200 s⁴ / (2 - exp s)`.

## Main results

* `norm_bch_quartic_remainder_small_s_le`: constant `20` for `s < 1/10`.
* `norm_bch_quartic_remainder_le`: the bound throughout `s < log 2`.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The order-4 BCH remainder on the ball of radius `1/10`. -/
theorem norm_bch_quartic_remainder_small_s_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b‖ ≤
      20 * (‖a‖ + ‖b‖) ^ 4 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  simpa only [← bch_cubic_truncation_eq_sum_positivePowerTrunc a b, sub_add_eq_sub_sub] using
    norm_bch_sub_sum_positivePowerTrunc_le a b 4 (K := 20) hab hs (by norm_num [sum_range_succ])

/-- The BCH remainder after the cubic term, with constant `200` on `s < log 2`,
where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bch_quartic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b‖ ≤
      200 * (‖a‖ + ‖b‖) ^ 4 / (2 - Real.exp (‖a‖ + ‖b‖)) :=
  norm_sub_le_succ_pow_div_of_lt_log_two 3 (by positivity) hab
    (norm_bch_sub_add_sub_bracket_le a b hab) (norm_bchCubicTerm_le a b)
    (norm_bch_quartic_remainder_small_s_le a b hab) (by norm_num)
    (by intro hs; linarith only [hs])

end FQFP.BCH
