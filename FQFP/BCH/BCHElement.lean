/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Analysis.Logarithm

/-!
# The Baker–Campbell–Hausdorff element

The BCH element is `log (exp a * exp b)`, using Mathlib's exponential and logarithm.
Its definition is available in a topological ring; the inverse identity needs the
Banach-algebra hypotheses and the sufficient bound `‖a‖ + ‖b‖ < log 2`.

## Main results

* `exp_bch`: the exponential of the BCH element is the product of exponentials.
* `bch_eq_add_of_commute`: commuting inputs give their sum in the convergence range.
* `bch_zero`, `zero_bch`: zero is a local identity for the BCH operation.

Quantitative commutator bounds are in `BCHCommutator`; the analytic exp/log facts
are in `FQFP.BCH.Analysis.Logarithm`.
-/

@[expose] public noncomputable section

open NormedSpace

namespace FQFP.BCH

/-- The BCH element is the logarithm of the ordered product of exponentials. -/
def bch {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]
    (a b : 𝔸) : 𝔸 := log (exp a * exp b)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **The structural BCH theorem** on the sufficient convergence range `‖a‖ + ‖b‖ < log 2`. -/
theorem exp_bch (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    exp (bch a b) = exp a * exp b :=
  exp_log (norm_exp_mul_exp_sub_one_lt_one a b hab)

/-- For commuting inputs, the BCH element is their sum on the convergence range. -/
theorem bch_eq_add_of_commute {a b : 𝔸} (h : Commute a b)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) : bch a b = a + b := by
  rw [bch, ← exp_add_of_commute h]
  exact log_exp_of_norm_lt _ ((norm_add_le a b).trans_lt hab)

/-- Zero is a right identity for BCH on the convergence range. -/
@[simp]
theorem bch_zero (a : 𝔸) (ha : ‖a‖ < Real.log 2) : bch a 0 = a := by
  simpa using bch_eq_add_of_commute (Commute.zero_right a) (by simpa using ha)

/-- Zero is a left identity for BCH on the convergence range. -/
@[simp]
theorem zero_bch (a : 𝔸) (ha : ‖a‖ < Real.log 2) : bch 0 a = a := by
  simpa using bch_eq_add_of_commute (Commute.zero_left a) (by simpa using ha)

end FQFP.BCH
