/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.SymmetricQuintic

/-!
# Symmetric BCH through degree seven

The seventh-degree correction is homogeneous and bounded by the seventh power of the
input radius. The finite logarithm identity includes the cancellation of degree eight,
so the symmetric BCH remainder has order nine on the quarter-radius neighborhood.

## Main results

* `norm_symmetricBchSepticTerm_le`: the homogeneous polynomial norm bound.
* `norm_symmetric_bch_septic_sub_poly_le`: the source ninth-order remainder bound.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

section PolynomialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- The septic symmetric correction is bounded by the seventh power of the total input norm. -/
theorem norm_symmetricBchSepticTerm_le (a b : A) :
    ‖symmetricBchSepticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 :=
  WordTable.norm_smul_eval_one_pair_le _ symmetricBchSepticTermTable a b (by decide)
    symmetricBchSepticTermTable_length (by decide +kernel)

end PolynomialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- **Symmetric BCH through degree seven** with the source ninth-order remainder constant. -/
theorem norm_symmetric_bch_septic_sub_poly_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetricBch a b - (a + b) - symmetricBchCubicTerm a b - symmetricBchQuinticTerm a b -
      symmetricBchSepticTerm a b‖ ≤ 1000000000000 * (‖a‖ + ‖b‖) ^ 9 := by
  simpa only [sub_add_eq_sub_sub] using
    norm_symmetricBch_sub_le_of_sum_eq a b hab 9 (C := 1000000000000)
      (sum_logCoeff_positivePowerTrunc_eq_symmetric_septic a b) (by norm_num)

end FQFP.BCH
