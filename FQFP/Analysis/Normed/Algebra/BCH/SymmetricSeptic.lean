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
    ‖symmetricBchSepticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by
  have hbudget : (symmetricBchSepticTermTable.map fun p ↦ p.2.natAbs).sum = 83256 := by
    decide +kernel
  have heval := WordTable.norm_eval_one_le_of_length ![a, b] symmetricBchSepticTermTable
    (by decide : 0 < 7) symmetricBchSepticTermTable_length (M := ‖a‖ + ‖b‖)
    (fun i ↦ by fin_cases i <;> simp)
  rw [hbudget] at heval
  rw [symmetricBchSepticTerm]
  calc
    _ ≤ ‖(967680 : ℚ)⁻¹‖ * (83256 * (‖a‖ + ‖b‖) ^ 7) :=
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left heval (norm_nonneg _))
    _ = (83256 / 967680 : ℝ) * (‖a‖ + ‖b‖) ^ 7 := by
      norm_num [← Rat.norm_cast_real]
      ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (by norm_num)

end PolynomialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- **Symmetric BCH through degree seven** with the source ninth-order remainder constant. -/
theorem norm_symmetric_bch_septic_sub_poly_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetricBch a b - (a + b) - symmetricBchCubicTerm a b - symmetricBchQuinticTerm a b -
      symmetricBchSepticTerm a b‖ ≤ 1000000000000 * (‖a‖ + ‖b‖) ^ 9 := by
  have ht := norm_symmetricBch_sub_sum_le a b hab 9
  rw [sum_logCoeff_positivePowerTrunc_eq_symmetric_septic a b] at ht
  norm_num at ht
  calc
    _ ≤ 3328 * (‖a‖ + ‖b‖) ^ 9 := by simpa only [sub_add_eq_sub_sub] using ht
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end FQFP.BCH
