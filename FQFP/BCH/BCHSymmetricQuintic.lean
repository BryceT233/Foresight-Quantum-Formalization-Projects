/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.SymmetricSeries
public import FQFP.BCH.BCHSymmetric
public import FQFP.BCH.BCHTerms

/-!
# Symmetric BCH through degree five

The logarithm of the symmetric exponential product has only its linear, cubic, and quintic
components through degree six. The finite coefficient identity and the analytic logarithm
tail are estimated separately, preserving the source seventh-order remainder bound.

## Main results

* `norm_symmetricBchCubicTerm_le`, `norm_symmetricBchQuinticTerm_le`: polynomial bounds.
* `norm_symmetric_bch_quintic_sub_poly_le`: the source bound with coefficient `20000000000`.
-/

@[expose] public noncomputable section

open NormedSpace Finset

namespace FQFP.BCH

section PolynomialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- The cubic symmetric correction is bounded by the cube of the total input norm. -/
theorem norm_symmetricBchCubicTerm_le (a b : A) :
    ‖symmetricBchCubicTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 3 := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have ha : ‖a‖ ≤ s := le_add_of_nonneg_right (norm_nonneg b)
  have hb : ‖b‖ ≤ s := le_add_of_nonneg_left (norm_nonneg a)
  have hD (x y : A) (hx : ‖x‖ ≤ s) (hy : ‖y‖ ≤ s) :
      ‖x * (x * y - y * x) - (x * y - y * x) * x‖ ≤ 4 * s ^ 3 := by
    apply (norm_double_commutator_le x y).trans
    calc
      _ ≤ 4 * s ^ 2 * s := by gcongr
      _ = _ := by ring
  have h₁ := (norm_smul_le ((24 : ℚ)⁻¹) _).trans
    (mul_le_mul_of_nonneg_left (hD a b ha hb) (norm_nonneg _))
  have h₂ := (norm_smul_le ((12 : ℚ)⁻¹) _).trans
    (mul_le_mul_of_nonneg_left (hD b a hb ha) (norm_nonneg _))
  calc
    _ ≤ ‖(24 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)‖ +
        ‖(12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖ := by
      simpa only [symmetricBchCubicTerm, norm_neg] using norm_add_le
        (-((24 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)))
        ((12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b))
    _ ≤ ‖(24 : ℚ)⁻¹‖ * (4 * s ^ 3) + ‖(12 : ℚ)⁻¹‖ * (4 * s ^ 3) := add_le_add h₁ h₂
    _ = (1 / 2 : ℝ) * s ^ 3 := by
      norm_num [← Rat.norm_cast_real]
      ring
    _ ≤ s ^ 3 := mul_le_of_le_one_left (pow_nonneg hs 3) (by norm_num)

/-- The quintic symmetric correction is bounded by the fifth power of the total input norm. -/
theorem norm_symmetricBchQuinticTerm_le (a b : A) :
    ‖symmetricBchQuinticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  have hbudget : (symmetricBchQuinticTermTable.map fun p ↦ p.2.natAbs).sum = 1216 := by
    decide
  have heval := WordTable.norm_eval_one_le_of_length ![a, b] symmetricBchQuinticTermTable
    (by decide : 0 < 5) symmetricBchQuinticTermTable_length (M := ‖a‖ + ‖b‖)
    (fun i ↦ by fin_cases i <;> simp)
  rw [hbudget] at heval
  rw [symmetricBchQuinticTerm]
  calc
    _ ≤ ‖(5760 : ℚ)⁻¹‖ * (1216 * (‖a‖ + ‖b‖) ^ 5) :=
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left heval (norm_nonneg _))
    _ = (1216 / 5760 : ℝ) * (‖a‖ + ‖b‖) ^ 5 := by
      norm_num [← Rat.norm_cast_real]
      ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (by norm_num)

end PolynomialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- **Symmetric BCH through degree five** with the source seventh-order remainder constant. -/
theorem norm_symmetric_bch_quintic_sub_poly_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖symmetricBch a b - (a + b) - symmetricBchCubicTerm a b - symmetricBchQuinticTerm a b‖ ≤
      20000000000 * (‖a‖ + ‖b‖) ^ 7 := by
  have ht := norm_symmetricBch_sub_sum_le a b hab 7
  rw [sum_logCoeff_positivePowerTrunc_eq_symmetric a b] at ht
  norm_num at ht
  calc
    _ ≤ 704 * (‖a‖ + ‖b‖) ^ 7 := by simpa only [sub_add_eq_sub_sub] using ht
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end FQFP.BCH
