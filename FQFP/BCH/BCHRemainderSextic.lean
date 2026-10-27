/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.BCHTruncation
public import FQFP.BCH.Analysis.ExponentialProduct
public import FQFP.BCH.Analysis.Power
public import FQFP.BCH.BCHRemainderQuintic

/-!
# Sixth-order BCH remainder

The fifth-degree BCH truncation has remainder bounded by the source constants.
Here `s = ‖a‖ + ‖b‖`.

## Main results

* `norm_bch_sextic_remainder_small_s_le`: constant `100` for `s < 1/10`.
* `norm_bch_sextic_remainder_le`: constant `100000` for `s < log 2`.
-/

@[expose] public noncomputable section
open NormedSpace Finset
namespace FQFP.BCH

private lemma logPartialSum_six {R : Type*} [Ring R] [Algebra ℚ R] (x : R) :
    logPartialSum R 6 x = x - (2 : ℚ)⁻¹ • x ^ 2 + (3 : ℚ)⁻¹ • x ^ 3 -
      (4 : ℚ)⁻¹ • x ^ 4 + (5 : ℚ)⁻¹ • x ^ 5 := by
  norm_num [logPartialSum, logCoeff, sum_range_succ]
  module

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The finite logarithm polynomial differs from the fifth-degree truncation by order six. -/
private lemma norm_sextic_log_residual_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 10) :
    let y := exp a * exp b - 1
    ‖y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 +
      (5 : ℚ)⁻¹ • y ^ 5 - bchCubicTerm a b - bchQuarticTerm a b -
      bchQuinticTerm a b‖ ≤ 62 * (‖a‖ + ‖b‖) ^ 6 := by
  dsimp only
  let y := exp a * exp b - 1
  let z := bchZ a b
  let P := y - z
  let T₂ := bchT2 a b
  let T₃ := bchT3 a b
  let T₄ := bchT4 a b
  let T₅ := bchT5 a b
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hz : ‖z‖ ≤ s := norm_add_le a b
  have hT₂ : ‖T₂‖ ≤ s ^ 2 := by
    simpa only [expMulTerm_two] using norm_expMulTerm_le_pow a b 2
  have hR2 : ‖P‖ ≤ s ^ 2 := by
    simpa only [sum_range_expMulTerm_two, P, y, z, bchZ, sub_add_eq_sub_sub] using
      norm_exp_mul_exp_sub_sum_le_pow a b 2 (by decide) hab
  have hR3 : ‖P - T₂‖ ≤ s ^ 3 := by
    simpa only [sum_range_expMulTerm_three, sub_add_eq_sub_sub] using
      norm_exp_mul_exp_sub_sum_le_pow a b 3 (by decide) hab
  have hR4 : ‖P - T₂ - T₃‖ ≤ s ^ 4 := by
    simpa only [sum_range_expMulTerm_four, sub_add_eq_sub_sub] using
      norm_exp_mul_exp_sub_sum_le_pow a b 4 (by decide) hab
  have hR5 : ‖P - T₂ - T₃ - T₄‖ ≤ s ^ 5 := by
    simpa only [sum_range_expMulTerm_five, sub_add_eq_sub_sub] using
      norm_exp_mul_exp_sub_sum_le_pow a b 5 (by decide) hab
  have hR6 : ‖P - T₂ - T₃ - T₄ - T₅‖ ≤ s ^ 6 := by
    simpa only [sum_range_expMulTerm_six, sub_add_eq_sub_sub] using
      norm_exp_mul_exp_sub_sum_le_pow a b 6 (by decide) hab
  have hy2 : ‖y‖ ≤ 2 * s := by
    have ht := norm_exp_mul_exp_sub_one_le a b
    have he := real_exp_sub_one_sub_id_le_sq hs (show s ≤ 1 by linarith only [hab])
    have hs2 : s ^ 2 ≤ s := by nlinarith only [hs, hab]
    linarith only [ht, he, hs2]
  let Q₁ := z + T₂ + T₃ + T₄ + T₅
  let Q₂ := z ^ 2 + (z * T₂ + T₂ * z) + (z * T₃ + T₂ ^ 2 + T₃ * z) +
    (z * T₄ + T₂ * T₃ + T₃ * T₂ + T₄ * z)
  let Q₃ := z ^ 3 + (z ^ 2 * T₂ + z * T₂ * z + T₂ * z ^ 2) + bchY35 a b
  let Q₄ := z ^ 4 + bchY45 a b
  let Q₅ := z ^ 5
  have hy : y = z + P := by dsimp only [P]; abel
  have hE₁ : ‖y - Q₁‖ ≤ s ^ 6 := by
    simpa only [Q₁, sub_add_eq_sub_sub] using hR6
  have hE₂ : ‖y ^ 2 - Q₂‖ ≤ 5 * s ^ 6 := by
    rw [hy]
    simpa only [Q₂, sub_add_eq_sub_sub] using
      norm_sq_sub_corrections_le z P T₂ T₃ T₄ hz hT₂ hR3 hR4 hR5
  have hE₃ : ‖y ^ 3 - Q₃‖ ≤ 10 * s ^ 6 := by
    rw [hy]
    simpa only [Q₃, bchY35, sub_add_eq_sub_sub] using
      norm_cube_sub_corrections_le z P T₂ T₃ hz hR2 hT₂ hR3 hR4
  have hE₄ : ‖y ^ 4 - Q₄‖ ≤ 15 * s ^ 6 := by
    simpa only [Q₄, bchY45, sub_add_eq_sub_sub] using
      norm_fourth_sub_linear_le y z T₂ hy2 hz hR2 hR3
  have hE₅ : ‖y ^ 5 - Q₅‖ ≤ 31 * s ^ 6 := by
    calc
      _ ≤ s ^ 2 * ∑ i ∈ range 5, (2 * s) ^ i * s ^ (4 - i) :=
        norm_pow_sub_pow_le_of_le y z hy2 hz hR2 4
      _ = 31 * s ^ 6 := by norm_num [sum_range_succ]; ring
  have htrunc : z + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b +
      bchQuarticTerm a b + bchQuinticTerm a b =
      Q₁ - (2 : ℚ)⁻¹ • Q₂ + (3 : ℚ)⁻¹ • Q₃ - (4 : ℚ)⁻¹ • Q₄ +
        (5 : ℚ)⁻¹ • Q₅ := bch_quintic_truncation_eq a b
  have heq : y - z - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 +
      (5 : ℚ)⁻¹ • y ^ 5 - bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b =
      (y - Q₁) - (2 : ℚ)⁻¹ • (y ^ 2 - Q₂) + (3 : ℚ)⁻¹ • (y ^ 3 - Q₃) -
        (4 : ℚ)⁻¹ • (y ^ 4 - Q₄) + (5 : ℚ)⁻¹ • (y ^ 5 - Q₅) := by
    calc
      _ = (y - (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 +
          (5 : ℚ)⁻¹ • y ^ 5) - (z + (2 : ℚ)⁻¹ • (a * b - b * a) +
            bchCubicTerm a b + bchQuarticTerm a b + bchQuinticTerm a b) := by abel
      _ = _ := by rw [htrunc]; simp only [smul_sub]; abel
  have hsmul (c : ℚ) (x : A) (M : ℝ) (hc : ‖c‖ ≤ 1) (hx : ‖x‖ ≤ M) :
      ‖c • x‖ ≤ M := by
    exact (norm_smul_le c x).trans (by
      simpa using mul_le_mul hc hx (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  have h₂ : ‖(2 : ℚ)⁻¹ • (y ^ 2 - Q₂)‖ ≤ 5 * s ^ 6 :=
    hsmul _ _ _ (by rw [norm_inv, ← Rat.norm_cast_real]; norm_num) hE₂
  have h₃ : ‖(3 : ℚ)⁻¹ • (y ^ 3 - Q₃)‖ ≤ 10 * s ^ 6 :=
    hsmul _ _ _ (by rw [norm_inv, ← Rat.norm_cast_real]; norm_num) hE₃
  have h₄ : ‖(4 : ℚ)⁻¹ • (y ^ 4 - Q₄)‖ ≤ 15 * s ^ 6 :=
    hsmul _ _ _ (by rw [norm_inv, ← Rat.norm_cast_real]; norm_num) hE₄
  have h₅ : ‖(5 : ℚ)⁻¹ • (y ^ 5 - Q₅)‖ ≤ 31 * s ^ 6 :=
    hsmul _ _ _ (by rw [norm_inv, ← Rat.norm_cast_real]; norm_num) hE₅
  change ‖y - z - (2 : ℚ)⁻¹ • (a * b - b * a) -
    (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 +
    (5 : ℚ)⁻¹ • y ^ 5 - bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b‖ ≤ _
  rw [heq]
  exact (norm_add_le_of_le (norm_sub_le_of_le (norm_add_le_of_le
    (norm_sub_le_of_le hE₁ h₂) h₃) h₄) h₅).trans_eq (by ring)

/-- The sixth-order BCH remainder has constant `100` for `‖a‖ + ‖b‖ < 1/10`. -/
theorem norm_bch_sextic_remainder_small_s_le (a b : A)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) (hs_small : ‖a‖ + ‖b‖ < 1 / 10) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b‖ ≤
      100 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let y := exp a * exp b - 1
  let s := ‖a‖ + ‖b‖
  let C := (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) +
    bchCubicTerm a b + bchQuarticTerm a b + bchQuinticTerm a b
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hpoly : ‖logPartialSum A 6 y - C‖ ≤ 62 * s ^ 6 := by
    have h := norm_sextic_log_residual_le a b hs_small
    simpa only [logPartialSum_six, C, y, s, sub_eq_add_neg, neg_add,
      add_assoc, add_comm, add_left_comm] using h
  have hexp6 : (Real.exp s - 1) ^ 6 ≤ 2 * s ^ 6 := by
    calc
      _ ≤ (1 + 1 / 10 : ℝ) ^ 6 * s ^ 6 :=
        real_exp_sub_one_pow_le_of_le hs hs_small.le (by norm_num) 6
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hs 6)
  simpa only [C, sub_add_eq_sub_sub] using
    norm_bch_sub_le_div_of_logPartialSum (B := 62) (E := 2) (K := 100)
      a b C 6 hab (by norm_num) hpoly hexp6 (by norm_num)

/-- The sixth-order BCH remainder has constant `100000` for `‖a‖ + ‖b‖ < log 2`. -/
theorem norm_bch_sextic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b - bchQuinticTerm a b‖ ≤
      100000 * (‖a‖ + ‖b‖) ^ 6 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  let s := ‖a‖ + ‖b‖
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have he : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
         _ = 2 := Real.exp_log (by norm_num)
  have hd : 0 < 2 - Real.exp s := by linarith only [he]
  have hd1 : 2 - Real.exp s ≤ 1 := by linarith only [Real.add_one_le_exp s, hs]
  by_cases hlarge : 1 / 10 ≤ s
  · exact norm_sub_le_succ_pow_div _ (bchQuinticTerm a b) 5 hs hd hd1
      (norm_bch_quintic_remainder_le a b hab) (norm_bchQuinticTerm_le a b)
      (show 3000 + 1 ≤ (100000 : ℝ) * s by linarith only [hlarge])
  · have hsmall : s < 1 / 10 := lt_of_not_ge hlarge
    exact (norm_bch_sextic_remainder_small_s_le a b hab hsmall).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (100 : ℝ) ≤ 100000)
          (pow_nonneg hs 6)) hd.le)

end FQFP.BCH
