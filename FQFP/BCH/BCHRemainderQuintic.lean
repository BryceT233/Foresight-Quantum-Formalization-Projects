/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHRemainderQuartic
public import FQFP.BCH.BCHTerms
public import FQFP.BCH.DynkinReeToolbox

/-!
# Fifth-order BCH remainder

The quartic truncation has error at most `3000 s⁵ / (2 - exp s)`.

## Main results

* `norm_bch_quintic_remainder_le`.
-/

@[expose] public noncomputable section

open NormedSpace Finset
open scoped Nat

namespace FQFP.BCH

/-- A quadratic perturbation gives a fifth-order error in the cubic expansion. -/
private lemma norm_cube_perturbation_le {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] (z P P₂ : 𝔸) (s : ℝ) (hs_nn : 0 ≤ s) (hs1 : s < 1)
    (hz_le : ‖z‖ ≤ s) (hP_le_s2 : ‖P‖ ≤ s ^ 2) (hS_le : ‖P - P₂‖ ≤ 5 * s ^ 3) :
    ‖(3 : ℚ)⁻¹ • ((z + P) ^ 3 - z ^ 3 -
      (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2))‖ ≤ 8 * s ^ 5 := by
  have hinner : (z + P) ^ 3 - z ^ 3 - (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2) =
      z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
        z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3 := by
          noncomm_ring
  rw [hinner]
  have hz2 : ‖z ^ 2‖ ≤ s ^ 2 :=
    (norm_pow_le' z (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
  have hP2 : ‖P ^ 2‖ ≤ s ^ 4 := by
    convert (norm_pow_le' P (by norm_num)).trans
      (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2) using 1
    ring
  have t1 : ‖z ^ 2 * (P - P₂)‖ ≤ 5 * s ^ 5 :=
    (norm_mul_le_of_le hz2 hS_le).trans_eq (by ring)
  have t2 : ‖z * (P - P₂) * z‖ ≤ 5 * s ^ 5 :=
    (norm_mul_le_of_le (norm_mul_le_of_le hz_le hS_le) hz_le).trans_eq (by ring)
  have t3 : ‖(P - P₂) * z ^ 2‖ ≤ 5 * s ^ 5 :=
    (norm_mul_le_of_le hS_le hz2).trans_eq (by ring)
  have t4 : ‖z * P ^ 2‖ ≤ s ^ 5 := (norm_mul_le_of_le hz_le hP2).trans_eq (by ring)
  have t5 : ‖P * z * P‖ ≤ s ^ 5 :=
    (norm_mul_le_of_le (norm_mul_le_of_le hP_le_s2 hz_le) hP_le_s2).trans_eq (by ring)
  have t6 : ‖P ^ 2 * z‖ ≤ s ^ 5 := (norm_mul_le_of_le hP2 hz_le).trans_eq (by ring)
  have t7 : ‖P ^ 3‖ ≤ s ^ 5 := by
    calc
      _ ≤ (s ^ 2) ^ 3 := (norm_pow_le' P (by norm_num)).trans
        (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 3)
      _ ≤ s ^ 5 := by nlinarith only [hs1, pow_nonneg hs_nn 5]
  have hsum : ‖z ^ 2 * (P - P₂) + z * (P - P₂) * z + (P - P₂) * z ^ 2 +
      z * P ^ 2 + P * z * P + P ^ 2 * z + P ^ 3‖ ≤ 19 * s ^ 5 :=
    (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le (norm_add_le_of_le t1 t2) t3) t4) t5) t6) t7).trans_eq (by ring)
  calc
    _ ≤ ‖(3 : ℚ)⁻¹‖ * (19 * s ^ 5) := (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ ≤ 8 * s ^ 5 := by
      rw [norm_inv, ← Rat.norm_cast_real]
      norm_num
      linarith only [pow_nonneg hs_nn 5]

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The degree-five error of the fourth logarithm polynomial on an exponential product. -/
private lemma norm_quintic_log_residual_le (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < 3 / 4) :
    let y := exp a * exp b - 1
    ‖y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 -
      bchCubicTerm a b - bchQuarticTerm a b‖ ≤
      32 * (‖a‖ + ‖b‖) ^ 5 := by
  dsimp only
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖; set β := ‖b‖
  have hs_nn : 0 ≤ s := by
    positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hy_le : ‖y‖ ≤ Real.exp s - 1 :=
    norm_exp_mul_exp_sub_one_le a b
  have hs34 : s < 3 / 4 := hab
  have hs1 : s < 1 := by
    linarith
  set G₁ := exp a - 1 - a - (2 : ℚ)⁻¹ • a ^ 2 - (6 : ℚ)⁻¹ • a ^ 3 -
      (24 : ℚ)⁻¹ • a ^ 4
  set G₂ := exp b - 1 - b - (2 : ℚ)⁻¹ • b ^ 2 - (6 : ℚ)⁻¹ • b ^ 3 -
      (24 : ℚ)⁻¹ • b ^ 4
  have hG₁_le : ‖G₁‖ ≤ α ^ 5 := by
    calc ‖G₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 - α ^ 4 / 24 :=
          norm_exp_sub_quartic_le a
      _ ≤ α ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg a)
          (lt_of_le_of_lt hα_le hs34)
  have hG₂_le : ‖G₂‖ ≤ β ^ 5 := by
    calc ‖G₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 - β ^ 4 / 24 :=
          norm_exp_sub_quartic_le b
      _ ≤ β ^ 5 := real_exp_fifth_order_le_quintic (norm_nonneg b)
          (lt_of_le_of_lt hβ_le hs34)
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set E₁ := D₁ - (2 : ℚ)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := D₂ - (2 : ℚ)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := E₁ - (6 : ℚ)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := E₂ - (6 : ℚ)⁻¹ • b ^ 3 with hF₂_def
  set P := y - (a + b) with hP_def
  set z := a + b with hz_def
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α :=
    norm_exp_sub_one_sub_id_le a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β :=
    norm_exp_sub_one_sub_id_le b
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hα_nn (by linarith only [hs1, hα_le])
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hβ_nn (by linarith only [hs1, hβ_le])
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hs_nn (by linarith only [hs1])
  have hs56 : s < 5 / 6 := by
    linarith
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_id_sub_sq_le a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_id_sub_sq_le b
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_cubic_le a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_cubic_le b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le hs34)
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le hs34)
  have hD₁s : ‖D₁‖ ≤ s ^ 2 :=
    hD₁_le.trans (hDa2.trans (pow_le_pow_left₀ hα_nn hα_le 2))
  have hD₂s : ‖D₂‖ ≤ s ^ 2 :=
    hD₂_le.trans (hDb2.trans (pow_le_pow_left₀ hβ_nn hβ_le 2))
  have hE₁s : ‖E₁‖ ≤ s ^ 3 :=
    hE₁_le.trans (hEa3.trans (pow_le_pow_left₀ hα_nn hα_le 3))
  have hE₂s : ‖E₂‖ ≤ s ^ 3 :=
    hE₂_le.trans (hEb3.trans (pow_le_pow_left₀ hβ_nn hβ_le 3))
  have hF₁s : ‖F₁‖ ≤ s ^ 4 :=
    hF₁_le.trans (hFa4.trans (pow_le_pow_left₀ hα_nn hα_le 4))
  have hF₂s : ‖F₂‖ ≤ s ^ 4 :=
    hF₂_le.trans (hFb4.trans (pow_le_pow_left₀ hβ_nn hβ_le 4))
  have hz_le : ‖z‖ ≤ s := by
    calc ‖z‖ = ‖a + b‖ := by rw [hz_def]
      _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ = s := by rw [hs_def]
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s :=
    norm_exp_mul_exp_sub_one_sub_add_le a b
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hy_le2 : ‖y‖ ≤ 2 * s := by
    calc ‖y‖ ≤ Real.exp s - 1 := hy_le
      _ ≤ s + s ^ 2 := by
        linarith [hEs2]
      _ ≤ 2 * s := by
        nlinarith only [hs_nn, hs1, sq_nonneg s]
  have hy4z4 : ‖y ^ 4 - z ^ 4‖ ≤ 15 * s ^ 5 := by
    have hy2 := (norm_pow_le y 2).trans (pow_le_pow_left₀ (norm_nonneg y) hy_le2 2)
    have hz2 := (norm_pow_le z 2).trans (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
    have hd : ‖y - z‖ ≤ s ^ 2 := hP_le_s2
    have hsq : ‖y ^ 2 - z ^ 2‖ ≤ (2 * s + s) * s ^ 2 :=
      (norm_sq_sub_sq_le y z).trans
        (mul_le_mul (add_le_add hy_le2 hz_le) hd (norm_nonneg _) (by positivity))
    calc
      _ = ‖(y ^ 2) ^ 2 - (z ^ 2) ^ 2‖ := by simp only [← pow_mul]
      _ ≤ ((2 * s) ^ 2 + s ^ 2) * ((2 * s + s) * s ^ 2) :=
        (norm_sq_sub_sq_le (y ^ 2) (z ^ 2)).trans
          (mul_le_mul (add_le_add hy2 hz2) hsq (norm_nonneg _) (by positivity))
      _ = 15 * s ^ 5 := by ring
  have hS_le : ‖P - (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2)‖ ≤
      5 * s ^ 3 :=
    (norm_exp_mul_exp_sub_quadratic_le a b).trans
      ((real_exp_third_order_le_cube hs_nn hs56).trans
        (by linarith only [pow_nonneg hs_nn 3]))
  have hG₁_s5 : ‖G₁‖ ≤ s ^ 5 :=
    le_trans hG₁_le (pow_le_pow_left₀ hα_nn hα_le 5)
  have hG₂_s5 : ‖G₂‖ ≤ s ^ 5 :=
    le_trans hG₂_le (pow_le_pow_left₀ hβ_nn hβ_le 5)
  have haF₂ : ‖a * F₂‖ ≤ s ^ 5 :=
    (norm_mul_le_of_le hα_le hF₂s).trans_eq (by ring)
  have hF₁b : ‖F₁ * b‖ ≤ s ^ 5 :=
    (norm_mul_le_of_le hF₁s hβ_le).trans_eq (by ring)
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  set W_H1 := (2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
      z * P - P * z - P ^ 2 with hW_H1_def
  have hH1 : y - z - (2 : ℚ)⁻¹ • (a * b - b * a) - (2 : ℚ)⁻¹ • y ^ 2 =
      (2 : ℚ)⁻¹ • W_H1 := by
    exact bchCommutator_residual_eq (exp a) (exp b) a b
  set I₁ := (2 : ℚ)⁻¹ • W_H1 + (3 : ℚ)⁻¹ • z ^ 3 -
      bchCubicTerm a b with hI₁_def
  set I₂ := (3 : ℚ)⁻¹ • (y ^ 3 - z ^ 3) with hI₂_def
  have hpB_split : y - z - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 -
      bchCubicTerm a b - bchQuarticTerm a b =
      I₁ + I₂ - (4 : ℚ)⁻¹ • y ^ 4 - bchQuarticTerm a b := by
    conv_lhs => rw [show y - z - (2 : ℚ)⁻¹ • (a * b - b * a) -
        (2 : ℚ)⁻¹ • y ^ 2 = (2 : ℚ)⁻¹ • W_H1 from hH1]
    simp only [hI₁_def, hI₂_def, smul_sub]
    abel
  have hI₁_eq2 : I₁ = (2 : ℚ)⁻¹ • W_H1 +
      (3 : ℚ)⁻¹ • z ^ 3 - bchCubicTerm a b := rfl
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : ℚ)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
      (2 : ℚ)⁻¹ • P ^ 2 := by
    rw [hI₁_eq2]; exact bchCubicTerm_residual_eq (exp a) (exp b) a b
  set T₃ := (6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 +
      (2 : ℚ)⁻¹ • (a * b ^ 2) + (2 : ℚ)⁻¹ • (a ^ 2 * b)
  set P₂ := a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2
  let corr₁ := (24 : ℚ)⁻¹ • a ^ 4 + (24 : ℚ)⁻¹ • b ^ 4 +
      (6 : ℚ)⁻¹ • (a * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b) +
      (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) -
      (2 : ℚ)⁻¹ • (z * T₃ + T₃ * z) -
      (2 : ℚ)⁻¹ • P₂ ^ 2
  let corr₂ := (3 : ℚ)⁻¹ • (z ^ 2 * P₂ + z * P₂ * z + P₂ * z ^ 2)
  have hQPI : corr₁ + corr₂ - (4 : ℚ)⁻¹ • z ^ 4 -
      bchQuarticTerm a b = 0 := quintic_pure_identity a b
  rw [hpB_split]
  have hrewrite : I₁ + I₂ - (4 : ℚ)⁻¹ • y ^ 4 - bchQuarticTerm a b =
      (I₁ - corr₁) + (I₂ - corr₂) - (4 : ℚ)⁻¹ • (y ^ 4 - z ^ 4) := by
    rw [sub_eq_zero.symm]
    convert hQPI using 1
    simp only [smul_sub]
    abel
  rw [hrewrite]
  have hGroup1 : ‖I₁ - corr₁‖ ≤ 20 * s ^ 5 := by
    rw [hI₁_quartic]
    have h_regroup :
        F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
          (2 : ℚ)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) -
          (2 : ℚ)⁻¹ • P ^ 2 - corr₁ =
        (F₁ - (24 : ℚ)⁻¹ • a ^ 4) + (F₂ - (24 : ℚ)⁻¹ • b ^ 4) +
        (a * E₂ - (6 : ℚ)⁻¹ • (a * b ^ 3)) +
        (E₁ * b - (6 : ℚ)⁻¹ • (a ^ 3 * b)) +
        (D₁ * D₂ - (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2)) +
        ((2 : ℚ)⁻¹ • (z * T₃ + T₃ * z) -
          (2 : ℚ)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z)) +
        ((2 : ℚ)⁻¹ • P₂ ^ 2 - (2 : ℚ)⁻¹ • P ^ 2) := by
      dsimp only [corr₁]
      abel
    rw [h_regroup]
    have hA : F₁ - (24 : ℚ)⁻¹ • a ^ 4 = G₁ := rfl
    have hB : F₂ - (24 : ℚ)⁻¹ • b ^ 4 = G₂ := rfl
    have hC : a * E₂ - (6 : ℚ)⁻¹ • (a * b ^ 3) = a * F₂ := by
      have : E₂ = F₂ + (6 : ℚ)⁻¹ • b ^ 3 := by
        rw [hF₂_def]; abel
      rw [this, mul_add, mul_smul_comm]; abel
    have hDt : E₁ * b - (6 : ℚ)⁻¹ • (a ^ 3 * b) = F₁ * b := by
      have : E₁ = F₁ + (6 : ℚ)⁻¹ • a ^ 3 := by
        rw [hF₁_def]; abel
      rw [this, add_mul, smul_mul_assoc]; abel
    have hEt : D₁ * D₂ - (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) =
        E₁ * E₂ + (2 : ℚ)⁻¹ • (a ^ 2 * E₂) + (2 : ℚ)⁻¹ • (E₁ * b ^ 2) := by
      have hd1 : D₁ = E₁ + (2 : ℚ)⁻¹ • a ^ 2 := by
        rw [hE₁_def]; abel
      have hd2 : D₂ = E₂ + (2 : ℚ)⁻¹ • b ^ 2 := by
        rw [hE₂_def]; abel
      rw [hd1, hd2]; simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
        smul_smul, show (2 : ℚ)⁻¹ * (2 : ℚ)⁻¹ = (4 : ℚ)⁻¹ from by norm_num, smul_add]; abel
    have hFt : (2 : ℚ)⁻¹ • (z * T₃ + T₃ * z) -
        (2 : ℚ)⁻¹ • (z * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * z) =
        (2 : ℚ)⁻¹ • (z * (T₃ - E₁ - E₂ - Q) + (T₃ - E₁ - E₂ - Q) * z) := by
      rw [← smul_sub]; congr 1; noncomm_ring
    have hGt : (2 : ℚ)⁻¹ • P₂ ^ 2 - (2 : ℚ)⁻¹ • P ^ 2 =
        (2 : ℚ)⁻¹ • (P₂ ^ 2 - P ^ 2) := (smul_sub _ _ _).symm
    rw [hA, hB, hC, hDt, hEt, hFt, hGt]
    have hT₃_exp : T₃ = (6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 + (2 : ℚ)⁻¹ • (a * b ^ 2) +
        (2 : ℚ)⁻¹ • (a ^ 2 * b) := by
          dsimp only
    have hSrest_eq : T₃ - E₁ - E₂ - Q = -(F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂) := by
      simp only [hT₃_exp, hQ_def, hF₁_def, hF₂_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def,
        mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
      abel
    have haEs : ‖a * E₂‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hα_le hE₂s).trans_eq (by ring)
    have hEbs : ‖E₁ * b‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hE₁s hβ_le).trans_eq (by ring)
    have hDDs : ‖D₁ * D₂‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hD₁s hD₂s).trans_eq (by ring)
    have hSrest_le : ‖T₃ - E₁ - E₂ - Q‖ ≤ 5 * s ^ 4 := by
      rw [hSrest_eq, norm_neg]
      exact (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
        (norm_add_le_of_le hF₁s hF₂s) haEs) hEbs) hDDs).trans_eq (by ring)
    have h2_le : ‖(2 : ℚ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, ← Rat.norm_cast_real]; norm_num
    have h2eq : ‖(2 : ℚ)⁻¹‖ = (2 : ℝ)⁻¹ := by
      rw [norm_inv, ← Rat.norm_cast_real]; norm_num
    have hP₂_le : ‖P₂‖ ≤ s ^ 2 := by
      have h1 : ‖a * b‖ ≤ α * β := norm_mul_le _ _
      have h2 : ‖(2 : ℚ)⁻¹ • a ^ 2‖ ≤ α ^ 2 :=
        (norm_smul_le _ _).trans (by
          simpa using mul_le_mul h2_le (norm_pow_le a 2) (norm_nonneg _) (by norm_num))
      have h3 : ‖(2 : ℚ)⁻¹ • b ^ 2‖ ≤ β ^ 2 :=
        (norm_smul_le _ _).trans (by
          simpa using mul_le_mul h2_le (norm_pow_le b 2) (norm_nonneg _) (by norm_num))
      have ht : ‖P₂‖ ≤ α * β + α ^ 2 + β ^ 2 :=
        norm_add_le_of_le (norm_add_le_of_le h1 h2) h3
      have hs2 : s ^ 2 = α ^ 2 + 2 * α * β + β ^ 2 := by rw [hs_def]; ring
      linarith only [ht, hs2, mul_nonneg hα_nn hβ_nn]
    have b5 : ‖E₁ * E₂ + (2 : ℚ)⁻¹ • (a ^ 2 * E₂) +
        (2 : ℚ)⁻¹ • (E₁ * b ^ 2)‖ ≤ 3 * s ^ 5 := by
      have t1 : ‖E₁ * E₂‖ ≤ s ^ 5 :=
        (norm_mul_le_of_le hE₁s hE₂s).trans
          (by nlinarith only [hs1, pow_nonneg hs_nn 5])
      have t2 : ‖(2 : ℚ)⁻¹ • (a ^ 2 * E₂)‖ ≤ s ^ 5 := by
        have h := (norm_mul_le_of_le
          ((norm_pow_le a 2).trans (pow_le_pow_left₀ hα_nn hα_le 2)) hE₂s).trans_eq
            (show s ^ 2 * s ^ 3 = s ^ 5 by ring)
        exact (norm_smul_le _ _).trans
          (by simpa using mul_le_mul h2_le h (norm_nonneg _) (by positivity))
      have t3 : ‖(2 : ℚ)⁻¹ • (E₁ * b ^ 2)‖ ≤ s ^ 5 := by
        have h := (norm_mul_le_of_le hE₁s
          ((norm_pow_le b 2).trans (pow_le_pow_left₀ hβ_nn hβ_le 2))).trans_eq
            (show s ^ 3 * s ^ 2 = s ^ 5 by ring)
        exact (norm_smul_le _ _).trans
          (by simpa using mul_le_mul h2_le h (norm_nonneg _) (by positivity))
      exact (norm_add_le_of_le (norm_add_le_of_le t1 t2) t3).trans_eq (by ring)
    have b6 : ‖(2 : ℚ)⁻¹ • (z * (T₃ - E₁ - E₂ - Q) +
        (T₃ - E₁ - E₂ - Q) * z)‖ ≤ 5 * s ^ 5 := by
      have hsum := norm_add_le_of_le (norm_mul_le_of_le hz_le hSrest_le)
        (norm_mul_le_of_le hSrest_le hz_le)
      calc
        _ ≤ ‖(2 : ℚ)⁻¹‖ * (s * (5 * s ^ 4) + (5 * s ^ 4) * s) :=
          (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
        _ = 5 * s ^ 5 := by rw [h2eq]; ring
    have b7 : ‖(2 : ℚ)⁻¹ • (P₂ ^ 2 - P ^ 2)‖ ≤ 6 * s ^ 5 := by
      have hd : ‖P₂ - P‖ ≤ 5 * s ^ 3 := by
        rw [norm_sub_rev]; exact hS_le
      calc _ ≤ ‖(2 : ℚ)⁻¹‖ * ‖P₂ ^ 2 - P ^ 2‖ := norm_smul_le _ _
           _ ≤ (2 : ℝ)⁻¹ * ((s ^ 2 + s ^ 2) * (5 * s ^ 3)) := by
             rw [h2eq]
             gcongr
             exact (norm_sq_sub_sq_le P₂ P).trans
               (mul_le_mul (add_le_add hP₂_le hP_le_s2) hd (norm_nonneg _) (by positivity))
           _ ≤ 6 * s ^ 5 := by
             nlinarith only [pow_nonneg hs_nn 5]
    exact (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
      (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le hG₁_s5 hG₂_s5)
        haF₂) hF₁b) b5) b6) b7).trans
          (by linarith only [pow_nonneg hs_nn 5])
  have hGroup2 : ‖I₂ - corr₂‖ ≤ 8 * s ^ 5 := by
    have hy_zP : y = z + P := by
      simp only [hP_def, hz_def]; abel
    rw [hI₂_def, ← smul_sub, hy_zP]
    exact norm_cube_perturbation_le z P P₂ s hs_nn hs1 hz_le hP_le_s2 hS_le
  have hGroup3 : ‖(4 : ℚ)⁻¹ • (y ^ 4 - z ^ 4)‖ ≤ 4 * s ^ 5 :=
    calc _ ≤ ‖(4 : ℚ)⁻¹‖ * ‖y ^ 4 - z ^ 4‖ := norm_smul_le _ _
      _ ≤ (4 : ℝ)⁻¹ * (15 * s ^ 5) := by
          have : ‖(4 : ℚ)⁻¹‖ = (4 : ℝ)⁻¹ := by
            rw [norm_inv, ← Rat.norm_cast_real]; norm_num
          rw [this]; exact mul_le_mul_of_nonneg_left hy4z4 (by norm_num)
      _ ≤ 4 * s ^ 5 := by
        nlinarith only [hs_nn, hs1, pow_nonneg hs_nn 5]
  calc ‖(I₁ - corr₁) + (I₂ - corr₂) - (4 : ℚ)⁻¹ • (y ^ 4 - z ^ 4)‖
      ≤ ‖(I₁ - corr₁) + (I₂ - corr₂)‖ + ‖(4 : ℚ)⁻¹ • (y ^ 4 - z ^ 4)‖ :=
        norm_sub_le _ _
    _ ≤ (‖I₁ - corr₁‖ + ‖I₂ - corr₂‖) + ‖(4 : ℚ)⁻¹ • (y ^ 4 - z ^ 4)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (20 * s ^ 5 + 8 * s ^ 5) + 4 * s ^ 5 := by
      linarith
    _ = 32 * s ^ 5 := by
      ring

/-- The BCH remainder after the quartic term, with constant `3000` on `s < log 2`,
where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bch_quintic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b‖ ≤
      3000 * (‖a‖ + ‖b‖) ^ 5 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set y := exp a * exp b - 1 with hy_def
  set s := ‖a‖ + ‖b‖ with hs_def
  set α := ‖a‖; set β := ‖b‖
  have hs_nn : 0 ≤ s := by
    positivity
  have hα_nn : (0 : ℝ) ≤ α := norm_nonneg a
  have hβ_nn : (0 : ℝ) ≤ β := norm_nonneg b
  have hα_le : α ≤ s := le_add_of_nonneg_right hβ_nn
  have hβ_le : β ≤ s := le_add_of_nonneg_left hα_nn
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hab
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by
    linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 :=
    norm_exp_mul_exp_sub_one_le a b
  have hs34 : s < 3 / 4 := lt_of_lt_of_le hab (by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ≤ 1 + 3 / 4 + (3 / 4) ^ 2 / 2 := by norm_num
      _ ≤ Real.exp (3 / 4) := Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hs1 : s < 1 := by
    linarith
  have hdecomp : bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b - bchQuarticTerm a b =
      (log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 - (3 : ℚ)⁻¹ • y ^ 3 +
        (4 : ℚ)⁻¹ • y ^ 4) +
      (y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
        (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 -
        bchCubicTerm a b - bchQuarticTerm a b) := by
    unfold bch
    rw [show exp a * exp b = 1 + y by rw [hy_def]; abel]
    abel
  rw [hdecomp]
  have hpieceA : ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 -
      (3 : ℚ)⁻¹ • y ^ 3 + (4 : ℚ)⁻¹ • y ^ 4‖ ≤
      (Real.exp s - 1) ^ 5 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 5 / (1 - ‖y‖) := norm_log_one_add_sub_quartic_le y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  have hpieceB : ‖y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 -
      bchCubicTerm a b - bchQuarticTerm a b‖ ≤
      32 * s ^ 5 :=
    norm_quintic_log_residual_le a b hs34
  have hE1_nn : 0 ≤ Real.exp s - 1 := by
    linarith [Real.add_one_le_exp s]
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hs_nn (by linarith only [hs1])
  have hexp5 : (Real.exp s - 1) ^ 5 ≤ 200 * s ^ 5 :=
    calc (Real.exp s - 1) ^ 5 ≤ (s + s ^ 2) ^ 5 := pow_le_pow_left₀ hE1_nn (by linarith) 5
      _ = s ^ 5 * (1 + s) ^ 5 := by
        ring
      _ ≤ s ^ 5 * 200 := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs_nn 5)
          have : (1 + s) ^ 5 ≤ (1 + 1) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
          linarith
      _ = 200 * s ^ 5 := by
        ring
  calc _ ≤ ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 -
          (3 : ℚ)⁻¹ • y ^ 3 + (4 : ℚ)⁻¹ • y ^ 4‖ +
        ‖y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
          (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - (4 : ℚ)⁻¹ • y ^ 4 -
          bchCubicTerm a b - bchQuarticTerm a b‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 5 / (2 - Real.exp s) +
        32 * s ^ 5 := by
          linarith [hpieceA, hpieceB]
    _ ≤ 3000 * s ^ 5 / (2 - Real.exp s) := by
      rw [div_add' _ _ _ (ne_of_gt hdenom), div_le_div_iff_of_pos_right hdenom]
      have hd : 2 - Real.exp s ≤ 1 := by linarith only [Real.add_one_le_exp s, hs_nn]
      nlinarith only [hexp5, mul_le_mul_of_nonneg_right hd (pow_nonneg hs_nn 5),
        pow_nonneg hs_nn 5]

end FQFP.BCH
