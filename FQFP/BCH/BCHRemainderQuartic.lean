/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Analysis.ExponentialProduct
public import FQFP.BCH.BCHCommutator

/-!
# Fourth-order BCH remainder

The cubic truncation has error at most `200 s⁴ / (2 - exp s)`.

## Main results

* `norm_bch_quartic_remainder_le`.
-/

@[expose] public noncomputable section

open NormedSpace Finset
open scoped Nat

namespace FQFP.BCH

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The BCH remainder after the cubic term, with constant `200` on `s < log 2`,
where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bch_quartic_remainder_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b‖ ≤
      200 * (‖a‖ + ‖b‖) ^ 4 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
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
  have hs56 : s < 5 / 6 := by
    calc s < Real.log 2 := hab
      _ ≤ 5 / 6 := by
          rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
          calc (2 : ℝ) ≤ 1 + 5 / 6 + (5 / 6) ^ 2 / 2 := by norm_num
            _ ≤ Real.exp (5 / 6) := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hs34 : s < 3 / 4 := lt_of_lt_of_le hab (by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
    calc (2 : ℝ) ≤ 1 + 3 / 4 + (3 / 4) ^ 2 / 2 := by norm_num
      _ ≤ Real.exp (3 / 4) := Real.quadratic_le_exp_of_nonneg (by norm_num))
  have hs1 : s < 1 := by
    linarith
  have hdecomp : bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      bchCubicTerm a b =
      (log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 - (3 : ℚ)⁻¹ • y ^ 3) +
      (y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
        (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 -
        bchCubicTerm a b) := by
    unfold bch
    rw [show exp a * exp b = 1 + y by rw [hy_def]; abel]
    abel
  rw [hdecomp]
  have hpieceA : ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 -
      (3 : ℚ)⁻¹ • y ^ 3‖ ≤
      (Real.exp s - 1) ^ 4 / (2 - Real.exp s) :=
    calc _ ≤ ‖y‖ ^ 4 / (1 - ‖y‖) := by simpa only [div_eq_mul_inv] using
      norm_log_one_add_sub_add_sq_sub_cube_le y hy_lt
      _ ≤ _ := div_le_div₀ (pow_nonneg (by linarith [Real.add_one_le_exp s]) _)
          (pow_le_pow_left₀ (norm_nonneg _) hy_le _) hdenom (by linarith)
  set D₁ := exp a - 1 - a with hD₁_def
  set D₂ := exp b - 1 - b with hD₂_def
  set P := y - (a + b) with hP_def
  set E₁ := exp a - 1 - a - (2 : ℚ)⁻¹ • a ^ 2 with hE₁_def
  set E₂ := exp b - 1 - b - (2 : ℚ)⁻¹ • b ^ 2 with hE₂_def
  set F₁ := exp a - 1 - a - (2 : ℚ)⁻¹ • a ^ 2 - (6 : ℚ)⁻¹ • a ^ 3 with hF₁_def
  set F₂ := exp b - 1 - b - (2 : ℚ)⁻¹ • b ^ 2 - (6 : ℚ)⁻¹ • b ^ 3 with hF₂_def
  set Q := a * D₂ + D₁ * b + D₁ * D₂ with hQ_def
  have hP_eq : P = a * b + D₁ + D₂ + Q := by
    rw [hQ_def, hP_def, hy_def, hD₁_def, hD₂_def]; noncomm_ring
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := norm_exp_sub_one_sub_id_le a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := norm_exp_sub_one_sub_id_le b
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 :=
    norm_exp_sub_one_sub_id_sub_sq_le a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 :=
    norm_exp_sub_one_sub_id_sub_sq_le b
  have hF₁_le : ‖F₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 :=
    norm_exp_sub_cubic_le a
  have hF₂_le : ‖F₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 :=
    norm_exp_sub_cubic_le b
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s :=
    norm_exp_mul_exp_sub_one_sub_add_le a b
  have hFa4 : Real.exp α - 1 - α - α ^ 2 / 2 - α ^ 3 / 6 ≤ α ^ 4 :=
    real_exp_fourth_order_le_quartic hα_nn (lt_of_le_of_lt hα_le (by linarith : s < 3 / 4))
  have hFb4 : Real.exp β - 1 - β - β ^ 2 / 2 - β ^ 3 / 6 ≤ β ^ 4 :=
    real_exp_fourth_order_le_quartic hβ_nn (lt_of_le_of_lt hβ_le (by linarith : s < 3 / 4))
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 :=
    real_exp_third_order_le_cube hα_nn (lt_of_le_of_lt hα_le hs56)
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 :=
    real_exp_third_order_le_cube hβ_nn (lt_of_le_of_lt hβ_le hs56)
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hα_nn (by linarith only [hs1, hα_le])
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hβ_nn (by linarith only [hs1, hβ_le])
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 :=
    real_exp_sub_one_sub_id_le_sq hs_nn (by linarith only [hs1])
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  have hEa_nn : 0 ≤ Real.exp α - 1 - α - α ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hα_nn]
  have hEb_nn : 0 ≤ Real.exp β - 1 - β - β ^ 2 / 2 := by
    linarith [Real.quadratic_le_exp_of_nonneg hβ_nn]
  have hpieceB_eq_H1 : y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
      (2 : ℚ)⁻¹ • y ^ 2 = (2 : ℚ)⁻¹ •
      ((2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
        (a + b) * P - P * (a + b) - P ^ 2) := by
    exact bchCommutator_residual_eq (exp a) (exp b) a b
  set pieceB := y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
    (2 : ℚ)⁻¹ • y ^ 2 + (3 : ℚ)⁻¹ • y ^ 3 - bchCubicTerm a b with hpieceB_def
  set z := a + b with hz_def
  set I₂ := (3 : ℚ)⁻¹ • (y ^ 3 - z ^ 3) with hI₂_def
  set I₁ := pieceB - I₂ with hI₁_def
  have hpieceB_split : pieceB = I₁ + I₂ := by
    rw [hI₁_def]; abel
  have hy_eq_zP : y = z + P := by
    simp only [hP_def, hz_def]; abel
  have hz_le : ‖z‖ ≤ s := by
    calc ‖z‖ = ‖a + b‖ := by rw [hz_def]
      _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ = s := by rw [hs_def]
  have hP_le_s2 : ‖P‖ ≤ s ^ 2 := le_trans hP_le hEs2
  have hI₂_bound : ‖I₂‖ ≤ 8 * s ^ 4 := by
    have hy3z3 : y ^ 3 - z ^ 3 = y ^ 2 * P + y * P * z + P * z ^ 2 := by
      rw [hy_eq_zP]; noncomm_ring
    have h3_norm : ‖(3 : ℚ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, ← Rat.norm_cast_real]
      norm_num
    have hy_le2 : ‖y‖ ≤ 2 * s := by
      have hs2 : s ^ 2 ≤ s := by nlinarith only [hs_nn, hs1]
      linarith only [hy_le, hEs2, hs2]
    have hy2 := (norm_pow_le y 2).trans (pow_le_pow_left₀ (norm_nonneg y) hy_le2 2)
    have hz2 := (norm_pow_le z 2).trans (pow_le_pow_left₀ (norm_nonneg z) hz_le 2)
    have hsum : ‖y ^ 2 * P + y * P * z + P * z ^ 2‖ ≤ 7 * s ^ 4 :=
      (norm_add_le_of_le (norm_add_le_of_le (norm_mul_le_of_le hy2 hP_le_s2)
        (norm_mul_le_of_le (norm_mul_le_of_le hy_le2 hP_le_s2) hz_le))
          (norm_mul_le_of_le hP_le_s2 hz2)).trans_eq (by ring)
    rw [hI₂_def, hy3z3]
    have h := mul_le_mul h3_norm hsum (norm_nonneg _) (by positivity)
    exact (norm_smul_le _ _).trans (h.trans (by linarith only [pow_nonneg hs_nn 4]))
  set W_H1 := (2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
          (a + b) * P - P * (a + b) - P ^ 2 with hW_H1_def
  have hI₁_eq2 : I₁ = (2 : ℚ)⁻¹ • W_H1 +
      (3 : ℚ)⁻¹ • z ^ 3 - bchCubicTerm a b := by
    have h1 : I₁ = (y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) -
        (2 : ℚ)⁻¹ • y ^ 2) + (3 : ℚ)⁻¹ • z ^ 3 - bchCubicTerm a b := by
      simp only [hI₁_def, hpieceB_def, hI₂_def, hz_def]
      rw [show (3 : ℚ)⁻¹ • y ^ 3 = (3 : ℚ)⁻¹ • (y ^ 3 - (a + b) ^ 3) +
          (3 : ℚ)⁻¹ • (a + b) ^ 3 from by rw [smul_sub]; abel]
      abel
    rw [h1, hpieceB_eq_H1]
  have hI₁_quartic : I₁ =
      F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂ -
      (2 : ℚ)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)) -
      (2 : ℚ)⁻¹ • P ^ 2 := by
    rw [hI₁_eq2]
    exact bchCubicTerm_residual_eq (exp a) (exp b) a b
  have hI₁_le : ‖I₁‖ ≤ 90 * s ^ 4 := by
    have h2_le : ‖(2 : ℚ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, ← Rat.norm_cast_real]; norm_num
    have hF₁_s4 : ‖F₁‖ ≤ s ^ 4 :=
      hF₁_le.trans (hFa4.trans (pow_le_pow_left₀ hα_nn hα_le 4))
    have hF₂_s4 : ‖F₂‖ ≤ s ^ 4 :=
      hF₂_le.trans (hFb4.trans (pow_le_pow_left₀ hβ_nn hβ_le 4))
    have hE₁_s3 : ‖E₁‖ ≤ s ^ 3 :=
      hE₁_le.trans (hEa3.trans (pow_le_pow_left₀ hα_nn hα_le 3))
    have hE₂_s3 : ‖E₂‖ ≤ s ^ 3 :=
      hE₂_le.trans (hEb3.trans (pow_le_pow_left₀ hβ_nn hβ_le 3))
    have hD₁_s2 : ‖D₁‖ ≤ s ^ 2 :=
      hD₁_le.trans (hDa2.trans (pow_le_pow_left₀ hα_nn hα_le 2))
    have hD₂_s2 : ‖D₂‖ ≤ s ^ 2 :=
      hD₂_le.trans (hDb2.trans (pow_le_pow_left₀ hβ_nn hβ_le 2))
    have haE₂ : ‖a * E₂‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hα_le hE₂_s3).trans_eq (by ring)
    have hE₁b : ‖E₁ * b‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hE₁_s3 hβ_le).trans_eq (by ring)
    have hDD : ‖D₁ * D₂‖ ≤ s ^ 4 :=
      (norm_mul_le_of_le hD₁_s2 hD₂_s2).trans_eq (by ring)
    have hEQ : ‖E₁ + E₂ + Q‖ ≤ 5 * s ^ 3 := by
      have heq : E₁ + E₂ + Q = exp a * exp b - 1 - (a + b) -
          (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) := by
        simp only [hQ_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def]
        noncomm_ring
      rw [heq]
      exact (norm_exp_mul_exp_sub_quadratic_le a b).trans
        ((real_exp_third_order_le_cube hs_nn hs56).trans
          (by linarith only [pow_nonneg hs_nn 3]))
    have hcross_inner : ‖(a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)‖ ≤
        10 * s ^ 4 :=
      (norm_add_le_of_le (norm_mul_le_of_le hz_le hEQ)
        (norm_mul_le_of_le hEQ hz_le)).trans_eq (by ring)
    have hcross : ‖(2 : ℚ)⁻¹ • ((a + b) * (E₁ + E₂ + Q) +
        (E₁ + E₂ + Q) * (a + b))‖ ≤ 10 * s ^ 4 := by
      exact (norm_smul_le _ _).trans
        (by simpa using mul_le_mul h2_le hcross_inner (norm_nonneg _) (by positivity))
    have hP2 : ‖(2 : ℚ)⁻¹ • P ^ 2‖ ≤ s ^ 4 := by
      have hp : ‖P ^ 2‖ ≤ s ^ 4 := by
        convert (norm_pow_le P 2).trans
          (pow_le_pow_left₀ (norm_nonneg P) hP_le_s2 2) using 1
        ring
      exact (norm_smul_le _ _).trans
        (by simpa using mul_le_mul h2_le hp (norm_nonneg _) (by positivity))
    have hsum : ‖F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂‖ ≤ 5 * s ^ 4 :=
      (norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le
        (norm_add_le_of_le hF₁_s4 hF₂_s4) haE₂) hE₁b) hDD).trans_eq (by ring)
    rw [hI₁_quartic]
    have hsub := (norm_sub_le (F₁ + F₂ + a * E₂ + E₁ * b + D₁ * D₂)
      ((2 : ℚ)⁻¹ • ((a + b) * (E₁ + E₂ + Q) + (E₁ + E₂ + Q) * (a + b)))).trans
        (add_le_add hsum hcross)
    exact (norm_sub_le _ _).trans ((add_le_add hsub hP2).trans
      (by linarith only [pow_nonneg hs_nn 4]))
  have hpieceB_le : ‖pieceB‖ ≤ 98 * s ^ 4 := by
    rw [hpieceB_split]
    calc ‖I₁ + I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_add_le _ _
      _ ≤ 90 * s ^ 4 + 8 * s ^ 4 := by
        linarith [hI₁_le, hI₂_bound]
      _ = 98 * s ^ 4 := by
        ring
  calc _ ≤ ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2 - (3 : ℚ)⁻¹ • y ^ 3‖ +
        ‖pieceB‖ := norm_add_le _ _
    _ ≤ (Real.exp s - 1) ^ 4 / (2 - Real.exp s) + 98 * s ^ 4 := by
      linarith [hpieceA, hpieceB_le]
    _ ≤ 200 * s ^ 4 / (2 - Real.exp s) := by
        rw [div_add' _ _ _ (ne_of_gt hdenom)]
        apply div_le_div_of_nonneg_right _ hdenom.le
        have hE1_nn : 0 ≤ Real.exp s - 1 := by
          linarith [Real.add_one_le_exp s]
        have hE1_le : Real.exp s - 1 ≤ s + s ^ 2 := by
          linarith [hEs2]
        have h1s4 : (1 + s) ^ 4 ≤ 10 := by
          calc (1 + s) ^ 4 ≤ (1 + 3 / 4 : ℝ) ^ 4 := by gcongr
               _ ≤ 10 := by norm_num
        have hexp4 : (Real.exp s - 1) ^ 4 ≤ 10 * s ^ 4 :=
          calc (Real.exp s - 1) ^ 4 ≤ (s + s ^ 2) ^ 4 := pow_le_pow_left₀ hE1_nn hE1_le 4
            _ = s ^ 4 * (1 + s) ^ 4 := by
              ring
            _ ≤ s ^ 4 * 10 := mul_le_mul_of_nonneg_left h1s4 (pow_nonneg hs_nn 4)
            _ = 10 * s ^ 4 := by
              ring
        nlinarith only [hexp4, pow_nonneg hs_nn 4, hdenom.le,
          show 2 - Real.exp s ≤ 1 from by linarith [Real.add_one_le_exp s]]

end FQFP.BCH
