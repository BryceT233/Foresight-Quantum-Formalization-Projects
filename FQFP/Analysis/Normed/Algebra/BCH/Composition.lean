/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.Commutator
import FQFP.Analysis.Normed.Algebra.Commutator

/-!
# Input and denominator control for nested BCH compositions

If `2 ‖x‖ + ‖y‖ ≤ s < 1/4`, the inner pair `x, y` is inside the BCH convergence range,
and the outer pair `bch x y, x` has total norm at most `2s`. The logarithm denominators
are bounded below by `11/16` at the inner scale and by `1/3` at the outer scale.
Taking `x = a/2`, `y = b` gives the input control shared by symmetric BCH estimates.

## Main results

* `norm_half_smul_le`, `norm_half_commutator_le`: half-scaled norm estimates.
* `eleven_sixteenths_le_two_sub_exp`, `one_third_le_two_sub_exp`: denominator bounds.
* `mul_pow_div_le_mul_pow`: rescale a power bound using a positive denominator lower bound.
* `half_lt_log_two`: the outer scale `1/2` lies inside the sufficient logarithm radius.
* `norm_bch_add_norm_le_two_mul`: norm control for a nested BCH input.
* `norm_bch_add_norm_lt_log_two`: convergence of the outer BCH pair.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-! ### Scalar denominator estimates -/

/-- A radius bound `r ≤ c * s` and a denominator bound `0 < d ≤ D` give
a remainder coefficient `M` whenever `K * c ^ n ≤ M * d`. -/
lemma mul_pow_div_le_mul_pow {K M r s c d D : ℝ} (n : ℕ)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hs : 0 ≤ s) (hradius : r ≤ c * s)
    (hd : 0 < d) (hden : d ≤ D) (hbudget : K * c ^ n ≤ M * d) :
    K * r ^ n / D ≤ M * s ^ n := by
  calc
    _ ≤ K * (c * s) ^ n / d :=
      div_le_div₀ (mul_nonneg hK (pow_nonneg (hr.trans hradius) n))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hradius n) hK) hd hden
    _ = (K * c ^ n / d) * s ^ n := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mpr hbudget) (pow_nonneg hs n)

/-- The logarithm denominator is at least `11/16` below a nonnegative scale `s < 1/4`. -/
lemma eleven_sixteenths_le_two_sub_exp {s t : ℝ} (hs0 : 0 ≤ s) (hs : s < 1 / 4)
    (ht : t ≤ s) : (11 : ℝ) / 16 ≤ 2 - Real.exp t := by
  have hTaylor := real_exp_third_order_le_cube hs0 (by linarith only [hs] : s < 5 / 6)
  have hsq := pow_le_pow_left₀ hs0 hs.le 2
  have hcube := pow_le_pow_left₀ hs0 hs.le 3
  linarith only [Real.exp_le_exp.mpr ht, hTaylor, hs, hsq, hcube]

/-- The cubic BCH remainder at an inner radius `t ≤ s < 1/4` is at most `(160/11) s³`. -/
lemma ten_mul_cube_div_two_sub_exp_le {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hs : s < 1 / 4) :
    10 * t ^ 3 / (2 - Real.exp t) ≤ 160 / 11 * s ^ 3 :=
  mul_pow_div_le_mul_pow (c := 1) (d := 11 / 16) 3 (by norm_num) ht (ht.trans hts)
    (by simpa only [one_mul] using hts) (by norm_num)
    (eleven_sixteenths_le_two_sub_exp (ht.trans hts) hs hts) (by norm_num)

/-- The logarithm denominator is at least `1/3` at every scale at most `1/2`. -/
lemma one_third_le_two_sub_exp {t : ℝ} (ht : t ≤ 1 / 2) :
    (1 : ℝ) / 3 ≤ 2 - Real.exp t := by
  have h := real_exp_third_order_le_div (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
  have he : Real.exp t ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr ht
  norm_num at h
  linarith only [h, he]

/-- The scale `1/2` lies inside the sufficient logarithm convergence radius. -/
lemma half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  have h := one_third_le_two_sub_exp (t := 1 / 2) le_rfl
  linarith only [h]

/-- At scales up to `1/4`, the quadratic and cubic corrections fit inside `s`. -/
private lemma quadratic_add_cubic_le_self {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 4) :
    s ^ 2 / 8 + 160 / 11 * s ^ 3 ≤ s := by
  calc
    _ = s * (s / 8 + 160 / 11 * s ^ 2) := by ring
    _ ≤ s * ((1 / 4) / 8 + 160 / 11 * (1 / 4) ^ 2) := by gcongr
    _ ≤ s := mul_le_of_le_one_right hs0 (by norm_num)

/-! ### Norm control for two consecutive BCH applications -/

section Norm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- Multiplication by the rational half contracts the norm by at least a factor of two. -/
lemma norm_half_smul_le (a : A) : ‖(2 : ℚ)⁻¹ • a‖ ≤ ‖a‖ / 2 := by
  calc
    _ ≤ ‖(2 : ℚ)⁻¹‖ * ‖a‖ := norm_smul_le _ _
    _ = ‖a‖ / 2 := by norm_num [← Rat.norm_cast_real, div_eq_mul_inv, mul_comm]

/-- A half-scaled first input satisfies the weighted bound for nested BCH. -/
lemma two_mul_norm_half_smul_add_norm_le (a b : A) :
    2 * ‖(2 : ℚ)⁻¹ • a‖ + ‖b‖ ≤ ‖a‖ + ‖b‖ := by
  have h := norm_half_smul_le a
  linarith only [h]

/-- The half-scaled commutator is bounded by the product of the two input norms. -/
lemma norm_half_commutator_le (x y : A) :
    ‖(2 : ℚ)⁻¹ • (x * y - y * x)‖ ≤ ‖x‖ * ‖y‖ := by
  simpa [TrotterError.nestedCommOfList, Ring.lie_def, mul_comm] using
    norm_smul_nestedCommOfList_le_of_le_one y [x] (c := (2 : ℚ)⁻¹)
      (by norm_num [← Rat.norm_cast_real])

variable [CompleteSpace A] [NormOneClass A]

/-- A weighted input bound controls the norm of the pair for a second BCH application. -/
lemma norm_bch_add_norm_le_two_mul (x y : A) {s : ℝ}
    (hxy : 2 * ‖x‖ + ‖y‖ ≤ s) (hs : s < 1 / 4) :
    ‖bch x y‖ + ‖x‖ ≤ 2 * s := by
  let s₁ := ‖x‖ + ‖y‖
  have hs0 : 0 ≤ s := (by positivity : 0 ≤ 2 * ‖x‖ + ‖y‖).trans hxy
  have hs₁0 : 0 ≤ s₁ := add_nonneg (norm_nonneg x) (norm_nonneg y)
  have hs₁ : s₁ ≤ s := by
    dsimp [s₁]
    linarith only [hxy, norm_nonneg x]
  have hs₁_log : s₁ < Real.log 2 := by
    have hhalf := half_lt_log_two
    linarith only [hs₁, hs, hhalf]
  have hcubic := ten_mul_cube_div_two_sub_exp_le hs₁0 hs₁ hs
  have herr := norm_bch_sub_add_sub_bracket_le x y hs₁_log
  have hδ : ‖bch x y - (x + y)‖ ≤ ‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hdecomp : bch x y - (x + y) =
        (bch x y - (x + y) - (2 : ℚ)⁻¹ • (x * y - y * x)) +
          (2 : ℚ)⁻¹ • (x * y - y * x) := by abel
    rw [hdecomp]
    exact (norm_add_le_of_le herr (norm_half_commutator_le x y)).trans_eq (by ring)
  have hz : ‖bch x y‖ ≤ s₁ + ‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hdecomp : bch x y = (bch x y - (x + y)) + (x + y) := by abel
    rw [hdecomp]
    have hsum : ‖x + y‖ ≤ s₁ := norm_add_le _ _
    exact (norm_add_le_of_le hδ hsum).trans_eq (by ring)
  have hprod : ‖x‖ * ‖y‖ ≤ s ^ 2 / 8 := by
    have hsq : (2 * ‖x‖ + ‖y‖) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (by positivity) hxy 2
    have hgm := four_mul_le_sq_add (2 * ‖x‖) ‖y‖
    nlinarith only [hsq, hgm]
  calc
    _ ≤ (s₁ + ‖x‖) + (‖x‖ * ‖y‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁)) := by
      linarith only [hz]
    _ ≤ s + (s ^ 2 / 8 + 160 / 11 * s ^ 3) := by
      dsimp only [s₁] at *
      linarith only [hxy, hprod, hcubic]
    _ ≤ 2 * s := by linarith only [quadratic_add_cubic_le_self hs0 hs.le]

/-- The weighted input bound places the outer BCH pair in the logarithm convergence range. -/
lemma norm_bch_add_norm_lt_log_two (x y : A) {s : ℝ}
    (hxy : 2 * ‖x‖ + ‖y‖ ≤ s) (hs : s < 1 / 4) :
    ‖bch x y‖ + ‖x‖ < Real.log 2 := by
  have hnorm := norm_bch_add_norm_le_two_mul x y hxy hs
  have hhalf := half_lt_log_two
  linarith only [hnorm, hs, hhalf]

end Norm

end FQFP.BCH
