/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHComposition
public import FQFP.BCH.BCHRemainderNonic

/-!
# Remainders for the two legs of symmetric BCH

For `h = a/2` and `z = bch h b`, the inner leg has inputs `(h, b)` and the outer leg
has inputs `(z, h)`. On `‖a‖ + ‖b‖ < 1/4`, both pairs lie in the BCH convergence range.
Their seventh- and ninth-order remainders retain the constants of the source estimates.

## Main results

* `norm_bch_inner_septic_remainder_le`: inner seventh-order constant `1500000`.
* `norm_bch_outer_septic_remainder_le`: outer seventh-order constant `12000000000`.
* `norm_bch_inner_nonic_remainder_le`: inner ninth-order constant `200000000`.
* `norm_bch_outer_nonic_remainder_le`: outer ninth-order constant `250000000000`.

The local `let` bindings in the statements abbreviate the actual BCH inputs; no new
polynomial or remainder is defined.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

private lemma mul_pow_div_le_mul_pow {K M r s c d D : ℝ} (n : ℕ)
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

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
  [CompleteSpace A] [NormOneClass A]

/-- The half-step specialization of the common composition input estimates. -/
private lemma half_input_bounds (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let h := (2 : ℚ)⁻¹ • a
    let s := ‖a‖ + ‖b‖
    (‖h‖ + ‖b‖ ≤ s ∧ ‖h‖ + ‖b‖ < Real.log 2 ∧
      (11 : ℝ) / 16 ≤ 2 - Real.exp (‖h‖ + ‖b‖)) ∧
    (‖bch h b‖ + ‖h‖ ≤ 2 * s ∧ ‖bch h b‖ + ‖h‖ < Real.log 2 ∧
      (1 : ℝ) / 3 ≤ 2 - Real.exp (‖bch h b‖ + ‖h‖)) := by
  dsimp only
  have hw := two_mul_norm_half_smul_add_norm_le a b
  have hinner : ‖(2 : ℚ)⁻¹ • a‖ + ‖b‖ ≤ ‖a‖ + ‖b‖ := by
    linarith only [hw, norm_nonneg ((2 : ℚ)⁻¹ • a)]
  have hdinner := eleven_sixteenths_le_two_sub_exp
    (add_nonneg (norm_nonneg a) (norm_nonneg b)) hab hinner
  have houter := norm_bch_add_norm_le_two_mul ((2 : ℚ)⁻¹ • a) b hw hab
  have hdouter := one_third_le_two_sub_exp
    (show ‖bch ((2 : ℚ)⁻¹ • a) b‖ + ‖(2 : ℚ)⁻¹ • a‖ ≤ 1 / 2 by
      linarith only [houter, hab])
  refine ⟨⟨hinner, ?_, hdinner⟩, houter, ?_, hdouter⟩
  · rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    linarith only [hdinner]
  · rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    linarith only [hdouter]

/-- The inner seventh-order remainder has constant `1500000` on the symmetric input ball. -/
theorem norm_bch_inner_septic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let h := (2 : ℚ)⁻¹ • a
    ‖bch h b - (h + b) - (2 : ℚ)⁻¹ • (h * b - b * h) - bchCubicTerm h b -
      bchQuarticTerm h b - bchQuinticTerm h b - bchSexticTerm h b‖ ≤
      1500000 * (‖a‖ + ‖b‖) ^ 7 := by
  dsimp only
  obtain ⟨⟨hr, hconv, hd⟩, -⟩ := half_input_bounds a b hab
  exact (norm_bch_septic_remainder_le _ _ hconv).trans
    (mul_pow_div_le_mul_pow (c := 1) (d := 11 / 16) 7 (by norm_num)
      (by positivity) (by positivity) (by simpa only [one_mul] using hr)
      (by norm_num) hd (by norm_num))

/-- The outer seventh-order remainder has constant `12000000000` on the symmetric input ball. -/
theorem norm_bch_outer_septic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let h := (2 : ℚ)⁻¹ • a
    let z := bch h b
    ‖bch z h - (z + h) - (2 : ℚ)⁻¹ • (z * h - h * z) - bchCubicTerm z h -
      bchQuarticTerm z h - bchQuinticTerm z h - bchSexticTerm z h‖ ≤
      12000000000 * (‖a‖ + ‖b‖) ^ 7 := by
  dsimp only
  obtain ⟨-, hr, hconv, hd⟩ := half_input_bounds a b hab
  exact (norm_bch_septic_remainder_le _ _ hconv).trans
    (mul_pow_div_le_mul_pow (c := 2) (d := 1 / 3) 7 (by norm_num)
      (by positivity) (by positivity) hr (by norm_num) hd (by norm_num))

/-- The inner ninth-order remainder has constant `200000000` on the symmetric input ball. -/
theorem norm_bch_inner_nonic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let h := (2 : ℚ)⁻¹ • a
    ‖bch h b - (h + b) - (2 : ℚ)⁻¹ • (h * b - b * h) - bchCubicTerm h b -
      bchQuarticTerm h b - bchQuinticTerm h b - bchSexticTerm h b -
      bchSepticTerm h b - bchOcticTerm h b‖ ≤
      200000000 * (‖a‖ + ‖b‖) ^ 9 := by
  dsimp only
  obtain ⟨⟨hr, hconv, hd⟩, -⟩ := half_input_bounds a b hab
  exact (norm_bch_nonic_remainder_le _ _ hconv).trans
    (mul_pow_div_le_mul_pow (c := 1) (d := 11 / 16) 9 (by norm_num)
      (by positivity) (by positivity) (by simpa only [one_mul] using hr)
      (by norm_num) hd (by norm_num))

/-- The outer ninth-order remainder has constant `250000000000` on the symmetric input ball. -/
theorem norm_bch_outer_nonic_remainder_le (a b : A) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    let h := (2 : ℚ)⁻¹ • a
    let z := bch h b
    ‖bch z h - (z + h) - (2 : ℚ)⁻¹ • (z * h - h * z) - bchCubicTerm z h -
      bchQuarticTerm z h - bchQuinticTerm z h - bchSexticTerm z h -
      bchSepticTerm z h - bchOcticTerm z h‖ ≤
      250000000000 * (‖a‖ + ‖b‖) ^ 9 := by
  dsimp only
  obtain ⟨-, hr, hconv, hd⟩ := half_input_bounds a b hab
  exact (norm_bch_nonic_remainder_le _ _ hconv).trans
    (mul_pow_div_le_mul_pow (c := 2) (d := 1 / 3) 9 (by norm_num)
      (by positivity) (by positivity) hr (by norm_num) hd (by norm_num))

end FQFP.BCH
