/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHCommutator

import FQFP.BCH.RealScalar

/-!
# Symmetric BCH: the Strang splitting has cubic error

The symmetric product `exp (a/2) * exp b * exp (a/2)` — equivalently `exp (bch (bch (a/2) b) (a/2))`
— differs from `exp (a + b)` by `O(s³)` rather than `O(s²)`:

`‖bch (bch (a/2) b) (a/2) - (a + b)‖ ≤ 300 s³`, for `s = ‖a‖ + ‖b‖ < 1/4`.

This is why the Strang splitting is a *second-order* integrator. The mechanism is a cancellation:
`BCHCommutator.norm_bch_sub_add_sub_bracket_le` applied twice exhibits `½[a/2, b]` from the first
application and `½[z, a/2]` from the second, and the ring identity

`(z * a' - a' * z) + (a' * b - b * a') = δ * a' - a' * δ`,   `δ = z - (a' + b)`,  `a' = a/2`,

turns their sum into a single commutator whose first factor `δ` is only `O(s²)`. The three
remaining pieces are then bounded by `10 s₂³ / (2 - e^{s₂})`, `(3 s² / (2 - e^{s₁})) · (s / 2)` and
`10 s₁³ / (2 - e^{s₁})` where `s₁ = ‖a'‖ + ‖b‖` and `s₂ = ‖z‖ + ‖a'‖`, giving
`240 + 24/11 + 160/11 ≈ 256.7` in place of the stated `300`.

## Provenance and design

Ported from `Lean-BCH/BCH/Basic.lean` (`norm_symmetric_bch_sub_add_le`). The real-arithmetic
bookkeeping is isolated in `symmetric_bch_scale_bounds` and `symmetric_bch_real_core`, each estimate
being an explicit chain of order-theoretic steps rather than one large `linarith`.

The source's `norm_symmetric_bch_sub_add_lie_le` is deliberately not ported: it is this statement
verbatim under a second name.
-/

@[expose] public section

open NormedSpace TrotterError

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-! ### The scalar bounds

The real-arithmetic inputs of the Strang estimate, in the order the proof consumes them. The
quantity `2 - e^{s₁}` is the denominator of the two bounds at scale `s₁`, and it is bounded below
because `s₁ ≤ s < 1/4` forces `e^{s₁} ≤ 1 + s + s² ≤ 21/16`. -/

/-- The exponential estimates the Strang bound consumes: `eˢ ≤ 1 + s + s²`,
`2 - e^{s₁} ≥ 11/16`, and the two power bounds `s² ≤ s/4`, `s³ ≤ s²/4` for `s ≤ 1/4`. -/
private lemma exp_bounds {s s₁ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4) (hs₁_le : s₁ ≤ s) :
    Real.exp s ≤ 1 + s + s ^ 2 ∧ (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ ∧
      s ^ 2 ≤ s / 4 ∧ s ^ 3 ≤ s ^ 2 / 4 := by
  have hs56 : s < 5 / 6 := by linarith only [hs14]
  have hs_le : s ≤ 1 / 4 := le_of_lt hs14
  have hs2_le : s ^ 2 ≤ s / 4 :=
    calc s ^ 2 = s * s := by ring
      _ ≤ s * (1 / 4) := mul_le_mul_of_nonneg_left hs_le hs_nn
      _ = s / 4 := by ring
  have hs3_le : s ^ 3 ≤ s ^ 2 / 4 :=
    calc s ^ 3 = s ^ 2 * s := by ring
      _ ≤ s ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hs_le (sq_nonneg s)
      _ = s ^ 2 / 4 := by ring
  have hexp_le : Real.exp s ≤ 1 + s + s ^ 2 := by
    have hcube := real_exp_third_order_le_cube hs_nn hs56
    linarith only [hcube, hs3_le, sq_nonneg s]
  refine ⟨hexp_le, ?_, hs2_le, hs3_le⟩
  have h₁ : Real.exp s₁ ≤ Real.exp s := Real.exp_le_exp.mpr hs₁_le
  have h₂ : 1 + s + s ^ 2 ≤ 21 / 16 := by linarith only [hs2_le, hs_le]
  linarith only [h₁, h₂, hexp_le]

/-- The scalar facts used before the final assembly: `2 - e^{s₁}` is bounded below, the cubic
correction at scale `s₁` is at most `(160/11) s³`, and `s²/8 + (160/11) s³ ≤ s`. -/
private lemma symmetric_bch_scale_bounds {s s₁ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4)
    (hs₁_nn : 0 ≤ s₁) (hs₁_le : s₁ ≤ s) :
    (11 : ℝ) / 16 ≤ 2 - Real.exp s₁ ∧
      10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 ∧
      s ^ 2 / 8 + 160 / 11 * s ^ 3 ≤ s := by
  obtain ⟨_, hdenom₁_lb, hs2_le, hs3_le⟩ := exp_bounds hs_nn hs14 hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith only [hdenom₁_lb]
  have hcubic_div_bound : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₁]
    have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
    have h1 : 10 * s₁ ^ 3 ≤ 10 * s ^ 3 := mul_le_mul_of_nonneg_left hs₁3 (by norm_num)
    have h2 : 160 / 11 * s ^ 3 * (11 / 16) = 10 * s ^ 3 := by ring
    have h3 : 160 / 11 * s ^ 3 * (11 / 16) ≤ 160 / 11 * s ^ 3 * (2 - Real.exp s₁) :=
      mul_le_mul_of_nonneg_left hdenom₁_lb (by positivity)
    linarith only [h1, h2, h3]
  refine ⟨hdenom₁_lb, hcubic_div_bound, ?_⟩
  have h1 : s ^ 2 / 8 ≤ s / 32 := by linarith only [hs2_le]
  have h2 : 160 / 11 * s ^ 3 ≤ 10 / 11 * s := by
    have h3 : s ^ 3 ≤ s / 16 := by linarith only [hs3_le, hs2_le]
    linarith only [h3]
  linarith only [h1, h2, hs_nn]

/-- **The real-arithmetic core of the Strang bound**: with `s₂ ≤ 2 s`, the three pieces
`10 s₂³/(2 - e^{s₂})`, `(3 s²/(2 - e^{s₁}))·(s/2)` and `10 s₁³/(2 - e^{s₁})` sum to at most
`300 s³`. The denominators are bounded by `1/3` (at `s₂`, via `s₂ < 1/2`) and `11/16` (at `s₁`),
giving `240 + 24/11 + 160/11 ≈ 256.7 ≤ 300`. -/
private lemma symmetric_bch_real_core {s s₁ s₂ : ℝ} (hs_nn : 0 ≤ s) (hs14 : s < 1 / 4)
    (hs₁_nn : 0 ≤ s₁) (hs₁_le : s₁ ≤ s) (hs₂_nn : 0 ≤ s₂) (hs₂_le : s₂ ≤ 2 * s) :
    10 * s₂ ^ 3 / (2 - Real.exp s₂) + 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) +
      10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 300 * s ^ 3 := by
  obtain ⟨-, hdenom₁_lb, -, -⟩ := exp_bounds hs_nn hs14 hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith only [hdenom₁_lb]
  -- `2 - e^{s₂} ≥ 1/3`, via `e^{s₂} ≤ 1 + s₂ + s₂²/2 + s₂³/3` and `s₂ ≤ 2s`
  have hs₂_lt : s₂ < 1 / 2 := by linarith
  have hs₂_lt_one : s₂ < 1 := by linarith
  have hexp_s₂_ub : Real.exp s₂ ≤ 1 + s₂ + s₂ ^ 2 / 2 + s₂ ^ 3 / 3 := by
    have h := real_exp_third_order_le_div hs₂_nn hs₂_lt_one
    have hc : s₂ ^ 3 / (6 * (1 - s₂)) ≤ s₂ ^ 3 / 3 :=
      div_le_div_of_nonneg_left (pow_nonneg hs₂_nn 3) (by norm_num) (by linarith)
    linarith
  have hdenom₂_lb : (1 : ℝ) / 3 ≤ 2 - Real.exp s₂ := by
    have hsq : s₂ ^ 2 ≤ 4 * s ^ 2 := by
      have h := pow_le_pow_left₀ hs₂_nn hs₂_le 2
      rwa [show (2 * s) ^ 2 = 4 * s ^ 2 from by ring] at h
    have hcu : s₂ ^ 3 ≤ 8 * s ^ 3 := by
      calc s₂ ^ 3 = s₂ * s₂ ^ 2 := by ring
        _ ≤ (2 * s) * (4 * s ^ 2) := mul_le_mul hs₂_le hsq (sq_nonneg _) (by linarith)
        _ = 8 * s ^ 3 := by ring
    have hsum : s₂ + s₂ ^ 2 / 2 + s₂ ^ 3 / 3 ≤ 2 / 3 := by
      have hpoly : 2 * s + 2 * s ^ 2 + 8 / 3 * s ^ 3 ≤ 2 / 3 := by
        have hfac : 2 / 3 - (2 * s + 2 * s ^ 2 + 8 / 3 * s ^ 3) =
            2 * (1 - 4 * s) / 3 + 2 * s * (1 - 3 * s - 4 * s ^ 2) / 3 := by ring
        have h14 : 0 ≤ 1 - 4 * s := by linarith
        have hinner : 0 ≤ 1 - 3 * s - 4 * s ^ 2 := by
          rw [show 1 - 3 * s - 4 * s ^ 2 = (1 - 4 * s) * (1 + s) from by ring]
          exact mul_nonneg h14 (by linarith)
        linarith [mul_nonneg hs_nn hinner]
      linarith
    linarith
  have hdenom₂ : 0 < 2 - Real.exp s₂ := by linarith
  -- the three pieces
  have hterm1 : 10 * s₂ ^ 3 / (2 - Real.exp s₂) ≤ 240 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₂]
    have hs₂3 : s₂ ^ 3 ≤ 8 * s ^ 3 := by
      have h := pow_le_pow_left₀ hs₂_nn hs₂_le 3
      rwa [show (2 * s) ^ 3 = 8 * s ^ 3 from by ring] at h
    have h1 : 240 * s ^ 3 * (1 / 3) ≤ 240 * s ^ 3 * (2 - Real.exp s₂) :=
      mul_le_mul_of_nonneg_left hdenom₂_lb (by positivity)
    have h2 : 10 * s₂ ^ 3 ≤ 240 * s ^ 3 * (1 / 3) := by linarith [pow_nonneg hs_nn 3]
    linarith
  have hterm2 : 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) ≤ 24 / 11 * s ^ 3 := by
    have hdiv : 3 * s ^ 2 / (2 - Real.exp s₁) ≤ 3 * s ^ 2 / (11 / 16) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom₁_lb
    calc 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2)
        ≤ 3 * s ^ 2 / (11 / 16) * (s / 2) := mul_le_mul_of_nonneg_right hdiv (by linarith)
      _ = 24 / 11 * s ^ 3 := by ring
  have hterm3 : 10 * s₁ ^ 3 / (2 - Real.exp s₁) ≤ 160 / 11 * s ^ 3 := by
    rw [div_le_iff₀ hdenom₁]
    have hs₁3 : s₁ ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hs₁_nn hs₁_le 3
    have h1 : 10 * s₁ ^ 3 ≤ 10 * s ^ 3 := mul_le_mul_of_nonneg_left hs₁3 (by norm_num)
    have h2 : 160 / 11 * s ^ 3 * (11 / 16) = 10 * s ^ 3 := by ring
    have h3 : 160 / 11 * s ^ 3 * (11 / 16) ≤ 160 / 11 * s ^ 3 * (2 - Real.exp s₁) :=
      mul_le_mul_of_nonneg_left hdenom₁_lb (by positivity)
    linarith
  linarith [hterm1, hterm2, hterm3, pow_nonneg hs_nn 3]

/-! ### The Strang bound -/

/-- **Symmetric BCH (Strang splitting)**: `bch (bch (a/2) b) (a/2) = a + b + O(s³)`, with an
explicit constant: `‖· - (a + b)‖ ≤ 300 s³` for `s = ‖a‖ + ‖b‖ < 1/4`.

The second-order commutators `½[a/2, b]` and `½[bch (a/2) b, a/2]` cancel, which is exactly what
makes the Strang splitting a second-order integrator. -/
theorem norm_symmetric_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (bch ((2 : ℚ)⁻¹ • a) b) ((2 : ℚ)⁻¹ • a) - (a + b)‖ ≤ 300 * (‖a‖ + ‖b‖) ^ 3 := by
  set a' : 𝔸 := (2 : ℚ)⁻¹ • a with ha'_def
  set s : ℝ := ‖a‖ + ‖b‖ with hs_def
  have hhalf_norm : ‖(2 : ℚ)⁻¹‖ = (2 : ℝ)⁻¹ := by
    rw [norm_inv, ← Rat.norm_cast_real]
    norm_num
  have ha'_le : ‖a'‖ ≤ ‖a‖ / 2 := by
    calc ‖a'‖ ≤ ‖(2 : ℚ)⁻¹‖ * ‖a‖ := norm_smul_le _ _
      _ = ‖a‖ / 2 := by rw [hhalf_norm]; ring
  have ha'_le_a : ‖a'‖ ≤ ‖a‖ := by linarith [norm_nonneg a]
  have hs_nn : 0 ≤ s := by rw [hs_def]; positivity
  have hs14 : s < 1 / 4 := by rw [hs_def]; exact hab
  set s₁ : ℝ := ‖a'‖ + ‖b‖ with hs₁_def
  have hs₁_le : s₁ ≤ s := by rw [hs₁_def, hs_def]; linarith [ha'_le_a]
  have hs₁_nn : 0 ≤ s₁ := by rw [hs₁_def]; positivity
  have ha_le_s : ‖a‖ ≤ s := by rw [hs_def]; exact le_add_of_nonneg_right (norm_nonneg b)
  have hb_le_s : ‖b‖ ≤ s := by rw [hs_def]; exact le_add_of_nonneg_left (norm_nonneg a)
  obtain ⟨hdenom₁_lb, hcubic_div_bound, hscale⟩ :=
    symmetric_bch_scale_bounds hs_nn hs14 hs₁_nn hs₁_le
  have hdenom₁ : 0 < 2 - Real.exp s₁ := by linarith
  -- both BCH applications are inside the radius of convergence
  have hlog2 : (1 : ℝ) / 4 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    have h := real_exp_third_order_le_cube (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 : ℝ) / 4 < 5 / 6)
    linarith
  -- needed for `s₂`, which is only known to satisfy `s₂ < 1 / 2`
  have hlog2_half : (1 : ℝ) / 2 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    have h := real_exp_third_order_le_cube (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 5 / 6)
    linarith
  have hs₁_log2 : s₁ < Real.log 2 := by linarith
  set z : 𝔸 := bch a' b with hz_def
  -- the two commutator norm bounds
  have hhalf_bracket : ‖(2 : ℚ)⁻¹ • (a' * b - b * a')‖ ≤ ‖a'‖ * ‖b‖ := by
    calc ‖(2 : ℚ)⁻¹ • (a' * b - b * a')‖
        ≤ ‖(2 : ℚ)⁻¹‖ * ‖a' * b - b * a'‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (‖a' * b‖ + ‖b * a'‖) := by
          rw [hhalf_norm]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
      _ ≤ (2 : ℝ)⁻¹ * (‖a'‖ * ‖b‖ + ‖b‖ * ‖a'‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            (by norm_num)
      _ = ‖a'‖ * ‖b‖ := by ring
  -- the two copies of the cubic bound
  have hR₃' : ‖z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a')‖ ≤
      10 * s₁ ^ 3 / (2 - Real.exp s₁) :=
    norm_bch_sub_add_sub_bracket_le a' b hs₁_log2
  -- `‖z - (a' + b)‖`, tightly enough to reach `s₂ ≤ 2s`
  have hδ_tight : ‖z - (a' + b)‖ ≤ ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have h : z - (a' + b) =
        (z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a')) +
          (2 : ℚ)⁻¹ • (a' * b - b * a') := by abel
    rw [h]
    exact (norm_add_le _ _).trans
      ((add_le_add hR₃' hhalf_bracket).trans_eq (by ring))
  have hz_le : ‖z‖ ≤ s₁ + ‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁) := by
    have hab_le : ‖a' + b‖ ≤ s₁ := norm_add_le a' b
    have h : z = (z - (a' + b)) + (a' + b) := by abel
    rw [h]
    linarith [norm_add_le (z - (a' + b)) (a' + b), hδ_tight, hab_le]
  have hab_prod : ‖a'‖ * ‖b‖ ≤ s ^ 2 / 8 := by
    have h2a'_b : 2 * ‖a'‖ + ‖b‖ ≤ s := by rw [hs_def]; linarith [ha'_le, norm_nonneg b]
    have hx_nn : 0 ≤ 2 * ‖a'‖ + ‖b‖ := by positivity
    have hsq : (2 * ‖a'‖ + ‖b‖) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hx_nn h2a'_b 2
    have hgm : 8 * (‖a'‖ * ‖b‖) ≤ (2 * ‖a'‖ + ‖b‖) ^ 2 :=
      calc 8 * (‖a'‖ * ‖b‖) = 4 * (2 * ‖a'‖) * ‖b‖ := by ring
        _ ≤ (2 * ‖a'‖ + ‖b‖) ^ 2 := four_mul_le_sq_add (2 * ‖a'‖) ‖b‖
    linarith
  set s₂ : ℝ := ‖z‖ + ‖a'‖ with hs₂_def
  have hs₁a'_le : s₁ + ‖a'‖ ≤ s := by rw [hs₁_def, hs_def]; linarith [ha'_le]
  have hs₂_le_2s : s₂ ≤ 2 * s := by
    rw [hs₂_def]
    calc ‖z‖ + ‖a'‖
        ≤ (s₁ + ‖a'‖) + (‖a'‖ * ‖b‖ + 10 * s₁ ^ 3 / (2 - Real.exp s₁)) := by
          linarith [hz_le]
      _ ≤ s + (s ^ 2 / 8 + 160 / 11 * s ^ 3) := by
          linarith [hs₁a'_le, hab_prod, hcubic_div_bound]
      _ ≤ 2 * s := by linarith [hscale]
  have hs₂_nn : 0 ≤ s₂ := by rw [hs₂_def]; positivity
  have hs₂_log2 : s₂ < Real.log 2 := by linarith
  have hR₃'' : ‖bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)‖ ≤
      10 * s₂ ^ 3 / (2 - Real.exp s₂) :=
    norm_bch_sub_add_sub_bracket_le z a' hs₂_log2
  -- the cancellation identity and the algebraic decomposition
  set δ : 𝔸 := z - (a' + b) with hδ_def
  have hcomm_cancel : (z * a' - a' * z) + (a' * b - b * a') = δ * a' - a' * δ := by
    rw [hδ_def]; noncomm_ring
  have ha'_add : a' + a' = a := by
    rw [ha'_def, ← add_smul, show (2 : ℚ)⁻¹ + (2 : ℚ)⁻¹ = 1 from by
      rw [← two_mul, mul_inv_cancel₀ (two_ne_zero : (2 : ℚ) ≠ 0)]]
    exact one_smul _ _
  have hfull : bch z a' - (a + b) =
      (bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)) +
      ((2 : ℚ)⁻¹ • (δ * a' - a' * δ)) +
      (z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a')) := by
    have hsmul_expand : (2 : ℚ)⁻¹ • (δ * a' - a' * δ) =
        (2 : ℚ)⁻¹ • (z * a' - a' * z) + (2 : ℚ)⁻¹ • (a' * b - b * a') := by
      rw [← smul_add, ← hcomm_cancel]
    rw [hsmul_expand, ← ha'_add]
    abel
  -- the middle piece
  have hcomm_bound : ‖(2 : ℚ)⁻¹ • (δ * a' - a' * δ)‖ ≤ ‖δ‖ * ‖a'‖ := by
    calc ‖(2 : ℚ)⁻¹ • (δ * a' - a' * δ)‖
        ≤ ‖(2 : ℚ)⁻¹‖ * ‖δ * a' - a' * δ‖ := norm_smul_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (‖δ * a'‖ + ‖a' * δ‖) := by
          rw [hhalf_norm]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
      _ ≤ (2 : ℝ)⁻¹ * (‖δ‖ * ‖a'‖ + ‖a'‖ * ‖δ‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            (by norm_num)
      _ = ‖δ‖ * ‖a'‖ := by ring
  have hδ_le : ‖δ‖ ≤ 3 * s₁ ^ 2 / (2 - Real.exp s₁) := by
    rw [hδ_def]
    exact norm_bch_sub_add_le a' b hs₁_log2
  have ha'_le_s2 : ‖a'‖ ≤ s / 2 := by linarith [ha'_le, ha_le_s]
  have hδ_cubic : ‖δ‖ * ‖a'‖ ≤ 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) := by
    have h1 : ‖δ‖ * ‖a'‖ ≤ (3 * s₁ ^ 2 / (2 - Real.exp s₁)) * (s / 2) :=
      mul_le_mul hδ_le ha'_le_s2 (norm_nonneg _) (div_nonneg (by positivity) hdenom₁.le)
    have hs₁2 : 3 * s₁ ^ 2 ≤ 3 * s ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs₁_nn hs₁_le 2) (by norm_num)
    have h2 : 3 * s₁ ^ 2 / (2 - Real.exp s₁) ≤ 3 * s ^ 2 / (2 - Real.exp s₁) :=
      div_le_div_of_nonneg_right hs₁2 hdenom₁.le
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (by linarith))
  -- assemble
  have hbound : ‖(bch z a' - (z + a') - (2 : ℚ)⁻¹ • (z * a' - a' * z)) +
        ((2 : ℚ)⁻¹ • (δ * a' - a' * δ)) +
        (z - (a' + b) - (2 : ℚ)⁻¹ • (a' * b - b * a'))‖ ≤
      10 * s₂ ^ 3 / (2 - Real.exp s₂) + 3 * s ^ 2 / (2 - Real.exp s₁) * (s / 2) +
        10 * s₁ ^ 3 / (2 - Real.exp s₁) :=
    (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hR₃'' (hcomm_bound.trans hδ_cubic)))
        hR₃')
  rw [hfull]
  exact hbound.trans (symmetric_bch_real_core hs_nn hs14 hs₁_nn hs₁_le hs₂_nn hs₂_le_2s)

end

end FQFP.BCH
