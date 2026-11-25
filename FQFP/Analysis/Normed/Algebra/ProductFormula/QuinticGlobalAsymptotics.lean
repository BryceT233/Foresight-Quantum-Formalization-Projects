/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Asymptotics.Pow
public import FQFP.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalRemainder
public import FQFP.Analysis.Calculus.TaylorAsymptotics

/-!
# Fixed-time limits from sixth-order global remainders

A uniform sixth-order bound along positive integer step counts gives a sharp
fourth-order global coefficient. A vanishing coefficient gives sixth-order decay.

## Main results

* `FQFP.tendsto_nat_pow_four_mul_norm_of_remainder_le`.
* `FQFP.isBigO_inv_nat_pow_six_of_remainder_le`.
-/

@[expose] public noncomputable section

open Filter Asymptotics
open scoped Topology

namespace FQFP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sixth-order remainder along integer step counts gives the sharp
fixed-time fourth-order norm coefficient. -/
theorem tendsto_nat_pow_four_mul_norm_of_remainder_le (F : ℕ → E) (K : E)
    (t B : ℝ) (ht : 0 ≤ t)
    (hF : ∀ᶠ n in atTop, ‖F n - (t / n) ^ 4 • K‖ ≤ (t / n) ^ 6 * B) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * ‖F n‖) atTop (𝓝 (t ^ 4 * ‖K‖)) := by
  have hvec : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 • F n) atTop (𝓝 (t ^ 4 • K)) := by
    apply tendsto_nat_pow_smul_of_isBigO (by decide : 4 < 6)
    simpa only [smul_smul, ← mul_pow, div_eq_inv_mul] using isBigO_inv_nat_pow_of_remainder_le hF
  simpa only [norm_smul, norm_pow, Real.norm_natCast, Real.norm_of_nonneg ht] using hvec.norm

omit [NormedSpace ℝ E] in
/-- If the leading operator vanishes, a sixth-order remainder gives
`O(r⁻⁶)` along positive integer step counts. -/
theorem isBigO_inv_nat_pow_six_of_remainder_le (F : ℕ → E) (t B : ℝ)
    (hF : ∀ᶠ n in atTop, ‖F n‖ ≤ (t / n) ^ 6 * B) :
    F =O[atTop] (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 6) :=
  isBigO_inv_nat_pow_of_remainder_le hF

/-- The explicit quintic global remainder yields its sharp norm limit along
positive integer step counts. -/
theorem tendsto_nat_pow_four_mul_norm_of_quinticGlobalRemainder (F : ℕ → E) (K : E)
    (ℓ C alpha J t : ℝ) (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hF : ∀ n : ℕ, 1 ≤ n → ‖F n - (t / n) ^ 4 • K‖ ≤
      quinticGlobalRemainder ℓ C alpha J t (t / n) n) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * ‖F n‖) Filter.atTop
      (𝓝 (t ^ 4 * ‖K‖)) := by
  obtain ⟨B, hB⟩ := exists_eventually_le_pow_six_of_le_quinticGlobalRemainder hℓ hC ht hF
  exact tendsto_nat_pow_four_mul_norm_of_remainder_le F K t B ht hB

end FQFP
