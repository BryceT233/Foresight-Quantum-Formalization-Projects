/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar remainders for quintic global error estimates

The local and global remainder polynomials retain the original commutator
constants. Their small-step estimates give fixed-time asymptotics along integers.

## Main definitions

* `FQFP.quinticStepBound`: the local error bound capped at two.
* `FQFP.quinticCenteredRemainder`: the centered local remainder.
* `FQFP.quinticGlobalRemainder`: the continuous global remainder.
-/

@[expose] public noncomputable section

namespace FQFP

/-- The local norm bound, capped by the distance between two contractions. -/
def quinticStepBound (ℓ C h : ℝ) : ℝ := min 2 (h ^ 5 * ℓ + h ^ 7 * C)

/-- The centered local remainder with its unsplit second commutator constant. -/
def quinticCenteredRemainder (ℓ C alpha h : ℝ) : ℝ :=
  h ^ 7 * (C + 5 / 14 * alpha) + 1 / 2 * h ^ 10 * ℓ ^ 2 +
    5 / 12 * h ^ 12 * ℓ * C

/-- The global operator remainder, including the finite-product quadratic term. -/
def quinticGlobalRemainder (ℓ C alpha J t h : ℝ) (r : ℕ) : ℝ :=
  t * h ^ 6 * (C + 5 / 14 * alpha + J / 24) + t / 2 * h ^ 9 * ℓ ^ 2 +
    5 * t / 12 * h ^ 11 * ℓ * C +
      (r : ℝ) * ((r : ℝ) - 1) / 2 * quinticStepBound ℓ C h ^ 2

/-- A nonnegative step gives a nonnegative capped local bound. -/
lemma quinticStepBound_nonneg {ℓ C h : ℝ} (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C)
    (hh : 0 ≤ h) : 0 ≤ quinticStepBound ℓ C h := by
  unfold quinticStepBound
  positivity

/-- The discrete remainder plus the midpoint error equals the global remainder. -/
lemma quinticGlobalRemainder_eq (ℓ C alpha J t h : ℝ) (r : ℕ)
    (ht : (r : ℝ) * h = t) :
    quinticGlobalRemainder ℓ C alpha J t h r =
      (r : ℝ) * quinticCenteredRemainder ℓ C alpha h +
        (r : ℝ) * ((r : ℝ) - 1) / 2 * quinticStepBound ℓ C h ^ 2 +
          h ^ 4 * (t * h ^ 2 * J / 24) := by
  rw [← ht]
  unfold quinticGlobalRemainder quinticCenteredRemainder
  ring

/-- For steps at most one, the original remainder is bounded by a fixed
multiple of the sixth power of the step. -/
theorem quinticGlobalRemainder_le_pow_six {ℓ C alpha J t h : ℝ} {r : ℕ}
    (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hr : 1 ≤ r) (ht : (r : ℝ) * h = t) :
    quinticGlobalRemainder ℓ C alpha J t h r ≤ h ^ 6 *
      (t * (C + 5 / 14 * alpha + J / 24) + t / 2 * ℓ ^ 2 +
        5 * t / 12 * ℓ * C + t ^ 2 / 2 * (ℓ + C) ^ 2) := by
  have ht0 : 0 ≤ t := ht ▸ mul_nonneg (Nat.cast_nonneg _) hh
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd0 := quinticStepBound_nonneg hℓ hC hh
  have hd : quinticStepBound ℓ C h ≤ h ^ 5 * (ℓ + C) := by
    calc
      _ ≤ h ^ 5 * ℓ + h ^ 7 * C := min_le_right _ _
      _ ≤ h ^ 5 * ℓ + h ^ 5 * C := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hh hh1 (by decide : 5 ≤ 7)) hC)
      _ = _ := by ring
  have hquad : (r : ℝ) * ((r : ℝ) - 1) / 2 * quinticStepBound ℓ C h ^ 2 ≤
      t ^ 2 / 2 * h ^ 6 * (ℓ + C) ^ 2 := by
    calc
      _ ≤ (r : ℝ) ^ 2 / 2 * (h ^ 5 * (ℓ + C)) ^ 2 := by
        gcongr
        nlinarith
      _ = t ^ 2 / 2 * h ^ 8 * (ℓ + C) ^ 2 := by
        rw [← ht]
        ring
      _ ≤ t ^ 2 / 2 * h ^ 6 * (ℓ + C) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hh hh1 (by decide : 6 ≤ 8)) (by positivity))
          (sq_nonneg _)
  unfold quinticGlobalRemainder
  calc
    _ ≤ t * h ^ 6 * (C + 5 / 14 * alpha + J / 24) + t / 2 * h ^ 6 * ℓ ^ 2 +
        5 * t / 12 * h ^ 6 * ℓ * C + t ^ 2 / 2 * h ^ 6 * (ℓ + C) ^ 2 := by
      apply add_le_add _ hquad
      apply add_le_add
      · apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hh hh1 (by decide : 6 ≤ 9)) (by positivity))
          (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hh hh1 (by decide : 6 ≤ 11)) (by positivity)) hℓ) hC
    _ = _ := by ring

/-- At fixed nonnegative time, the sixth-power remainder bound holds
eventually along positive integer step counts. -/
theorem eventually_quinticGlobalRemainder_le_pow_six {ℓ C t : ℝ} (alpha J : ℝ)
    (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    ∀ᶠ r : ℕ in Filter.atTop,
      quinticGlobalRemainder ℓ C alpha J t (t / r) r ≤ (t / r) ^ 6 *
        (t * (C + 5 / 14 * alpha + J / 24) + t / 2 * ℓ ^ 2 +
          5 * t / 12 * ℓ * C + t ^ 2 / 2 * (ℓ + C) ^ 2) := by
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat t).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with r hsmall hr
  apply quinticGlobalRemainder_le_pow_six hℓ hC
    (div_nonneg ht (Nat.cast_nonneg r)) hsmall.le hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by lia)
  exact mul_div_cancel₀ t hr0

end FQFP
