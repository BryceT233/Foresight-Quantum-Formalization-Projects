/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.StepBounds
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.GCongr
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
  have hd : quinticStepBound ℓ C h ≤ h ^ 5 * (ℓ + C) := by
    calc
      _ ≤ h ^ 5 * ℓ + h ^ 7 * C := min_le_right _ _
      _ ≤ h ^ 5 * ℓ + h ^ 5 * C := by
        gcongr h ^ 5 * ℓ + ?_ * C
        exact pow_le_pow_of_le_one hh hh1 (by decide : 5 ≤ 7)
      _ = _ := by ring
  have hlocal : quinticCenteredRemainder ℓ C alpha h ≤
      h ^ 7 * (C + 5 / 14 * alpha + ℓ ^ 2 / 2 + 5 / 12 * ℓ * C) := by
    unfold quinticCenteredRemainder
    calc
      _ ≤ h ^ 7 * (C + 5 / 14 * alpha) + 1 / 2 * h ^ 7 * ℓ ^ 2 +
          5 / 12 * h ^ 7 * ℓ * C := by
        gcongr h ^ 7 * _ + 1 / 2 * ?_ * ℓ ^ 2 + 5 / 12 * ?_ * ℓ * C
        · exact pow_le_pow_of_le_one hh hh1 (by decide : 7 ≤ 10)
        · exact pow_le_pow_of_le_one hh hh1 (by decide : 7 ≤ 12)
      _ = _ := by ring
  have hacc := linear_quadratic_accumulation_le_of_step_le_pow (p := 4) (q := 6) hr ht hlocal
    (quinticStepBound_nonneg hℓ hC hh) hd (pow_le_pow_of_le_one hh hh1 (by decide))
  rw [quinticGlobalRemainder_eq _ _ _ _ _ _ _ ht]
  refine (add_le_add hacc le_rfl).trans_eq ?_
  ring

/-- At fixed nonnegative time, the sixth-power remainder bound holds
eventually along positive integer step counts. -/
theorem eventually_quinticGlobalRemainder_le_pow_six {ℓ C t : ℝ} (alpha J : ℝ)
    (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    ∀ᶠ r : ℕ in Filter.atTop,
      quinticGlobalRemainder ℓ C alpha J t (t / r) r ≤ (t / r) ^ 6 *
        (t * (C + 5 / 14 * alpha + J / 24) + t / 2 * ℓ ^ 2 +
          5 * t / 12 * ℓ * C + t ^ 2 / 2 * (ℓ + C) ^ 2) :=
  eventually_div_natCast_of_forall_step ht zero_lt_one fun hh hh1 hr hrh ↦
    quinticGlobalRemainder_le_pow_six hℓ hC hh hh1 hr hrh

/-- A sequence bounded by the quintic global remainder at positive step counts
is eventually bounded by a constant times the sixth power of the step size. -/
lemma exists_eventually_le_pow_six_of_le_quinticGlobalRemainder
    {f : ℕ → ℝ} {ℓ C alpha J t : ℝ} (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hf : ∀ n : ℕ, 1 ≤ n → f n ≤ quinticGlobalRemainder ℓ C alpha J t (t / n) n) :
    ∃ B : ℝ, ∀ᶠ n : ℕ in Filter.atTop, f n ≤ (t / n) ^ 6 * B := by
  have hbound := eventually_quinticGlobalRemainder_le_pow_six alpha J hℓ hC ht
  exact ⟨_, ((Filter.eventually_ge_atTop 1).and hbound).mono fun n ⟨hn, hrem⟩ ↦
    (hf n hn).trans hrem⟩

end FQFP
