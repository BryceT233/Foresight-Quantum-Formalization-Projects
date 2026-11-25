/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Scalar estimates for equal time steps

A local power bound controls the quadratic error accumulated over pairs of steps.
At fixed nonnegative time, sufficiently fine subdivisions satisfy any positive step-size bound.
-/

public section

namespace FQFP

open Filter

/-- With total time `t = r * h`, a local error of order `p + 1` contributes
at most a term of order `2 * p` when accumulated over pairs of steps. -/
lemma quadratic_accumulation_le_of_step_le_pow {r : ℕ} {t h δ C : ℝ} {p : ℕ}
    (hr : 1 ≤ r) (ht : (r : ℝ) * h = t) (hδ : 0 ≤ δ) (hstep : δ ≤ h ^ (p + 1) * C) :
    (r : ℝ) * ((r : ℝ) - 1) / 2 * δ ^ 2 ≤ t ^ 2 / 2 * h ^ (2 * p) * C ^ 2 := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  calc
    _ ≤ (r : ℝ) * r / 2 * (h ^ (p + 1) * C) ^ 2 := by
      gcongr
      exact sub_le_self _ zero_le_one
    _ = _ := by
      rw [← ht, pow_succ, Nat.mul_comm 2 p, pow_mul]
      ring

/-- A bound valid for every positive subdivision with step size at most `ε`
holds eventually for the equal steps `t / r` at fixed nonnegative time. -/
lemma eventually_div_natCast_of_forall_step {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε)
    {P : ℕ → ℝ → Prop}
    (hP : ∀ {r : ℕ} {h : ℝ}, 0 ≤ h → h ≤ ε → 1 ≤ r → (r : ℝ) * h = t → P r h) :
    ∀ᶠ r : ℕ in atTop, P r (t / r) := by
  filter_upwards [(tendsto_const_div_atTop_nhds_zero_nat t).eventually_lt_const hε,
    eventually_gt_atTop 0] with r hh hr
  exact hP (div_nonneg ht (Nat.cast_nonneg r)) hh.le hr
    (mul_div_cancel₀ t (Nat.cast_ne_zero.mpr hr.ne'))

end FQFP
