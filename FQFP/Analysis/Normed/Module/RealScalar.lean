/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.Linarith

/-!
# Norm bounds for real scalar multiples

Bounds use only the real scalar norm; no exponential construction is required.

## Main results

* `TrotterError.norm_smul_le_of_abs_le_one`.
* `TrotterError.norm_smul_exp_arg_le`.
-/

@[expose] public section

namespace TrotterError

/-- `|c| ≤ 1` implies `‖c • A‖ ≤ ‖A‖` in any normed algebra. -/
lemma norm_smul_le_of_abs_le_one {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) : ‖c • A‖ ≤ ‖A‖ := by
  calc
    ‖c • A‖ = |c| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖A‖ := one_mul _

/-- For `u ≤ 1`, `0 ≤ t`, and `|c| ≤ 1`, the exponential argument `(u * t) * ‖c • A‖` is at
most `t * ‖A‖`. -/
lemma norm_smul_exp_arg_le {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]
    (c : ℝ) (A : 𝔸) (hc : |c| ≤ 1) (u t : ℝ) (ht : 0 ≤ t) (hu1 : u ≤ 1) :
    (u * t) * ‖c • A‖ ≤ t * ‖A‖ := by
  have hc' : u * |c| ≤ 1 := by
    simpa using mul_le_mul hu1 hc (abs_nonneg _) zero_le_one
  have hle : u * t * |c| ≤ t := by
    calc
      u * t * |c| = t * (u * |c|) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hc' ht
      _ = t := mul_one _
  calc
    (u * t) * ‖c • A‖ = u * t * |c| * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ ≤ t * ‖A‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

end TrotterError
