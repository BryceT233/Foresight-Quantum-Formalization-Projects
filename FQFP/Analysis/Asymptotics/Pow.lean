/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Power-order asymptotics near zero

Power comparison and addition, multiplication and boundedness rules.

## Main results

* `TrotterError.eventually_abs_le_one_nhds_zero`.
* `TrotterError.isBigO_abs_pow_abs_pow_of_le`.
* `TrotterError.orderCond_add`.
* `TrotterError.orderCond_mul`.
* `TrotterError.isBigO_norm_one_of_continuous`.
* `TrotterError.orderCond_mul_left`.
* `TrotterError.neg_pow_isBigO`.
* `TrotterError.tendsto_neg_nhds_zero`.
-/

@[expose] public section

namespace TrotterError

open Asymptotics Finset
open scoped Topology BigOperators

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- For `|τ| ≤ 1` in a neighborhood of `0`, the function `|τ|^n` is bounded by `|τ|^m` whenever
`m ≤ n`. -/
lemma eventually_abs_le_one_nhds_zero : ∀ᶠ τ in 𝓝 (0 : ℝ), |τ| ≤ 1 := by
  refine Filter.mem_of_superset
    (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : 0 < (1 : ℝ))) ?_
  intro τ hτ
  simpa [Metric.closedBall, dist_eq_norm, sub_zero] using hτ

/-- For `m ≤ n`, `|τ|^n = O(|τ|^m)` as `τ → 0`. -/
lemma isBigO_abs_pow_abs_pow_of_le {m n : ℕ} (hmn : m ≤ n) :
    (fun τ : ℝ => |τ| ^ n) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => |τ| ^ m) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_abs_le_one_nhds_zero] with τ hτ
  have hnn : 0 ≤ |τ| := abs_nonneg τ
  rw [Real.norm_of_nonneg (pow_nonneg hnn n), Real.norm_of_nonneg (pow_nonneg hnn m), one_mul]
  exact pow_le_pow_of_le_one hnn hτ hmn

/-- Addition rule (order.tex:80): `F = O(τ^p)` and `G = O(τ^q)` imply `F + G = O(τ^{min p q})`. -/
theorem orderCond_add (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q) := by
  have htri : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖F τ‖ + ‖G τ‖) := by
    refine Filter.Eventually.isBigO ?_
    filter_upwards with τ
    simpa [Real.norm_eq_abs] using (norm_add_le (F τ) (G τ))
  have hsum : (fun τ => ‖F τ‖ + ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ p + |τ| ^ q) := by
    simpa [Real.norm_eq_abs, norm_pow] using hF.add_add hG
  have hlast : (fun τ => |τ| ^ p + |τ| ^ q) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) := by
    have hp : (fun τ => |τ| ^ p) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_left p q)
    have hq : (fun τ => |τ| ^ q) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_right p q)
    exact hp.add hq
  have hbig : (fun τ => ‖F τ‖ + ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
    hsum.trans hlast
  have hres : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => |τ| ^ min p q) :=
    htri.trans hbig
  have hres' : (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖τ ^ min p q‖) := by
    simpa [Real.norm_eq_abs, norm_pow] using hres
  exact isBigO_norm_right.mp hres'

/-- Multiplication rule (order.tex:81): `F = O(τ^p)` and `G = O(τ^q)` imply
`F * G = O(τ^{p+q})`. -/
theorem orderCond_mul (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q)) := by
  have htri : (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => ‖F τ‖ * ‖G τ‖) := by
    refine Filter.Eventually.isBigO ?_
    filter_upwards with τ
    simpa [Real.norm_eq_abs] using (norm_mul_le (F τ) (G τ))
  have hbig : (fun τ => ‖F τ‖ * ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q)) :=
    (hF.mul hG).congr_right (fun τ => (pow_add τ p q).symm)
  exact htri.trans hbig

/-- A continuous function is `O(1)` at `0` (bounded in a neighbourhood of `0`). -/
lemma isBigO_norm_one_of_continuous {F : ℝ → 𝔸} (hF : Continuous F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) :=
  hF.norm.continuousAt.isBigO_one (F := ℝ)

/-- Left-multiplying an `O(τ^p)` function by an `O(1)` function stays `O(τ^p)`. -/
lemma orderCond_mul_left {F G : ℝ → 𝔸} (p : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) :
    (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  simpa using orderCond_mul F G 0 p hF hG

/-- `(-τ)^p = O(τ^p)` as `τ → 0`: the two functions have the same absolute value. -/
lemma neg_pow_isBigO (p : ℕ) :
    (fun τ : ℝ => (-τ) ^ p) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards with τ
  rw [one_mul]
  exact le_of_eq (by
    rw [Real.norm_eq_abs ((-τ) ^ p), Real.norm_eq_abs (τ ^ p), abs_pow (-τ) p, abs_pow τ p,
      abs_neg τ])

/-- `τ ↦ -τ` tends to `0` as `τ → 0`. -/
lemma tendsto_neg_nhds_zero : Filter.Tendsto (fun a : ℝ => -a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa using continuous_neg.tendsto (0 : ℝ)

end TrotterError
