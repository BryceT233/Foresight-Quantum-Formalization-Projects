/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Power-order asymptotics

Power comparison, arithmetic and boundedness near zero, and inverse-power decay of sequences.

## Main results

* `TrotterError.eventually_abs_le_one_nhds_zero`.
* `TrotterError.isBigO_abs_pow_abs_pow_of_le`.
* `TrotterError.orderCond_add`.
* `TrotterError.orderCond_mul`.
* `TrotterError.isBigO_norm_one_of_continuous`.
* `TrotterError.orderCond_mul_left`.
* `TrotterError.neg_pow_isBigO`.
* `TrotterError.tendsto_neg_nhds_zero`.
* `TrotterError.isBigO_comp_neg_pow_iff`.
* `FQFP.tendsto_inv_smul_of_isLittleO_sub`.
* `FQFP.isBigO_inv_nat_pow_of_remainder_le`.
* `FQFP.tendsto_nat_pow_smul_of_isBigO`.
-/

@[expose] public section

namespace TrotterError

open Asymptotics Finset
open scoped Topology BigOperators

/-- The absolute value is at most one in a neighborhood of zero. -/
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
theorem orderCond_add {𝔸 : Type*} [SeminormedAddCommGroup 𝔸] (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ + G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q) := by
  have hp : (fun τ : ℝ => τ ^ p) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q) := by
    simpa only [← Real.norm_eq_abs, ← norm_pow, isBigO_norm_left, isBigO_norm_right] using
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_left p q)
  have hq : (fun τ : ℝ => τ ^ q) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ min p q) := by
    simpa only [← Real.norm_eq_abs, ← norm_pow, isBigO_norm_left, isBigO_norm_right] using
      isBigO_abs_pow_abs_pow_of_le (Nat.min_le_right p q)
  exact isBigO_norm_left.mpr
    (((isBigO_norm_left.mp hF).trans hp).add ((isBigO_norm_left.mp hG).trans hq))

/-- Multiplication rule (order.tex:81): `F = O(τ^p)` and `G = O(τ^q)` imply
`F * G = O(τ^{p+q})`. -/
theorem orderCond_mul {𝔸 : Type*} [NormedRing 𝔸] (F G : ℝ → 𝔸) (p q : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ q)) :
    (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + q)) :=
  isBigO_norm_left.mpr
    (((isBigO_norm_left.mp hF).mul (isBigO_norm_left.mp hG)).congr_right
      (fun τ => (pow_add τ p q).symm))

/-- A continuous function is `O(1)` at `0` (bounded in a neighbourhood of `0`). -/
lemma isBigO_norm_one_of_continuous {𝔸 : Type*} [SeminormedAddCommGroup 𝔸]
    {F : ℝ → 𝔸} (hF : Continuous F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) :=
  hF.norm.continuousAt.isBigO_one (F := ℝ)

/-- Left-multiplying an `O(τ^p)` function by an `O(1)` function stays `O(τ^p)`. -/
lemma orderCond_mul_left {𝔸 : Type*} [NormedRing 𝔸] {F G : ℝ → 𝔸} (p : ℕ)
    (hF : (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)))
    (hG : (fun τ => ‖G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) :
    (fun τ => ‖F τ * G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  simpa using orderCond_mul F G 0 p hF hG

/-- `(-τ)^p = O(τ^p)` as `τ → 0`: the two functions have the same absolute value. -/
lemma neg_pow_isBigO (p : ℕ) :
    (fun τ : ℝ => (-τ) ^ p) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) :=
  isBigO_of_le _ fun τ => by simp [norm_pow]

/-- `τ ↦ -τ` tends to `0` as `τ → 0`. -/
lemma tendsto_neg_nhds_zero : Filter.Tendsto (fun a : ℝ => -a) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  simpa using continuous_neg.tendsto (0 : ℝ)

/-- Reversing the sign of the argument preserves a power-order bound at zero. -/
lemma isBigO_comp_neg_pow_iff {E : Type*} [Norm E] {f : ℝ → E} {p : ℕ} :
    (fun τ => f (-τ)) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      f =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  have reflect {g : ℝ → E} (hg : g =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p)) :
      (fun τ => g (-τ)) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) :=
    (hg.comp_tendsto tendsto_neg_nhds_zero).trans (neg_pow_isBigO p)
  exact ⟨fun h => by simpa only [neg_neg] using reflect h, reflect⟩

end TrotterError

namespace FQFP

open Asymptotics Filter
open scoped Topology

/-- If `F` has leading term `g • v` with an `o(g)` remainder, dividing by an
eventually nonzero `g` recovers the coefficient `v`. -/
theorem tendsto_inv_smul_of_isLittleO_sub {ι 𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {l : Filter ι}
    {F : ι → E} {g : ι → 𝕜} {v : E} (hg : ∀ᶠ i in l, g i ≠ 0)
    (hF : (fun i ↦ F i - g i • v) =o[l] g) :
    Tendsto (fun i ↦ (g i)⁻¹ • F i) l (𝓝 v) := by
  apply tendsto_sub_nhds_zero_iff.mp
  refine hF.tendsto_inv_smul_nhds_zero.congr' ?_
  filter_upwards [hg] with i hi
  simp [smul_sub, hi]

/-- An inverse-power expansion with a strictly higher-order remainder determines
the limit of the rescaled sequence. -/
theorem tendsto_nat_pow_smul_of_isBigO {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {F : ℕ → E} {v : E} {p q : ℕ} (hpq : p < q)
    (hF : (fun n : ℕ ↦ F n - ((n : ℝ)⁻¹) ^ p • v) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ q)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p • F n) atTop (𝓝 v) := by
  have hpow : (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ q) =o[atTop] (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ p) :=
    (isLittleO_pow_pow hpq).comp_tendsto tendsto_inv_atTop_nhds_zero_nat
  have hn : ∀ᶠ n : ℕ in atTop, ((n : ℝ)⁻¹) ^ p ≠ 0 :=
    (eventually_gt_atTop 0).mono fun n hn ↦
      pow_ne_zero p (inv_ne_zero (Nat.cast_ne_zero.mpr hn.ne'))
  simpa only [inv_pow, inv_inv] using
    tendsto_inv_smul_of_isLittleO_sub hn (hF.trans_isLittleO hpow)

/-- An eventual norm bound by a constant times `(t / n) ^ p` gives inverse-power decay
of order `p` along natural indices. -/
theorem isBigO_inv_nat_pow_of_remainder_le {E : Type*} [Norm E]
    {F : ℕ → E} {t B : ℝ} {p : ℕ}
    (hF : ∀ᶠ n : ℕ in atTop, ‖F n‖ ≤ (t / n) ^ p * B) :
    F =O[atTop] (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ p) := by
  apply IsBigO.of_bound (t ^ p * B)
  filter_upwards [hF] with n hn
  simpa only [norm_pow, norm_inv, Real.norm_natCast, div_eq_mul_inv, mul_pow,
    mul_right_comm] using hn

end FQFP
