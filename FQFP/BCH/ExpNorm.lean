/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.Calculus
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Norm bounds for the exponential

Norm bounds for `NormedSpace.exp` in a complete normed algebra, stated over the shared
scalar interface used throughout the Foresight Quantum formalizations: results that only
need the rational structure are proved over `ℚ`, while `𝕂` is carried along so callers may
instantiate at `ℝ`, `ℂ`, or a general `RCLike` field.

## Main results

* `hasSum_real_exp`, `hasSum_real_exp_tail`: the real exponential series and its tails.
* `norm_exp_sub_one_le`: `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1`.
* `norm_exp_sub_sum_le`: the parametrized remainder bound
  `‖exp x - ∑ i ∈ range n, (i!)⁻¹ • x^i‖ ≤ Real.exp ‖x‖ - ∑ i ∈ range n, ‖x‖^i / i!`.

## Implementation notes

Mathlib states these bounds for `ℂ` and `ℝ` only (`Complex.norm_exp_sub_one_le`,
`Complex.norm_exp_sub_sum_le_exp_norm_sub_sum`); the statements below hold in an arbitrary
complete normed algebra and are strictly more general.

**No overlap with `TrotterError`.** The two exponential bounds that `TrotterError` also has —
`norm_exp_term_le` and `norm_exp_le` (`TrotterError/Calculus.lean:508,516`) — are deliberately
*not* restated here: their statements are identical to `TrotterError`'s, so callers should use
`TrotterError.norm_exp_le` / `TrotterError.norm_exp_term_le`. Only the bounds `TrotterError`
does not have live in this file. (`Polyrith`-free proofs are used throughout.)

`[NormOneClass 𝔸]` is an explicit hypothesis of the bounds below, because the term estimate
goes through `norm_pow_le`. It is deliberately not a section variable, so that a caller needing
the weaker statement can see exactly which hypothesis to drop.

`norm_exp_sub_sum_le` replaces the eight hand-unrolled tail bounds of `Lean-BCH`
(`norm_exp_sub_one_le`, `norm_exp_sub_one_sub_le`, … up to order nine), each of which was
the same proof at a different `n`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP.BCH

noncomputable section

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-! ### The real exponential series and its tails -/

/-- The real exponential series sums to `Real.exp`. -/
lemma hasSum_real_exp (r : ℝ) :
    HasSum (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ * r ^ n) (Real.exp r) := by
  simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
    (exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) r)

/-- The tail of the real exponential series after the first `k` terms sums to `Real.exp r`
minus the corresponding partial sum. -/
lemma hasSum_real_exp_tail (r : ℝ) (k : ℕ) :
    HasSum (fun n : ℕ => (Nat.factorial (n + k) : ℝ)⁻¹ * r ^ (n + k))
      (Real.exp r - ∑ i ∈ range k, (Nat.factorial i : ℝ)⁻¹ * r ^ i) := by
  have h := hasSum_real_exp r
  have hsumm : Summable fun n : ℕ => (Nat.factorial (n + k) : ℝ)⁻¹ * r ^ (n + k) :=
    (summable_nat_add_iff k).mpr h.summable
  rw [hsumm.hasSum_iff]
  have hsplit := h.summable.sum_add_tsum_nat_add k
  rw [h.tsum_eq] at hsplit
  linarith

/-! ### Bounds for the exponential series

The term bound and `‖exp x‖ ≤ Real.exp ‖x‖` are **not** restated here: `TrotterError` already
has them, with identical statements, as `TrotterError.norm_exp_term_le` and
`TrotterError.norm_exp_le` (`TrotterError/Calculus.lean:508,516`). The bounds below are the
ones `TrotterError` does not have, so a caller wanting a tail estimate can reach for these
without duplicating the exponential bound itself. -/

/-- `‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1` in any complete normed algebra. -/
theorem norm_exp_sub_one_le [NormOneClass 𝔸] (x : 𝔸) :
    ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hsumm : Summable fun n : ℕ => (Nat.factorial n : ℚ)⁻¹ • x ^ n := expSeries_summable' x
  have h0 : (Nat.factorial 0 : ℚ)⁻¹ • x ^ 0 = (1 : 𝔸) := by simp
  have hsub : exp x - 1 = ∑' n : ℕ, (Nat.factorial (n + 1) : ℚ)⁻¹ • x ^ (n + 1) := by
    rw [exp_eq_tsum_rat]
    beta_reduce
    rw [hsumm.tsum_eq_zero_add, h0, add_sub_cancel_left]
  rw [hsub]
  refine tsum_of_norm_bounded ?_ fun n => TrotterError.norm_exp_term_le x (n + 1)
  convert hasSum_real_exp_tail ‖x‖ 1 using 2
  · rw [inv_mul_eq_div]
  · simp

/-- The parametrized exponential remainder bound: the tail of the exponential series after
the first `n` terms is bounded by the corresponding tail of the real exponential series. -/
theorem norm_exp_sub_sum_le [NormOneClass 𝔸] (x : 𝔸) (n : ℕ) :
    ‖exp x - ∑ i ∈ range n, (Nat.factorial i : ℚ)⁻¹ • x ^ i‖
      ≤ Real.exp ‖x‖ - ∑ i ∈ range n, ‖x‖ ^ i / Nat.factorial i := by
  have hsumm : Summable fun i : ℕ => (Nat.factorial i : ℚ)⁻¹ • x ^ i := expSeries_summable' x
  have hsub : exp x - ∑ i ∈ range n, (Nat.factorial i : ℚ)⁻¹ • x ^ i
      = ∑' k : ℕ, (Nat.factorial (k + n) : ℚ)⁻¹ • x ^ (k + n) := by
    rw [exp_eq_tsum_rat]
    beta_reduce
    rw [← hsumm.sum_add_tsum_nat_add n]
    abel
  rw [hsub]
  refine tsum_of_norm_bounded ?_ fun k => TrotterError.norm_exp_term_le x (k + n)
  have hfin : ∑ i ∈ range n, ‖x‖ ^ i / Nat.factorial i
      = ∑ i ∈ range n, (Nat.factorial i : ℝ)⁻¹ * ‖x‖ ^ i :=
    sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  convert hasSum_real_exp_tail ‖x‖ n using 2
  rw [inv_mul_eq_div]

/-! ### Taylor remainders of the real exponential

The third-order remainder of `Real.exp` on `[0, 1)`, in the two forms the BCH estimates consume:
a `1/(1 - r)`-shaped one valid on `[0, 1)`, and the polynomial `r³` one valid on `[0, 5/6)` — the
latter is the shape appearing in the cubic and higher-order BCH bounds, which is why it carries the
numerically convenient threshold `5/6` rather than the sharp `1`. Both come from the termwise
bound `1/k! ≤ 1/6` for `k ≥ 3`.

These are statements about `Real.exp` alone, so they carry no algebra variables. -/

/-- **Third-order Taylor remainder of `Real.exp`, `1/(1 - r)` form**:
`exp r - 1 - r - r²/2 ≤ r³ / (6 (1 - r))` for `0 ≤ r < 1`. -/
theorem real_exp_third_order_le_div {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 / (6 * (1 - r)) := by
  have h3 : (∑ i ∈ Finset.range 3, (Nat.factorial i : ℝ)⁻¹ * r ^ i) = 1 + r + r ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
    ring
  have hval : HasSum (fun n : ℕ => (Nat.factorial (n + 3) : ℝ)⁻¹ * r ^ (n + 3))
      (Real.exp r - 1 - r - r ^ 2 / 2) := by
    have h := hasSum_real_exp_tail r 3
    rw [h3] at h
    convert h using 1
    ring
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 3) * (6 : ℝ)⁻¹)
      (r ^ 3 * (1 - r)⁻¹ * (6 : ℝ)⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one hr hr1).mul_left (r ^ 3)
    rw [show (fun n : ℕ => r ^ 3 * r ^ n) = (fun n : ℕ => r ^ (n + 3)) from
      funext fun n => by ring] at hg
    exact hg.mul_right (6 : ℝ)⁻¹
  have hterm : ∀ n : ℕ,
      (Nat.factorial (n + 3) : ℝ)⁻¹ * r ^ (n + 3) ≤ r ^ (n + 3) * (6 : ℝ)⁻¹ := by
    intro n
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr _)
    rw [inv_le_inv₀ (by positivity) (by norm_num : (0 : ℝ) < 6)]
    exact_mod_cast Nat.factorial_le (by lia : 3 ≤ n + 3)
  have hsumm : Summable fun n : ℕ => (Nat.factorial (n + 3) : ℝ)⁻¹ * r ^ (n + 3) :=
    (summable_nat_add_iff 3).mpr (hasSum_real_exp r).summable
  calc Real.exp r - 1 - r - r ^ 2 / 2
      = ∑' n : ℕ, (Nat.factorial (n + 3) : ℝ)⁻¹ * r ^ (n + 3) := hval.tsum_eq.symm
    _ ≤ ∑' n : ℕ, r ^ (n + 3) * (6 : ℝ)⁻¹ := hsumm.tsum_le_tsum hterm hgeom.summable
    _ = r ^ 3 * (1 - r)⁻¹ * (6 : ℝ)⁻¹ := hgeom.tsum_eq
    _ = r ^ 3 / (6 * (1 - r)) := by rw [div_eq_mul_inv, mul_inv_rev]; ring

/-- **Third-order Taylor remainder of `Real.exp`, cubic form**:
`exp r - 1 - r - r²/2 ≤ r³` for `0 ≤ r < 5/6`. -/
theorem real_exp_third_order_le_cube {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 5 / 6) :
    Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 := by
  have hr1' : r < 1 := by linarith
  calc Real.exp r - 1 - r - r ^ 2 / 2 ≤ r ^ 3 / (6 * (1 - r)) :=
        real_exp_third_order_le_div hr hr1'
    _ ≤ r ^ 3 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * (1 - r))]
        nlinarith [sq_nonneg r, pow_nonneg hr 3]

/-! ### Taylor remainders in a normed algebra

The low-order cases of `norm_exp_sub_sum_le` written in the form every caller uses: the remainder
after subtracting `1 + x` (resp. `1 + x + x²/2`). These are the second- and third-order inputs of
the BCH estimates in `BCHElement.lean` and `BCHCommutator.lean`. -/

section ExpRemainder

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
  [NormOneClass 𝔸]

/-- **Second-order Taylor remainder of `exp`**:
`‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖`. -/
theorem norm_exp_sub_one_sub_id_le (x : 𝔸) :
    ‖exp x - 1 - x‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ := by
  have h := norm_exp_sub_sum_le x 2
  have hsum : (∑ i ∈ Finset.range 2, (Nat.factorial i : ℚ)⁻¹ • x ^ i) = 1 + x := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hsum' : (∑ i ∈ Finset.range 2, ‖x‖ ^ i / (Nat.factorial i : ℝ)) = 1 + ‖x‖ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum, hsum'] at h
  rw [show exp x - (1 + x) = exp x - 1 - x by abel] at h
  refine h.trans_eq ?_
  ring

/-- **Third-order Taylor remainder of `exp`**:
`‖exp x - 1 - x - x²/2‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖²/2`. -/
theorem norm_exp_sub_one_sub_id_sub_sq_le (x : 𝔸) :
    ‖exp x - 1 - x - (2 : ℚ)⁻¹ • x ^ 2‖ ≤ Real.exp ‖x‖ - 1 - ‖x‖ - ‖x‖ ^ 2 / 2 := by
  have h := norm_exp_sub_sum_le x 3
  have hsum : (∑ i ∈ Finset.range 3, (Nat.factorial i : ℚ)⁻¹ • x ^ i)
      = 1 + x + (2 : ℚ)⁻¹ • x ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  have hsum' : (∑ i ∈ Finset.range 3, ‖x‖ ^ i / (Nat.factorial i : ℝ))
      = 1 + ‖x‖ + ‖x‖ ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum, hsum'] at h
  rw [show exp x - (1 + x + (2 : ℚ)⁻¹ • x ^ 2) = exp x - 1 - x - (2 : ℚ)⁻¹ • x ^ 2 by
    abel] at h
  refine h.trans_eq ?_
  ring

end ExpRemainder

end

end FQFP.BCH
