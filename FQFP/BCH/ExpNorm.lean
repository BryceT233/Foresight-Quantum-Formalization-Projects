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

end

end FQFP.BCH
