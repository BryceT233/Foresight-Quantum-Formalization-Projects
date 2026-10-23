/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds in a normed algebra

Bounds for `NormedSpace.exp`, its finite Taylor remainders, and products of exponentials.
These estimates form a common analytic foundation for BCH and product-formula errors.

## Main results

* `norm_exp_le`: the exponential norm is bounded by the real exponential of the norm.
* `norm_exp_sub_sum_le`: the Taylor remainder is bounded by the scalar exponential tail.
* `norm_exp_mul_exp_sub_one_le`: a product estimate independent of convergence thresholds.
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- Each term of the exponential series is bounded by `‖a‖^n / n!`. -/
lemma norm_exp_term_le [NormOneClass 𝔸] (a : 𝔸) (n : ℕ) :
    ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ ≤ ‖a‖ ^ n / Nat.factorial n := by
  rw [norm_smul, norm_inv, ← Rat.norm_cast_real, Real.norm_eq_abs, inv_mul_eq_div]
  norm_cast; gcongr
  exact norm_pow_le ..

/-- The exponential norm is bounded by the real exponential of the norm. -/
lemma norm_exp_le [NormOneClass 𝔸] (a : 𝔸) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [NormedSpace.exp_eq_tsum ℚ, Real.exp_eq_exp_ℝ,
    ← (NormedSpace.expSeries_div_hasSum_exp _).tsum_eq]
  have hnsumm : Summable fun n ↦ ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ :=
    (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_exp_term_le a)
  calc
    _ ≤ ∑' n, ‖(Nat.factorial n : ℚ)⁻¹ • a ^ n‖ := norm_tsum_le_tsum_norm hnsumm
    _ ≤ ∑' n, ‖a‖ ^ n / Nat.factorial n :=
      hnsumm.tsum_le_tsum (norm_exp_term_le a) (Real.summable_pow_div_factorial ‖a‖)

variable [CompleteSpace 𝔸]

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

/-! ### Bounds for the exponential series -/

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
  refine tsum_of_norm_bounded ?_ fun n => norm_exp_term_le x (n + 1)
  convert hasSum_real_exp_tail ‖x‖ 1 using 2
  · rw [inv_mul_eq_div]
  · simp

/-- The distance from a product of exponentials to `1` is bounded by the scalar exponential
at the sum of the norms, minus `1`. -/
theorem norm_exp_mul_exp_sub_one_le [NormOneClass 𝔸] (a b : 𝔸) :
    ‖exp a * exp b - 1‖ ≤ Real.exp (‖a‖ + ‖b‖) - 1 := by
  rw [show exp a * exp b - 1 = (exp a - 1) * exp b + (exp b - 1) by
    noncomm_ring]
  calc
    _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
    _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) :=
      add_le_add
        (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_le b) (norm_nonneg _)
          (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg a))))
        (norm_exp_sub_one_le b)
    _ = Real.exp (‖a‖ + ‖b‖) - 1 := by rw [Real.exp_add]; ring

/-- **The BCH smallness condition**: `‖exp a * exp b - 1‖ < 1` when `‖a‖ + ‖b‖ < log 2`, which is
what puts `exp a * exp b` inside the ball where the log series converges. -/
theorem norm_exp_mul_exp_sub_one_lt_one [NormOneClass 𝔸] (a b : 𝔸)
    (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖exp a * exp b - 1‖ < 1 := by
  refine (norm_exp_mul_exp_sub_one_le a b).trans_lt ?_
  have h := Real.exp_strictMono hab
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- **The BCH smallness condition, one-sided form**: `‖exp a - 1‖ < 1` when `‖a‖ < log 2`. -/
theorem norm_exp_sub_one_lt_one [NormOneClass 𝔸] (a : 𝔸) (ha : ‖a‖ < Real.log 2) :
    ‖exp a - 1‖ < 1 := by
  have h := norm_exp_mul_exp_sub_one_lt_one a (0 : 𝔸) (by simpa using ha)
  simpa [exp_zero] using h

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
  refine tsum_of_norm_bounded ?_ fun k => norm_exp_term_le x (k + n)
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

variable [NormOneClass 𝔸]

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

/-- The error after the linear part of a product of two exponentials is bounded by the
quadratic scalar exponential remainder at the sum of the norms. -/
theorem norm_exp_mul_exp_sub_one_sub_add_le (a b : 𝔸) :
    ‖exp a * exp b - 1 - (a + b)‖ ≤
      Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by
  rw [show exp a * exp b - 1 - (a + b) =
    (exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b) by
      noncomm_ring]
  calc
    _ ≤ ‖exp a - 1‖ * ‖exp b - 1‖ + ‖exp a - 1 - a‖ + ‖exp b - 1 - b‖ := by
      grw [norm_add_le, norm_add_le, norm_mul_le]
    _ ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
        (Real.exp ‖a‖ - 1 - ‖a‖) + (Real.exp ‖b‖ - 1 - ‖b‖) :=
      add_le_add (add_le_add
        (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_sub_one_le b) (norm_nonneg _)
          (sub_nonneg.mpr (Real.one_le_exp (norm_nonneg a))))
        (norm_exp_sub_one_sub_id_le a)) (norm_exp_sub_one_sub_id_le b)
    _ = Real.exp (‖a‖ + ‖b‖) - 1 - (‖a‖ + ‖b‖) := by rw [Real.exp_add]; ring

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

end FQFP
