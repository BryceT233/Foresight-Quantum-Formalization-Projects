/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

module

public import FQFP.BCH.BCHElement
public import Mathlib.Algebra.Lie.OfAssociative

import FQFP.BCH.RealScalar

/-!
# The commutator expansion of the BCH element

How far `bch a b` is from `a + b`, and what the leading correction is. Two estimates, both for
`s = ‖a‖ + ‖b‖ < log 2` (the radius of convergence of the BCH series, where both diverge):

* `norm_bch_sub_add_le` — **quadratic**: `‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)`, i.e. the linear
  part of `bch a b` is `a + b`.
* `norm_bch_sub_add_sub_bracket_le` — **cubic (commutator extraction)**:
  `‖bch a b - (a + b) - ½(a * b - b * a)‖ ≤ 10 s³ / (2 - eˢ)`, which identifies the leading
  non-commutative correction as the Lie bracket `½[a, b]`. `lie_eq_commutator` records
  `⁅a, b⁆ = a * b - b * a` and `norm_bch_sub_add_sub_lie_le` is the same bound in `⁅·,·⁆` notation.

The symmetric (Strang) refinement of the cubic bound — where `½[a, b]` cancels — is in
`BCHSymmetric.lean`.

## Provenance

Ported from `Lean-BCH/BCH/Basic.lean` (`norm_bch_sub_add_le`,
`norm_bch_sub_add_sub_bracket_le`, `lie_eq_commutator`, `norm_bch_sub_add_sub_lie_le`). The
source's cubic bound carried `set_option maxHeartbeats 16000000`, which this version does not need:
the real arithmetic is isolated in `bch_cubic_real_core`, and each estimate there is an explicit
chain of order-theoretic steps rather than one large `linarith`.
See `artifacts/bch-port.md` §5.2 for the diagnosis and the measured heartbeat counts.

The source's `norm_bch_sub_add_le'` is deliberately not ported: it is the quadratic bound verbatim
under a second name.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open NormedSpace TrotterError

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
/-! ### The quadratic bound for `bch`

`‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)` where `s = ‖a‖ + ‖b‖`. The proof splits
`bch a b - (a + b)` into the logarithm's remainder at `exp a * exp b - 1` and the exponential's own
remainder `exp a * exp b - 1 - (a + b)`, bounds each, and uses `eˢ ≤ 1 + s + s²` (for `s < 1`,
where `1 + s ≤ eˢ < 2`) to absorb the result into `3 s² / (2 - eˢ)`. The bound diverges at
`s = log 2`, the radius of convergence. -/

/-- **The quadratic BCH bound**: `‖bch a b - (a + b)‖ ≤ 3 s² / (2 - eˢ)` for
`s = ‖a‖ + ‖b‖ < log 2`, with the leading non-commutative correction `⁅a, b⁆/2` left inside the
remainder. -/
theorem norm_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b)‖ ≤ 3 * (‖a‖ + ‖b‖) ^ 2 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  set y : 𝔸 := exp a * exp b - 1 with hy_def
  set s : ℝ := ‖a‖ + ‖b‖ with hs_def
  have hs_lt : s < Real.log 2 := by rw [hs_def]; exact hab
  have hs_nn : 0 ≤ s := by rw [hs_def]; positivity
  have hE_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hs_lt
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one a b hab
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hfac : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hfac]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) :=
          add_le_add
            (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_le b) (norm_nonneg _)
              (by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]))
            (norm_exp_sub_one_le b)
      _ = Real.exp s - 1 := by rw [hs_def, Real.exp_add]; ring
  -- part 1: the logarithm's remainder at `y`
  have hpart1 : ‖log (1 + y) - y‖ ≤ (Real.exp s - 1) ^ 2 / (2 - Real.exp s) := by
    have h1pos : 0 < 1 - ‖y‖ := by linarith
    have h2pos : 0 < 2 - Real.exp s := hdenom
    calc ‖log (1 + y) - y‖ ≤ ‖y‖ ^ 2 * (1 - ‖y‖)⁻¹ := norm_log_one_add_sub_le y hy_lt
      _ ≤ (Real.exp s - 1) ^ 2 * (2 - Real.exp s)⁻¹ := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le 2) ?_
            (inv_nonneg.mpr h1pos.le) (sq_nonneg _)
          rw [inv_le_inv₀ h1pos h2pos]
          linarith
      _ = (Real.exp s - 1) ^ 2 / (2 - Real.exp s) := by rw [div_eq_mul_inv]
  -- part 2: the exponential's remainder
  have hpart2 : ‖y - (a + b)‖ ≤ Real.exp s - 1 - s := by
    have hident : y - (a + b) =
        (exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b) := by
      rw [hy_def]; noncomm_ring
    rw [hident]
    calc ‖(exp a - 1) * (exp b - 1) + (exp a - 1 - a) + (exp b - 1 - b)‖
        ≤ (Real.exp ‖a‖ - 1) * (Real.exp ‖b‖ - 1) +
          (Real.exp ‖a‖ - 1 - ‖a‖) + (Real.exp ‖b‖ - 1 - ‖b‖) := by
          refine ((norm_add_le _ _).trans ?_).trans
            (add_le_add le_rfl (norm_exp_sub_one_sub_id_le b))
          refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
          refine add_le_add (add_le_add ?_ (norm_exp_sub_one_sub_id_le a)) le_rfl
          exact (norm_mul_le _ _).trans (mul_le_mul (norm_exp_sub_one_le a)
            (norm_exp_sub_one_le b) (norm_nonneg _)
            (by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]))
      _ = Real.exp s - 1 - s := by rw [hs_def, Real.exp_add]; ring
  have hY : (1 : 𝔸) + y = exp a * exp b := by rw [hy_def]; abel
  have hbch : bch a b = log (1 + y) := by rw [bch, ← hY]
  rw [show bch a b - (a + b) = (log (1 + y) - y) + (y - (a + b)) by rw [hbch]; abel]
  refine (norm_add_le _ _).trans ((add_le_add hpart1 hpart2).trans ?_)
  rw [div_add' _ _ _ (ne_of_gt hdenom), div_le_div_iff_of_pos_right hdenom]
  set E := Real.exp s with hE_def
  have hs_lt_one : s < 1 := by linarith [Real.add_one_le_exp s]
  have hE_taylor : E - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (show ‖s‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.add_one_le_exp s]),
      Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hE_le : E ≤ 1 + s + s ^ 2 := by linarith
  nlinarith [sq_nonneg s, mul_self_nonneg (s * s),
    show s ^ 3 ≤ s ^ 2 from by
      calc s ^ 3 = s ^ 2 * s := by ring
        _ ≤ s ^ 2 * 1 := by nlinarith [sq_nonneg s]
        _ = s ^ 2 := by ring]

/-! ### The cubic bound: commutator extraction

`‖bch a b - (a + b) - ½(a * b - b * a)‖ ≤ 10 s³ / (2 - eˢ)` for `s = ‖a‖ + ‖b‖ < log 2`. This
identifies the leading non-commutative correction to `bch` as the Lie bracket `½[a, b]`, leaving a
cubic remainder.

The proof decomposes

`bch a b - (a + b) - ½(ab - ba)`

into the logarithm's own cubic remainder at `y = exp a * exp b - 1` — bounded by
`norm_log_one_add_sub_add_sq_le`, with the geometric factor `(1 - ‖y‖)⁻¹` replaced by
`(2 - eˢ)⁻¹` — and the exponential's cubic remainder
`y - (a + b) - ½(ab - ba) - ½y²`. The algebraic identity `bch_cubic_pieceB_eq` rewrites the latter
as `½ • bchCubicW`, whose norm is then estimated by the triangle inequality against the second-
and third-order exponential remainders.

The real-arithmetic bookkeeping is isolated in `bch_cubic_real_core`, so that each inequality is
discharged by its own small `nlinarith` instead of one monolithic call — the source's version of
this proof needed a `maxHeartbeats` bump, which this split removes. -/

section CubicBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **The real-arithmetic core of the cubic BCH bound.** For `s = α + β` with `α, β ≥ 0` and
`s < 5/6` (hence `eˢ < 2`), the cubic exponential remainder `(eˢ - 1)³` plus the exponential-
remainder block times `2 - eˢ` is at most `10 s³`.

The two ingredients are the third-order Taylor bounds `e^t - 1 - t - t²/2 ≤ t³` (`t = α, β, s`) and
`e^s - 1 ≤ s + s²`; the bookkeeping is split into the individual `hRB*` estimates, each a scoped
`linarith only [...]` so that it never has to scan the whole (product-heavy) context. -/
private lemma bch_cubic_real_core {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : α + β = s)
    (hs1 : s < 1) (hs56 : s < 5 / 6) (hexp_lt : Real.exp s < 2) :
    (Real.exp s - 1) ^ 3 +
        ((Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
          (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
          s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2) * (2 - Real.exp s)
      ≤ 10 * s ^ 3 := by
  have hs_nn : 0 ≤ s := by linarith only [hα, hβ, hs]
  have hα_le : α ≤ s := by linarith only [hβ, hs]
  have hβ_le : β ≤ s := by linarith only [hα, hs]
  have hα56 : α < 5 / 6 := lt_of_le_of_lt hα_le hs56
  have hβ56 : β < 5 / 6 := lt_of_le_of_lt hβ_le hs56
  have h2E_nn : 0 ≤ 2 - Real.exp s := by linarith only [hexp_lt]
  have h2E_le : 2 - Real.exp s ≤ 1 := by linarith only [Real.add_one_le_exp s, hs_nn]
  -- the Taylor remainders of the real exponential
  have hEa3 : Real.exp α - 1 - α - α ^ 2 / 2 ≤ α ^ 3 := real_exp_third_order_le_cube hα hα56
  have hEb3 : Real.exp β - 1 - β - β ^ 2 / 2 ≤ β ^ 3 := real_exp_third_order_le_cube hβ hβ56
  have hEa_nn : 0 ≤ Real.exp α - 1 - α - α ^ 2 / 2 := by
    linarith only [Real.quadratic_le_exp_of_nonneg hα]
  have hEb_nn : 0 ≤ Real.exp β - 1 - β - β ^ 2 / 2 := by
    linarith only [Real.quadratic_le_exp_of_nonneg hβ]
  have hDa_nn : 0 ≤ Real.exp α - 1 - α := by
    linarith only [Real.quadratic_le_exp_of_nonneg hα, sq_nonneg α]
  have hDb_nn : 0 ≤ Real.exp β - 1 - β := by
    linarith only [Real.quadratic_le_exp_of_nonneg hβ, sq_nonneg β]
  have hDa2 : Real.exp α - 1 - α ≤ α ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (show ‖α‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hα]; linarith only [hα56])
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith only [Real.add_one_le_exp α]),
      Real.norm_eq_abs, abs_of_nonneg hα] at h
  have hDb2 : Real.exp β - 1 - β ≤ β ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (show ‖β‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hβ]; linarith only [hβ56])
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith only [Real.add_one_le_exp β]),
      Real.norm_eq_abs, abs_of_nonneg hβ] at h
  have hEs2 : Real.exp s - 1 - s ≤ s ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (show ‖s‖ ≤ 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hs_nn]; linarith only [hs1])
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith only [Real.add_one_le_exp s]),
      Real.norm_eq_abs, abs_of_nonneg hs_nn] at h
  have hEs_nn : 0 ≤ Real.exp s - 1 - s := by
    linarith only [Real.quadratic_le_exp_of_nonneg hs_nn, sq_nonneg s]
  -- `(1 + s)³ ≤ 13/2` for `s < 5/6`
  have h1s3 : (1 + s) ^ 3 ≤ 13 / 2 := by
    have hmono : (1 + s) ^ 3 ≤ (1 + 5 / 6 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hs_nn]) (by linarith only [hs56]) 3
    have hval : ((1 + 5 / 6 : ℝ)) ^ 3 ≤ 13 / 2 := by norm_num
    linarith only [hmono, hval]
  have hE1_le : Real.exp s - 1 ≤ s + s ^ 2 := by linarith only [hEs2]
  have hE13_bound : (Real.exp s - 1) ^ 3 ≤ 13 / 2 * s ^ 3 := by
    calc (Real.exp s - 1) ^ 3 ≤ (s + s ^ 2) ^ 3 :=
          pow_le_pow_left₀ (by linarith only [Real.add_one_le_exp s, hs_nn]) hE1_le 3
      _ = s ^ 3 * (1 + s) ^ 3 := by ring
      _ ≤ s ^ 3 * (13 / 2) := mul_le_mul_of_nonneg_left h1s3 (pow_nonneg hs_nn 3)
      _ = 13 / 2 * s ^ 3 := by ring
  -- each block of the exponential remainder, times `2 - eˢ ≤ 1`
  have hRB1 : (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - Real.exp s) ≤ α ^ 3 :=
    calc _ ≤ (Real.exp α - 1 - α - α ^ 2 / 2) * 1 :=
          mul_le_mul_of_nonneg_left h2E_le hEa_nn
      _ = _ := mul_one _
      _ ≤ α ^ 3 := hEa3
  have hRB2 : (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - Real.exp s) ≤ β ^ 3 :=
    calc _ ≤ (Real.exp β - 1 - β - β ^ 2 / 2) * 1 :=
          mul_le_mul_of_nonneg_left h2E_le hEb_nn
      _ = _ := mul_one _
      _ ≤ β ^ 3 := hEb3
  have hRB3 : α * (Real.exp β - 1 - β) * (2 - Real.exp s) ≤ α * β ^ 2 :=
    calc α * (Real.exp β - 1 - β) * (2 - Real.exp s) ≤ α * (Real.exp β - 1 - β) * 1 :=
          mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hα hDb_nn)
      _ = α * (Real.exp β - 1 - β) := mul_one _
      _ ≤ α * β ^ 2 := mul_le_mul_of_nonneg_left hDb2 hα
  have hRB4 : (Real.exp α - 1 - α) * β * (2 - Real.exp s) ≤ α ^ 2 * β :=
    calc (Real.exp α - 1 - α) * β * (2 - Real.exp s) ≤ (Real.exp α - 1 - α) * β * 1 :=
          mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hDa_nn hβ)
      _ = (Real.exp α - 1 - α) * β := mul_one _
      _ ≤ α ^ 2 * β := mul_le_mul_of_nonneg_right hDa2 hβ
  have hRB5 : (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * (2 - Real.exp s) ≤ α ^ 2 * β ^ 2 :=
    calc (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * (2 - Real.exp s)
        ≤ (Real.exp α - 1 - α) * (Real.exp β - 1 - β) * 1 :=
          mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hDa_nn hDb_nn)
      _ = (Real.exp α - 1 - α) * (Real.exp β - 1 - β) := mul_one _
      _ ≤ α ^ 2 * β ^ 2 := mul_le_mul hDa2 hDb2 hDb_nn (by positivity)
  have hRB6 : s * (Real.exp s - 1 - s) * (2 - Real.exp s) ≤ s ^ 3 :=
    calc s * (Real.exp s - 1 - s) * (2 - Real.exp s) ≤ s * (Real.exp s - 1 - s) * 1 :=
          mul_le_mul_of_nonneg_left h2E_le (mul_nonneg hs_nn hEs_nn)
      _ = s * (Real.exp s - 1 - s) := mul_one _
      _ ≤ s * s ^ 2 := mul_le_mul_of_nonneg_left hEs2 hs_nn
      _ = s ^ 3 := by ring
  have hRB7 : (Real.exp s - 1 - s) ^ 2 / 2 * (2 - Real.exp s) ≤ s ^ 3 / 2 :=
    calc (Real.exp s - 1 - s) ^ 2 / 2 * (2 - Real.exp s) ≤ (Real.exp s - 1 - s) ^ 2 / 2 * 1 :=
          mul_le_mul_of_nonneg_left h2E_le (by positivity)
      _ = (Real.exp s - 1 - s) ^ 2 / 2 := mul_one _
      _ ≤ s ^ 4 / 2 := by
          have h : (Real.exp s - 1 - s) ^ 2 ≤ s ^ 4 := by
            have h2 := pow_le_pow_left₀ hEs_nn hEs2 2
            rwa [show (s ^ 2) ^ 2 = s ^ 4 from by ring] at h2
          linarith only [h]
      _ ≤ s ^ 3 / 2 := by
          have h4 : s ^ 4 ≤ s ^ 3 :=
            calc s ^ 4 = s ^ 3 * s := by ring
              _ ≤ s ^ 3 * 1 :=
                  mul_le_mul_of_nonneg_left (by linarith only [hs1]) (pow_nonneg hs_nn 3)
              _ = s ^ 3 := mul_one _
          linarith only [h4]
  -- the composite estimates
  have ht_nn : 0 ≤ α * β := mul_nonneg hα hβ
  have ht_le : α * β ≤ s ^ 2 / 4 := by
    have h : 4 * (α * β) ≤ s ^ 2 := by
      calc 4 * (α * β) = 4 * α * β := by ring
        _ ≤ (α + β) ^ 2 := four_mul_le_sq_add α β
        _ = s ^ 2 := by rw [← hs]
    linarith only [h]
  have ht_sq : (α * β) * (α * β) ≤ s ^ 4 / 16 := by
    have hsq : (α * β) * (α * β) ≤ (s ^ 2 / 4) * (s ^ 2 / 4) :=
      mul_le_mul ht_le ht_le ht_nn (by positivity)
    have heq : (s ^ 2 / 4) * (s ^ 2 / 4) = s ^ 4 / 16 := by ring
    rwa [heq] at hsq
  have hα3β3 : α ^ 3 + β ^ 3 ≤ s ^ 3 := by
    have h : s ^ 3 = α ^ 3 + β ^ 3 + (3 * α ^ 2 * β + 3 * α * β ^ 2) := by rw [← hs]; ring
    have hnn : 0 ≤ 3 * α ^ 2 * β + 3 * α * β ^ 2 := by positivity
    linarith only [h, hnn]
  have hcross_s3 : α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 ≤ s ^ 3 := by
    have h1 : α * β ^ 2 + α ^ 2 * β = (α * β) * s := by rw [← hs]; ring
    have h2 : α ^ 2 * β ^ 2 = (α * β) * (α * β) := by ring
    calc α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2
        = (α * β) * s + (α * β) * (α * β) := by rw [h1, h2]
      _ ≤ (s ^ 2 / 4) * s + s ^ 4 / 16 :=
          add_le_add (mul_le_mul_of_nonneg_right ht_le hs_nn) ht_sq
      _ = s ^ 3 * (1 / 4) + s ^ 3 * (s / 16) := by ring
      _ = s ^ 3 * (1 / 4 + s / 16) := by ring
      _ ≤ s ^ 3 * (1 / 4 + 1 / 16) :=
          mul_le_mul_of_nonneg_left (by linarith only [hs1]) (pow_nonneg hs_nn 3)
      _ ≤ s ^ 3 * 1 := mul_le_mul_of_nonneg_left (by norm_num) (pow_nonneg hs_nn 3)
      _ = s ^ 3 := mul_one _
  have h_sum1 : (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - Real.exp s) +
      (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - Real.exp s) ≤ s ^ 3 :=
    (add_le_add hRB1 hRB2).trans hα3β3
  have hcross_le : (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
      (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - Real.exp s) ≤
      α * β ^ 2 + α ^ 2 * β + α ^ 2 * β ^ 2 := by
    rw [add_mul, add_mul]
    exact add_le_add (add_le_add hRB3 hRB4) hRB5
  have h_sum2 : (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
      (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - Real.exp s) ≤ s ^ 3 :=
    hcross_le.trans hcross_s3
  -- distribute the product and add up: `13/2 + 1 + 1 + 1 + 1/2 = 10`
  have hexpand : ((Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
        (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
          (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
        s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2) * (2 - Real.exp s) =
      (Real.exp α - 1 - α - α ^ 2 / 2) * (2 - Real.exp s) +
      (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - Real.exp s) +
      (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
        (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - Real.exp s) +
      s * (Real.exp s - 1 - s) * (2 - Real.exp s) +
      (Real.exp s - 1 - s) ^ 2 / 2 * (2 - Real.exp s) := by ring
  rw [hexpand]
  calc (Real.exp s - 1) ^ 3 +
        ((Real.exp α - 1 - α - α ^ 2 / 2) * (2 - Real.exp s) +
          (Real.exp β - 1 - β - β ^ 2 / 2) * (2 - Real.exp s) +
          (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) * (2 - Real.exp s) +
          s * (Real.exp s - 1 - s) * (2 - Real.exp s) +
          (Real.exp s - 1 - s) ^ 2 / 2 * (2 - Real.exp s))
      ≤ 13 / 2 * s ^ 3 + (s ^ 3 + s ^ 3 + s ^ 3 + s ^ 3 / 2) :=
        add_le_add hE13_bound (by linarith only [h_sum1, h_sum2, hRB6, hRB7])
    _ = 10 * s ^ 3 := by ring

/-- **Commutator extraction (H1)**: `bch a b` agrees with `a + b + ½(a * b - b * a)` up to
`10 s³ / (2 - eˢ)`, so the leading non-commutative correction to `bch` is the Lie bracket
`½[a, b]`. -/
theorem norm_bch_sub_add_sub_bracket_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a)‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸
  set y : 𝔸 := exp a * exp b - 1 with hy_def
  set s : ℝ := ‖a‖ + ‖b‖ with hs_def
  set α : ℝ := ‖a‖ with hα_def
  set β : ℝ := ‖b‖ with hβ_def
  have hαβ : α + β = s := by rw [hα_def, hβ_def, hs_def]
  have hα_nn : 0 ≤ α := by rw [hα_def]; exact norm_nonneg a
  have hβ_nn : 0 ≤ β := by rw [hβ_def]; exact norm_nonneg b
  have hs_nn : 0 ≤ s := by linarith
  have hs_lt : s < Real.log 2 := by rw [hs_def]; exact hab
  have hs56 : s < 5 / 6 := by
    calc s < Real.log 2 := hs_lt
      _ ≤ 5 / 6 := by
          rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
          calc (2 : ℝ) ≤ 1 + 5 / 6 + (5 / 6) ^ 2 / 2 := by norm_num
            _ ≤ Real.exp (5 / 6) := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hs1 : s < 1 := by linarith
  have hexp_lt : Real.exp s < 2 := by
    calc Real.exp s < Real.exp (Real.log 2) := Real.exp_strictMono hs_lt
      _ = 2 := Real.exp_log (by norm_num)
  have hdenom : 0 < 2 - Real.exp s := by linarith
  have hy_lt : ‖y‖ < 1 := norm_exp_mul_exp_sub_one_lt_one a b hab
  set D₁ : 𝔸 := exp a - 1 - a with hD₁_def
  set D₂ : 𝔸 := exp b - 1 - b with hD₂_def
  set E₁ : 𝔸 := exp a - 1 - a - (2 : ℚ)⁻¹ • a ^ 2 with hE₁_def
  set E₂ : 𝔸 := exp b - 1 - b - (2 : ℚ)⁻¹ • b ^ 2 with hE₂_def
  set P : 𝔸 := y - (a + b) with hP_def
  set W : 𝔸 := (2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂) -
    (a + b) * P - P * (a + b) - P ^ 2 with hW_def
  have hE₁_le : ‖E₁‖ ≤ Real.exp α - 1 - α - α ^ 2 / 2 := by
    rw [hE₁_def, hα_def]; exact norm_exp_sub_one_sub_id_sub_sq_le a
  have hE₂_le : ‖E₂‖ ≤ Real.exp β - 1 - β - β ^ 2 / 2 := by
    rw [hE₂_def, hβ_def]; exact norm_exp_sub_one_sub_id_sub_sq_le b
  have hD₁_le : ‖D₁‖ ≤ Real.exp α - 1 - α := by
    rw [hD₁_def, hα_def]; exact norm_exp_sub_one_sub_id_le a
  have hD₂_le : ‖D₂‖ ≤ Real.exp β - 1 - β := by
    rw [hD₂_def, hβ_def]; exact norm_exp_sub_one_sub_id_le b
  have hexpαβ : Real.exp α * Real.exp β = Real.exp s := by rw [← Real.exp_add, hαβ]
  have hy_le : ‖y‖ ≤ Real.exp s - 1 := by
    have hfac : y = (exp a - 1) * exp b + (exp b - 1) := by
      rw [hy_def, sub_mul, one_mul]; abel
    calc ‖y‖ = ‖(exp a - 1) * exp b + (exp b - 1)‖ := by rw [hfac]
      _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ (Real.exp α - 1) * Real.exp β + (Real.exp β - 1) := by
          rw [hα_def, hβ_def]
          exact add_le_add
            (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_le b) (norm_nonneg _)
              (by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]))
            (norm_exp_sub_one_le b)
      _ = Real.exp s - 1 := by
          rw [show (Real.exp α - 1) * Real.exp β + (Real.exp β - 1)
              = Real.exp α * Real.exp β - 1 by ring, hexpαβ]
  have hP_factor : P = (exp a - 1) * (exp b - 1) + D₁ + D₂ := by
    rw [hP_def, hy_def, hD₁_def, hD₂_def]; noncomm_ring
  have hP_le : ‖P‖ ≤ Real.exp s - 1 - s := by
    rw [hP_factor]
    calc ‖(exp a - 1) * (exp b - 1) + D₁ + D₂‖
        ≤ ‖(exp a - 1) * (exp b - 1)‖ + ‖D₁‖ + ‖D₂‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (Real.exp α - 1) * (Real.exp β - 1) + (Real.exp α - 1 - α) + (Real.exp β - 1 - β) := by
          refine add_le_add (add_le_add ?_ hD₁_le) hD₂_le
          rw [hα_def, hβ_def]
          exact (norm_mul_le _ _).trans
            (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_sub_one_le b) (norm_nonneg _)
              (by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]))
      _ = Real.exp s - 1 - s := by
          rw [show (Real.exp α - 1) * (Real.exp β - 1) + (Real.exp α - 1 - α) + (Real.exp β - 1 - β)
              = Real.exp α * Real.exp β - 1 - (α + β) by ring, hexpαβ, hαβ]
  -- **piece A**: the logarithm's cubic remainder
  have hpieceA : ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2‖ ≤
      (Real.exp s - 1) ^ 3 / (2 - Real.exp s) := by
    have h1pos : (0 : ℝ) < 1 - ‖y‖ := by linarith
    calc ‖log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2‖ ≤ ‖y‖ ^ 3 * (1 - ‖y‖)⁻¹ :=
          norm_log_one_add_sub_add_sq_le y hy_lt
      _ ≤ (Real.exp s - 1) ^ 3 * (2 - Real.exp s)⁻¹ := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy_le 3) ?_ (inv_nonneg.mpr h1pos.le)
            (pow_nonneg (by linarith [Real.add_one_le_exp s]) 3)
          rw [inv_le_inv₀ h1pos hdenom]
          linarith
      _ = (Real.exp s - 1) ^ 3 / (2 - Real.exp s) := by rw [div_eq_mul_inv]
  -- **piece B**: the exponential's cubic remainder, as `½ • W`
  have hpieceB_eq : y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - (2 : ℚ)⁻¹ • y ^ 2 =
      (2 : ℚ)⁻¹ • W := by
    have h2ne : (2 : ℚ) ≠ 0 := two_ne_zero
    have hinj : Function.Injective fun z : 𝔸 => (2 : ℚ) • z := by
      intro u v huv
      have := congrArg (fun w : 𝔸 => (2 : ℚ)⁻¹ • w) huv
      simpa only [smul_smul, inv_mul_cancel₀ h2ne, one_smul] using this
    refine hinj ?_
    rw [hW_def, hP_def, hE₁_def, hE₂_def, hD₁_def, hD₂_def, hy_def]
    simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h2ne, one_smul, two_smul]
    noncomm_ring
  have hW_bound : ‖W‖ ≤ ‖(2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖ +
      ‖(a + b) * P‖ + ‖P * (a + b)‖ + ‖P ^ 2‖ := by
    have h : ‖W‖ ≤ ((‖(2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖ + ‖(a + b) * P‖) +
        ‖P * (a + b)‖) + ‖P ^ 2‖ := by
      rw [hW_def]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      refine (norm_sub_le _ _).trans ?_
      exact add_le_add (norm_sub_le _ _) le_rfl
    linarith
  have hT_le : ‖(2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖ ≤
      2 * (‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖) := by
    have haD : ‖a * D₂‖ ≤ α * ‖D₂‖ := norm_mul_le a D₂
    have hDb : ‖D₁ * b‖ ≤ ‖D₁‖ * β := norm_mul_le D₁ b
    have hDD : ‖D₁ * D₂‖ ≤ ‖D₁‖ * ‖D₂‖ := norm_mul_le D₁ D₂
    have hinner : ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
        ≤ ‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖ := by
      have h12 : ‖E₁ + E₂‖ ≤ ‖E₁‖ + ‖E₂‖ := norm_add_le _ _
      calc ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖
          ≤ ‖E₁ + E₂ + a * D₂ + D₁ * b‖ + ‖D₁ * D₂‖ := norm_add_le _ _
        _ ≤ (‖E₁ + E₂ + a * D₂‖ + ‖D₁ * b‖) + ‖D₁ * D₂‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ((‖E₁ + E₂‖ + ‖a * D₂‖) + ‖D₁ * b‖) + ‖D₁ * D₂‖ :=
            add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
        _ ≤ (((‖E₁‖ + ‖E₂‖) + α * ‖D₂‖) + ‖D₁‖ * β) + ‖D₁‖ * ‖D₂‖ :=
            add_le_add (add_le_add (add_le_add h12 haD) hDb) hDD
        _ = ‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖ := by ring
    calc ‖(2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖
        ≤ ‖(2 : ℚ)‖ * ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖ := norm_smul_le _ _
      _ = 2 * ‖E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂‖ := by
          rw [show ‖(2 : ℚ)‖ = 2 by rw [← Rat.norm_cast_real]; norm_num]
      _ ≤ 2 * (‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
  have habP : ‖(a + b) * P‖ ≤ s * ‖P‖ := by
    calc ‖(a + b) * P‖ ≤ ‖a + b‖ * ‖P‖ := norm_mul_le _ _
      _ ≤ (α + β) * ‖P‖ := mul_le_mul_of_nonneg_right (norm_add_le a b) (norm_nonneg P)
      _ = s * ‖P‖ := by rw [hαβ]
  have hPab : ‖P * (a + b)‖ ≤ ‖P‖ * s := by
    calc ‖P * (a + b)‖ ≤ ‖P‖ * ‖a + b‖ := norm_mul_le _ _
      _ ≤ ‖P‖ * (α + β) := mul_le_mul_of_nonneg_left (norm_add_le a b) (norm_nonneg P)
      _ = ‖P‖ * s := by rw [hαβ]
  have hP2 : ‖P ^ 2‖ ≤ ‖P‖ ^ 2 := norm_pow_le P 2
  have hpieceB : ‖y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - (2 : ℚ)⁻¹ • y ^ 2‖ ≤
      (Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
      (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
        (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
      s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2 := by
    have hQ_le : ‖E₁‖ + ‖E₂‖ + α * ‖D₂‖ + ‖D₁‖ * β + ‖D₁‖ * ‖D₂‖ ≤
        (Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
        (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
          (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) := by
      have h1 : α * ‖D₂‖ ≤ α * (Real.exp β - 1 - β) := mul_le_mul_of_nonneg_left hD₂_le hα_nn
      have h2 : ‖D₁‖ * β ≤ (Real.exp α - 1 - α) * β := mul_le_mul_of_nonneg_right hD₁_le hβ_nn
      have h3 : ‖D₁‖ * ‖D₂‖ ≤ (Real.exp α - 1 - α) * (Real.exp β - 1 - β) :=
        mul_le_mul hD₁_le hD₂_le (norm_nonneg _) (by linarith [Real.add_one_le_exp α])
      linarith [hE₁_le, hE₂_le]
    have hW_le : ‖W‖ ≤ 2 * ((Real.exp α - 1 - α - α ^ 2 / 2) +
        (Real.exp β - 1 - β - β ^ 2 / 2) +
        (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
          (Real.exp α - 1 - α) * (Real.exp β - 1 - β))) +
        2 * (s * (Real.exp s - 1 - s)) + (Real.exp s - 1 - s) ^ 2 := by
      have h1 : ‖(2 : ℚ) • (E₁ + E₂ + a * D₂ + D₁ * b + D₁ * D₂)‖ ≤
          2 * ((Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
            (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
              (Real.exp α - 1 - α) * (Real.exp β - 1 - β))) :=
        hT_le.trans (mul_le_mul_of_nonneg_left hQ_le (by norm_num))
      have h2 : ‖(a + b) * P‖ ≤ s * (Real.exp s - 1 - s) :=
        habP.trans (mul_le_mul_of_nonneg_left hP_le hs_nn)
      have h3 : ‖P * (a + b)‖ ≤ (Real.exp s - 1 - s) * s :=
        hPab.trans (mul_le_mul_of_nonneg_right hP_le hs_nn)
      have h4 : ‖P ^ 2‖ ≤ (Real.exp s - 1 - s) ^ 2 :=
        hP2.trans (pow_le_pow_left₀ (norm_nonneg P) hP_le 2)
      linarith [hW_bound, h1, h2, h3, h4]
    rw [hpieceB_eq]
    refine (norm_smul_le (2 : ℚ)⁻¹ W).trans ?_
    rw [show ‖(2 : ℚ)⁻¹‖ = (2 : ℝ)⁻¹ by
      rw [norm_inv, ← Rat.norm_cast_real]
      norm_num]
    calc (2 : ℝ)⁻¹ * ‖W‖
        ≤ (2 : ℝ)⁻¹ * (2 * ((Real.exp α - 1 - α - α ^ 2 / 2) +
            (Real.exp β - 1 - β - β ^ 2 / 2) +
            (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
              (Real.exp α - 1 - α) * (Real.exp β - 1 - β))) +
            2 * (s * (Real.exp s - 1 - s)) + (Real.exp s - 1 - s) ^ 2) :=
          mul_le_mul_of_nonneg_left hW_le (by norm_num)
      _ = (Real.exp α - 1 - α - α ^ 2 / 2) + (Real.exp β - 1 - β - β ^ 2 / 2) +
          (α * (Real.exp β - 1 - β) + (Real.exp α - 1 - α) * β +
            (Real.exp α - 1 - α) * (Real.exp β - 1 - β)) +
          s * (Real.exp s - 1 - s) + (Real.exp s - 1 - s) ^ 2 / 2 := by ring
  -- assemble
  have hY : (1 : 𝔸) + y = exp a * exp b := by rw [hy_def]; abel
  have hbch : bch a b = log (1 + y) := by rw [bch, ← hY]
  rw [show bch a b - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) =
      (log (1 + y) - y + (2 : ℚ)⁻¹ • y ^ 2) +
      (y - (a + b) - (2 : ℚ)⁻¹ • (a * b - b * a) - (2 : ℚ)⁻¹ • y ^ 2) by
    rw [hbch]; abel]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hpieceA hpieceB).trans ?_
  rw [div_add' _ _ _ (ne_of_gt hdenom), div_le_div_iff_of_pos_right hdenom]
  exact bch_cubic_real_core hα_nn hβ_nn hαβ hs1 hs56 hexp_lt

end CubicBound

/-! ### The Lie bracket

`⁅a, b⁆ = a * b - b * a` in an associative ring, via Mathlib's `LieRing.ofAssociativeRing`. The
instance is installed locally, as in `ChildsBasis.lean` and `NestedCommNorm.lean`. The Lie-form
restatements of the BCH bounds (`norm_bch_sub_add_sub_lie_le`, `norm_symmetric_bch_sub_add_lie_le`)
belong next to those bounds.

The statement needs only `[Ring 𝔸]`, so it sits outside the normed section. -/

end

section LieBracket

variable {𝔸 : Type*} [Ring 𝔸]

attribute [local instance] LieRing.ofAssociativeRing

/-- In an associative ring the Lie bracket is the ring commutator, `⁅a, b⁆ = a * b - b * a`. -/
theorem lie_eq_commutator (a b : 𝔸) : ⁅a, b⁆ = a * b - b * a :=
  LieRing.of_associative_ring_bracket a b

end LieBracket

section CubicBoundLie

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

attribute [local instance] LieRing.ofAssociativeRing

/-- **Commutator extraction, Lie bracket form**: `bch a b = a + b + ½⁅a, b⁆ + O(s³)`, the source's
main statement of H1 in Mathlib's Lie-bracket notation. -/
theorem norm_bch_sub_add_sub_lie_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖bch a b - (a + b) - (2 : ℚ)⁻¹ • ⁅a, b⁆‖ ≤
      10 * (‖a‖ + ‖b‖) ^ 3 / (2 - Real.exp (‖a‖ + ‖b‖)) := by
  rw [lie_eq_commutator]
  exact norm_bch_sub_add_sub_bracket_le a b hab

end CubicBoundLie


end FQFP.BCH
