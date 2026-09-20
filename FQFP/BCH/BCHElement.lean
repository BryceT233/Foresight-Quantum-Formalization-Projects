/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.ExpNorm
public import FQFP.BCH.Logarithm

import FQFP.BCH.RealScalar

/-!
# The Baker–Campbell–Hausdorff element

For `a b` in a complete normed algebra with `‖a‖ + ‖b‖ < log 2`, the Baker–Campbell–Hausdorff
element `bch a b` is the unique `Z` with `exp Z = exp a * exp b`. It is defined by applying the
Banach-algebra logarithm to the product:

`bch a b = log (exp a * exp b)`,

which is the form `Lean-BCH` writes as `logOnePlus (exp a * exp b - 1)`. Centering `log` at `1`
(see `FQFP/BCH/Logarithm.lean`) removes the subtraction from every statement, and `exp_bch` is then
read straight off `exp_log`.

This file is the *structural* layer: what `bch` is, and that it inverts `exp` on the ball where the
series converges. The quantitative layer — how far `bch a b` is from `a + b`, and that the leading
correction is the Lie bracket — is in `FQFP/BCH/BCHCommutator.lean`.

## The scalar interface

Everything is stated over `[NormedAlgebra ℚ 𝔸]` alone, because `NormedSpace.exp` and `FQFP.log`
carry no scalar field: both are `ℚ`-series with a junk value when no `ℚ`-algebra structure exists.
The `ℝ`-algebra structure that `Logarithm.lean`'s ODE argument needs is therefore *not* a
hypothesis but a local instance, obtained inside the proofs from `normedAlgebraReal`
(`RealScalar.lean`), which supplies it from `ℚ` plus completeness and proves it unique.

## Main definitions

* `bch a b` — the BCH element, `log (exp a * exp b)`.

## Main results

* `norm_exp_mul_exp_sub_one_lt_one`, `norm_exp_sub_one_lt_one` — the smallness conditions placing
  `exp a * exp b` (resp. `exp a`) inside the unit ball around `1`, which is exactly the convergence
  hypothesis of the log series.
* `exp_bch` — **the structural BCH theorem**: `exp (bch a b) = exp a * exp b` for
  `‖a‖ + ‖b‖ < log 2`.
* `log_exp_sub_one` — **the inverse identity**: `log (exp a) = a` for `‖a‖ < log 2`. The source's
  chain-of-neighborhoods argument, using `exp_eq_one_of_norm_lt` and
  `continuousOn_log_one_add`.
* `exp_eq_one_of_norm_lt` — `exp z = 1` with `‖z‖ < log 2` forces `z = 0`.
* `continuousOn_log_one_add` — `log (1 + ·)` is continuous on every closed ball of radius `< 1`.

## Provenance

Ported and re-architected from `Lean-BCH/BCH/Basic.lean`
(`norm_exp_mul_exp_sub_one_lt_one`, `norm_exp_sub_one_lt_one`, `bch`, `exp_bch`,
`exp_eq_one_of_norm_lt`, `continuousOn_logOnePlus`, `logOnePlus_exp_sub_one`). The source carried an
`RCLike 𝕂` scalar field and a hand-rolled `logOnePlus`, and unfolded `exp_logOnePlus` by hand in
`exp_bch`; here the definition is the centered `log` and `exp_bch` is `exp_log` itself.
-/

@[expose] public section

open NormedSpace TrotterError

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-! ### Smallness conditions

`bch` is `log` applied to `exp a * exp b`, so it needs that product inside the unit ball around
`1`. Both statements below have `Real.exp (‖a‖ + ‖b‖) < 2` — equivalently `‖a‖ + ‖b‖ < log 2` — as
their only arithmetic input. -/

/-- **The BCH smallness condition**: `‖exp a * exp b - 1‖ < 1` when `‖a‖ + ‖b‖ < log 2`, which is
what puts `exp a * exp b` inside the ball where the log series converges. -/
theorem norm_exp_mul_exp_sub_one_lt_one (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    ‖exp a * exp b - 1‖ < 1 := by
  have hfactor : exp a * exp b - 1 = (exp a - 1) * exp b + (exp b - 1) := by
    rw [sub_mul, one_mul]; abel
  have ha_nn : 0 ≤ Real.exp ‖a‖ - 1 := by linarith [Real.add_one_le_exp ‖a‖, norm_nonneg a]
  rw [hfactor]
  calc ‖(exp a - 1) * exp b + (exp b - 1)‖
      ≤ ‖(exp a - 1) * exp b‖ + ‖exp b - 1‖ := norm_add_le _ _
    _ ≤ ‖exp a - 1‖ * ‖exp b‖ + ‖exp b - 1‖ := by
        refine add_le_add ?_ le_rfl
        exact (norm_mul_le _ _).trans (le_of_eq rfl)
    _ ≤ (Real.exp ‖a‖ - 1) * Real.exp ‖b‖ + (Real.exp ‖b‖ - 1) :=
        add_le_add
          (mul_le_mul (norm_exp_sub_one_le a) (norm_exp_le b) (norm_nonneg _) ha_nn)
          (norm_exp_sub_one_le b)
    _ = Real.exp (‖a‖ + ‖b‖) - 1 := by rw [Real.exp_add]; ring
    _ < 1 := by
        have h2 : Real.exp (‖a‖ + ‖b‖) < 2 := by
          calc Real.exp (‖a‖ + ‖b‖) < Real.exp (Real.log 2) := Real.exp_strictMono hab
            _ = 2 := Real.exp_log (by norm_num)
        linarith

/-- **The BCH smallness condition, one-sided form**: `‖exp a - 1‖ < 1` when `‖a‖ < log 2`. -/
theorem norm_exp_sub_one_lt_one (a : 𝔸) (ha : ‖a‖ < Real.log 2) : ‖exp a - 1‖ < 1 := by
  have h := norm_exp_mul_exp_sub_one_lt_one a (0 : 𝔸) (by simpa using ha)
  simpa [exp_zero] using h

/-! ### The BCH element -/

/-- The Baker–Campbell–Hausdorff element of `a` and `b`: the `Z` with `exp Z = exp a * exp b`,
defined as `log (exp a * exp b)`. It satisfies `exp_bch` when `‖a‖ + ‖b‖ < log 2`. -/
noncomputable def bch (a b : 𝔸) : 𝔸 := log (exp a * exp b)

/-- **The structural BCH theorem**: `exp (bch a b) = exp a * exp b` for `‖a‖ + ‖b‖ < log 2`.

This is `exp_log` at `exp a * exp b`, whose side condition is
`norm_exp_mul_exp_sub_one_lt_one`. -/
theorem exp_bch (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < Real.log 2) :
    exp (bch a b) = exp a * exp b :=
  exp_log (norm_exp_mul_exp_sub_one_lt_one a b hab)

/-! ### The quadratic remainder of `exp`

`exp_eq_one_of_norm_lt` below needs the second-order remainder `‖exp z - 1 - z‖`, which is
`ExpNorm.norm_exp_sub_one_sub_id_le`. -/

/-- **If `exp z = 1` and `‖z‖ < log 2` then `z = 0`.** This is what upgrades the
chain-of-neighborhoods argument for `log_exp_sub_one` from `exp (h t) = 1` to `h t = 0`. -/
theorem exp_eq_one_of_norm_lt (z : 𝔸) (hz : exp z = 1) (hn : ‖z‖ < Real.log 2) : z = 0 := by
  have hkey : z = -(exp z - 1 - z) := by rw [hz]; simp
  have hbound : ‖z‖ ≤ Real.exp ‖z‖ - 1 - ‖z‖ := by
    calc ‖z‖ = ‖-(exp z - 1 - z)‖ := by conv_lhs => rw [hkey]
      _ = ‖exp z - 1 - z‖ := norm_neg _
      _ ≤ Real.exp ‖z‖ - 1 - ‖z‖ := norm_exp_sub_one_sub_id_le z
  by_contra h
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr h
  have hexp_lt : Real.exp ‖z‖ < 2 := by
    calc Real.exp ‖z‖ < Real.exp (Real.log 2) := Real.exp_strictMono hn
      _ = 2 := Real.exp_log (by norm_num)
  have h_half : ‖z‖ < 1 / 2 := by linarith
  have h_exp_bound : Real.exp ‖z‖ * (1 - ‖z‖) ≤ 1 := by
    have h_exp := hasSum_real_exp ‖z‖
    have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) (by linarith)
    have hle : Real.exp ‖z‖ ≤ (1 - ‖z‖)⁻¹ := by
      calc Real.exp ‖z‖ = ∑' n : ℕ, (Nat.factorial n : ℝ)⁻¹ * ‖z‖ ^ n := h_exp.tsum_eq.symm
        _ ≤ ∑' n : ℕ, ‖z‖ ^ n := by
            refine h_exp.summable.tsum_le_tsum (fun n => ?_) h_geom.summable
            have hfac : (Nat.factorial n : ℝ)⁻¹ ≤ 1 := by
              rw [inv_le_one₀ (by positivity)]
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
            calc (Nat.factorial n : ℝ)⁻¹ * ‖z‖ ^ n ≤ 1 * ‖z‖ ^ n :=
                  mul_le_mul_of_nonneg_right hfac (pow_nonneg (norm_nonneg z) n)
              _ = ‖z‖ ^ n := one_mul _
        _ = (1 - ‖z‖)⁻¹ := h_geom.tsum_eq
    calc Real.exp ‖z‖ * (1 - ‖z‖) ≤ (1 - ‖z‖)⁻¹ * (1 - ‖z‖) :=
          mul_le_mul_of_nonneg_right hle (by linarith)
      _ = 1 := inv_mul_cancel₀ (by linarith)
  nlinarith [norm_nonneg z, pow_nonneg (norm_nonneg z) 2]

/-! ### Continuity of `log (1 + ·)` on a closed ball

The source proved this by term-by-term continuity of the log series. Here it follows from
`continuousOn_log`: `closedBall 0 r` with `r < 1` maps into the open unit ball around `1` under
`y ↦ 1 + y`, and that ball is the open ball of convergence of `log`. -/

/-- `log (1 + ·)` is continuous on `closedBall 0 r` for `r < 1`. -/
theorem continuousOn_log_one_add {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun y : 𝔸 => log (1 + y)) (Metric.closedBall (0 : 𝔸) r) := by
  refine continuousOn_log.comp (continuousOn_const.add continuousOn_id) fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  have h1 : dist (1 + y) (1 : 𝔸) = ‖y‖ := by
    rw [dist_eq_norm, show (1 : 𝔸) + y - 1 = y by abel]
  rw [Metric.mem_eball, logSeries_radius_eq_one, edist_dist, h1, ENNReal.ofReal_lt_one]
  exact lt_of_le_of_lt hy hr

/-! ### The `log ∘ exp` identity

`log (exp a) = a` for `‖a‖ < log 2`. The source's chain-of-neighborhoods argument: put
`h t = log (1 + (exp (t • a) - 1)) - t • a`; then `h 0 = 0`, `exp (h t) = 1` throughout, and `h`
is continuous on the compact interval `[0, 1]`, so it is *uniformly* continuous there; a fixed-step
induction then propagates `h (k/N) = 0` from `k = 0` to `k = N`. Only two inputs are used: the
`log ∘ exp` identity `exp_log`, and `exp_eq_one_of_norm_lt` to convert `exp (h t) = 1` into
`h t = 0`. -/

/-- **`log (exp a) = a` for `‖a‖ < log 2`**: the logarithm inverts the exponential on the ball
where the BCH series converges. -/
theorem log_exp_sub_one (a : 𝔸) (ha : ‖a‖ < Real.log 2) : log (exp a) = a := by
  have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸
  set h : ℝ → 𝔸 := fun t => log (1 + (exp (t • a) - 1)) - t • a with hh_def
  suffices h1 : h 1 = 0 by
    simp only [hh_def] at h1
    rw [one_smul, show (1 : 𝔸) + (exp a - 1) = exp a from by abel, sub_eq_zero] at h1
    exact h1
  have h0 : h 0 = 0 := by rw [hh_def]; simp
  have hexp_ht : ∀ t : ℝ, t * ‖a‖ < Real.log 2 → 0 ≤ t → exp (h t) = 1 := by
    intro t ht ht_nn
    have harg : (1 : 𝔸) + (exp (t • a) - 1) = exp (t • a) := by abel
    have hnorm : ‖exp (t • a) - 1‖ < 1 := by
      refine norm_exp_sub_one_lt_one (t • a) ?_
      calc ‖t • a‖ ≤ |t| * ‖a‖ := norm_smul_le t a
        _ = t * ‖a‖ := by rw [abs_of_nonneg ht_nn]
        _ < Real.log 2 := ht
    have hexp_log : exp (log (1 + (exp (t • a) - 1))) = exp (t • a) := by
      rw [harg]; exact exp_log hnorm
    -- `exp (t • a)` commutes with `t • a`, hence so does its logarithm
    have hcomm : Commute (log (1 + (exp (t • a) - 1))) (t • a) := by
      rw [harg]
      exact (((Commute.refl a).smul_left t).exp_left).smul_right t |>.log_left
    rw [hh_def]
    simp only
    rw [sub_eq_add_neg, exp_add_of_commute hcomm.neg_right, hexp_log,
      ← exp_add_of_commute ((Commute.refl (t • a)).neg_right), add_neg_cancel, exp_zero]
  have hcont : ContinuousOn h (Set.Icc 0 1) := by
    have hρ_lt : Real.exp ‖a‖ - 1 < 1 := by
      have h2 : Real.exp ‖a‖ < 2 := by
        calc Real.exp ‖a‖ < Real.exp (Real.log 2) := Real.exp_strictMono ha
          _ = 2 := Real.exp_log (by norm_num)
      linarith
    rw [hh_def]
    refine ContinuousOn.sub ?_ (continuous_id.smul continuous_const).continuousOn
    refine (continuousOn_log_one_add hρ_lt).comp ?_ ?_
    · exact ContinuousOn.sub
        (NormedSpace.exp_continuous.continuousOn.comp
          ((continuous_id.smul continuous_const).continuousOn) (Set.mapsTo_univ _ _))
        continuousOn_const
    · intro t ht
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖exp (t • a) - 1‖ ≤ Real.exp ‖t • a‖ - 1 := norm_exp_sub_one_le (t • a)
        _ ≤ Real.exp (t * ‖a‖) - 1 := by
            gcongr
            calc ‖t • a‖ ≤ |t| * ‖a‖ := norm_smul_le t a
              _ = t * ‖a‖ := by rw [abs_of_nonneg ht.1]
        _ ≤ Real.exp (1 * ‖a‖) - 1 := by gcongr; exact ht.2
        _ = Real.exp ‖a‖ - 1 := by rw [one_mul]
  -- uniform continuity on the compact interval `[0, 1]`, then a fixed-step induction
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have huc := hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (Real.log 2) (Real.log_pos (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hN_pos : 0 < N := by
    rcases N with _ | n
    · simp at hN
      linarith [div_pos one_pos hδ_pos]
    · exact Nat.succ_pos n
  suffices hind : ∀ k : ℕ, k ≤ N → h (k / N) = 0 by
    have := hind N le_rfl
    rwa [show (N : ℝ) / N = 1 from div_self (Nat.cast_ne_zero.mpr (by lia))] at this
  intro k hk
  induction k with
  | zero => simpa using h0
  | succ k ih =>
      have hk_le : k ≤ N := by lia
      have hprev := ih hk_le
      have hN_pos_real : (0 : ℝ) < N := Nat.cast_pos.mpr hN_pos
      have hkN_mem : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Nat.cast_nonneg k) hN_pos_real.le,
         div_le_one_of_le₀ (Nat.cast_le.mpr hk_le) hN_pos_real.le⟩
      have hk1N_mem : ((k + 1 : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Nat.cast_nonneg _) hN_pos_real.le,
         div_le_one_of_le₀ (Nat.cast_le.mpr hk) hN_pos_real.le⟩
      have h1N_lt : (1 : ℝ) / N < δ := by
        rw [div_lt_iff₀ hN_pos_real]
        have hN' : (1 : ℝ) < N * δ := (div_lt_iff₀ hδ_pos).mp hN
        linarith
      have hdist' : dist ((↑(k + 1) : ℝ) / ↑N) (↑k / ↑N) < δ := by
        rw [dist_comm, Real.dist_eq,
          show (k : ℝ) / N - ((k + 1 : ℕ) : ℝ) / N = -(1 / N) from by
            push_cast; field_simp; ring,
          abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N)]
        exact h1N_lt
      have hnorm_small : ‖h ((k + 1 : ℕ) / N) - h (k / N)‖ < Real.log 2 := by
        rw [← dist_eq_norm]
        exact hδ _ hk1N_mem _ hkN_mem hdist'
      rw [hprev, sub_zero] at hnorm_small
      have hexp1 : exp (h ((k + 1 : ℕ) / N)) = 1 :=
        hexp_ht _ (by
          calc ((k + 1 : ℕ) : ℝ) / N * ‖a‖ ≤ 1 * ‖a‖ := by
                gcongr; exact hk1N_mem.2
            _ = ‖a‖ := one_mul _
            _ < Real.log 2 := ha) hk1N_mem.1
      exact exp_eq_one_of_norm_lt _ hexp1 hnorm_small

end

end FQFP.BCH
