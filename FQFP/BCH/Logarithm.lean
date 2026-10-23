/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Algebra.Logarithm
public import Mathlib.Analysis.SpecialFunctions.Exponential

import FQFP.BCH.RealScalar

/-!
# Analysis of the Banach-algebra logarithm

This file extends Mathlib's `NormedSpace.log` and `NormedSpace.logSeries` with convergence,
analyticity, remainder bounds, and the identity `exp (log x) = x` on the open unit ball around `1`.
The definitions and elementary algebraic properties come from Mathlib.

## Main definitions

* `logCoeff n` — the rational coefficient `(-1)^(n+1)/n`.
* `logPartialSum 𝔸 n x` — the log series summed over degrees strictly smaller than `n`.

## Main results

* `logSeries_radius_eq_one` — the series has radius of convergence `1`.
* `log_hasFPowerSeriesOnBall` — `log` is the sum of its series on the open unit ball around `1`.
* `hasStrictFDerivAt_log_one` — `log` is strictly differentiable at `1`, derivative the identity.
* `exp_log_one_add`, `exp_log` — `exp (log (1 + x)) = 1 + x` for `‖x‖ < 1`, and `exp (log y) = y`
  for `‖y - 1‖ < 1`, by the ODE route.
-/

@[expose] public section

open FormalMultilinearSeries Filter NormedSpace Topology
open scoped ENNReal

namespace FQFP

variable {𝔸 𝕂 : Type*}

/-! ### Additional lemmas for the formal multilinear series -/

section Series

variable [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- Function form of `logSeries_apply_eq`. -/
theorem logSeries_apply_eq' (x : 𝔸) :
    (fun n => logSeries 𝕂 𝔸 n fun _ => x)
      = fun n : ℕ => ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n :=
  funext (logSeries_apply_eq x)

/-- **The linear term is `x`.** -/
@[simp]
theorem logSeries_apply_one (x : 𝔸) : (logSeries 𝕂 𝔸 1 fun _ => x) = x := by
  rw [logSeries_apply_eq]
  norm_num

/-- **The quadratic term is `-(1/2) • x^2`.** -/
@[simp]
theorem logSeries_apply_two (x : 𝔸) :
    (logSeries 𝕂 𝔸 2 fun _ => x) = (-(2 : 𝕂)⁻¹) • x ^ 2 := by
  rw [logSeries_apply_eq]
  norm_num [div_eq_mul_inv]

private lemma neg_one_pow_div_natCast_eq_inv_intCast (T : Type*) [DivisionRing T] (k n : ℕ) :
    ((-1) ^ k / n : T) = (((-1) ^ k * n : ℤ) : T)⁻¹ := by
  rcases Nat.even_or_odd k with hk | hk <;> simp [hk.neg_one_pow, div_eq_mul_inv, inv_neg]

/-- If `E` is a module over two division rings `R` and `S`, then scalar multiplication by the
coefficients `(-1) ^ k / n` of the logarithm series agrees in `R` and in `S`. -/
private lemma neg_one_pow_div_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E]
    [DivisionRing R] [DivisionRing S] [Module R E] [Module S E] (k n : ℕ) (x : E) :
    ((-1) ^ k / n : R) • x = ((-1) ^ k / n : S) • x := by
  rw [neg_one_pow_div_natCast_eq_inv_intCast R, neg_one_pow_div_natCast_eq_inv_intCast S,
    inv_intCast_smul_eq R S]

/-- A version of `logSeries_eq_logSeries_rat` for two arbitrary scalar fields. Counterpart of
`NormedSpace.expSeries_eq_expSeries`. -/
theorem logSeries_eq_logSeries {𝕂' : Type*} [Field 𝕂'] [Algebra 𝕂' 𝔸] (n : ℕ) (x : 𝔸) :
    (logSeries 𝕂 𝔸 n fun _ => x) = logSeries 𝕂' 𝔸 n fun _ => x := by
  rw [logSeries_apply_eq, logSeries_apply_eq, neg_one_pow_div_natCast_smul_eq 𝕂 𝕂']

end Series

/-! ### The radius of convergence

Unlike `expSeries`, whose radius is infinite (`expSeries_radius_eq_top`), the log series has radius
`1`: its coefficients are `1/n`, so the ratio test tends to `1`.

The coefficient norms and the ratio tests mention only `ℚ` and `ℝ`, so they carry no algebra
variables at all. The radius itself is then computed separately over the two scalar fields, since
`logSeries ℚ 𝔸` and `logSeries ℝ 𝔸` are different series: the ODE route below differentiates along a
real parameter and so needs the `ℝ` one, while `log` itself is defined through the `ℚ` one. -/

/-- **The coefficients of the log series have norm `1/n`.** -/
theorem norm_logSeries_coeff (n : ℕ) : ‖((-1 : ℚ) ^ (n + 1) / n)‖ = (n : ℝ)⁻¹ := by
  rw [norm_div, norm_pow, show ‖(-1 : ℚ)‖ = 1 by simp, one_pow, one_div]
  congr 1
  rw [← Rat.norm_cast_real]
  norm_num

/-- **The coefficients of the log series have norm `1/n`, over `ℝ`.** -/
theorem norm_logSeries_coeff_real (n : ℕ) : ‖((-1 : ℝ) ^ (n + 1) / n)‖ = (n : ℝ)⁻¹ := by
  rw [norm_div, norm_pow, show ‖(-1 : ℝ)‖ = 1 by simp, one_pow, one_div]
  simp

/-- **The ratio of consecutive coefficient norms tends to `1`**, which is the ratio test that fixes
the radius. Its orientation matches `ofScalars_radius_eq_of_tendsto`. -/
theorem tendsto_norm_logSeries_coeff_ratio :
    Tendsto (fun n : ℕ => ‖((-1 : ℚ) ^ (n + 1) / n)‖ / ‖((-1 : ℚ) ^ (n.succ + 1) / n.succ)‖)
      atTop (𝓝 1) := by
  simp_rw [norm_logSeries_coeff]
  simpa only [inv_div_inv, Nat.cast_succ, inv_div, inv_one] using
    (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1).inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- **The ratio of consecutive coefficient norms tends to `1`**, over `ℝ`. The two coefficient norms
are the same function of `n`, so this follows from the `ℚ` statement by rewriting. -/
theorem tendsto_norm_logSeries_coeff_ratio_real :
    Tendsto (fun n : ℕ => ‖((-1 : ℝ) ^ (n + 1) / n)‖ / ‖((-1 : ℝ) ^ (n.succ + 1) / n.succ)‖)
      atTop (𝓝 1) := by
  simpa only [norm_logSeries_coeff, norm_logSeries_coeff_real] using
    tendsto_norm_logSeries_coeff_ratio

section Radius

variable [NormedRing 𝔸]

variable [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] in
/-- **The radius of `logSeries ℚ 𝔸` is `1`.** Counterpart of `expSeries_radius_eq_top`. -/
theorem logSeries_radius_eq_one : (logSeries ℚ 𝔸).radius = 1 := by
  rw [logSeries_eq_ofScalars]
  convert FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (E := 𝔸)
    (fun n : ℕ => ((-1 : ℚ) ^ (n + 1) / n)) (r := 1) one_ne_zero
    tendsto_norm_logSeries_coeff_ratio using 1

variable [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] in
/-- **The radius of `logSeries ℝ 𝔸` is `1`.** Counterpart of `logSeries_radius_eq_one`. -/
theorem logSeries_radius_eq_one_real : (logSeries ℝ 𝔸).radius = 1 := by
  rw [logSeries_eq_ofScalars]
  convert FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (E := 𝔸)
    (fun n : ℕ => ((-1 : ℝ) ^ (n + 1) / n)) (r := 1) one_ne_zero
    tendsto_norm_logSeries_coeff_ratio_real using 1

end Radius

/-! ### Summability inside the ball

`logSeries` is an `ofScalars` series like `expSeries`, so summability inside the ball is read off
`FormalMultilinearSeries.summable_norm_apply`. Unlike `expSeries`, whose radius is infinite, these
are the only summability statements available here: there is no counterpart of `expSeries_summable`
without the ball hypothesis. -/

section PowerSeries

variable [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- **The log series is summable in norm inside its ball.** Counterpart of
`NormedSpace.norm_expSeries_summable_of_mem_ball`. -/
theorem norm_logSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n => ‖logSeries 𝕂 𝔸 n fun _ => x‖ :=
  (logSeries 𝕂 𝔸).summable_norm_apply hx

/-- Diagonal form of `norm_logSeries_summable_of_mem_ball`. Counterpart of
`NormedSpace.norm_expSeries_summable_of_mem_ball'`. -/
theorem norm_logSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n : ℕ => ‖((-1 : 𝕂) ^ (n + 1) / n) • x ^ n‖ := by
  change Summable (norm ∘ _)
  rw [← logSeries_apply_eq']
  exact norm_logSeries_summable_of_mem_ball x hx

variable [CompleteSpace 𝔸]

/-- **The log series is summable inside its ball.** Counterpart of
`NormedSpace.expSeries_summable_of_mem_ball`. -/
theorem logSeries_summable_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n => logSeries 𝕂 𝔸 n fun _ => x :=
  (norm_logSeries_summable_of_mem_ball x hx).of_norm

/-- Diagonal form of `logSeries_summable_of_mem_ball`. Counterpart of
`NormedSpace.expSeries_summable_of_mem_ball'`. -/
theorem logSeries_summable_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    Summable fun n : ℕ => ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n :=
  (norm_logSeries_summable_of_mem_ball' x hx).of_norm

/-! ### The power series

`log` is the sum of its power series on the open ball around `1` with the series' actual radius.
For rational and real scalars, that radius is `1` when `‖1‖ = 1`. The generic statements below use
the actual radius and apply to any normed scalar field of characteristic zero. -/

variable [CharZero 𝕂]

/-- **`log (1 + x)` is the sum of the log series inside its ball of convergence.** Counterpart of
`expSeries_hasSum_exp_of_mem_ball`. The scalar field has characteristic zero; the radius is the
actual radius of the series, without an assumption on the norm of rational scalars. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun n => logSeries 𝕂 𝔸 n fun _ => x) (log (1 + x)) := by
  simpa only [log_eq_logSeries_sum 𝕂, add_sub_cancel_left] using
    FormalMultilinearSeries.hasSum (logSeries 𝕂 𝔸) hx

/-- Diagonal form of `logSeries_hasSum_log_one_add_of_mem_ball`. Counterpart of
`expSeries_hasSum_exp_of_mem_ball'`. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries 𝕂 𝔸).radius) :
    HasSum (fun n : ℕ => ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n) (log (1 + x)) := by
  rw [← logSeries_apply_eq']
  exact logSeries_hasSum_log_one_add_of_mem_ball x hx

/-- **`log` has its power series on its ball of convergence**, whenever that radius is positive. -/
theorem log_hasFPowerSeriesOnBall_of_radius_pos (h : 0 < (logSeries 𝕂 𝔸).radius) :
    HasFPowerSeriesOnBall log (logSeries 𝕂 𝔸) 1 (logSeries 𝕂 𝔸).radius := by
  simpa only [log_eq_logSeries_sum 𝕂, zero_add] using
    ((logSeries 𝕂 𝔸).hasFPowerSeriesOnBall h).comp_sub (1 : 𝔸)

end PowerSeries

section Ball

variable [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

variable [NormOneClass 𝔸] in
/-- Any point of the open unit ball lies inside the radius of convergence. -/
theorem mem_eball_logSeries_radius {x : 𝔸} (hx : ‖x‖ < 1) :
    x ∈ Metric.eball (0 : 𝔸) (logSeries ℚ 𝔸).radius := by
  rwa [mem_eball_zero_iff, logSeries_radius_eq_one, ← ofReal_norm, ENNReal.ofReal_lt_one]

variable [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **`log` is the sum of its power series on the open unit ball around `1`.** Counterpart of
`exp_hasFPowerSeriesOnBall`, whose ball is instead all of `𝔸`. -/
theorem log_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall log (logSeries ℚ 𝔸) 1 1 := by
  simpa only [logSeries_radius_eq_one] using
    log_hasFPowerSeriesOnBall_of_radius_pos (𝕂 := ℚ) (𝔸 := 𝔸)
      (by simp only [logSeries_radius_eq_one, zero_lt_one])

/-- **`log` has a power series at its center.** Counterpart of
`hasFPowerSeriesAt_exp_zero_of_radius_pos`. -/
theorem log_hasFPowerSeriesAt_one : HasFPowerSeriesAt log (logSeries ℚ 𝔸) 1 :=
  log_hasFPowerSeriesOnBall.hasFPowerSeriesAt

/-- **`log` is continuous on its ball.** Counterpart of `continuousOn_exp`, whose ball is instead
all of `𝔸`. -/
theorem continuousOn_log :
    ContinuousOn (log : 𝔸 → 𝔸) (Metric.eball (1 : 𝔸) (logSeries ℚ 𝔸).radius) := by
  rw [logSeries_radius_eq_one]
  exact log_hasFPowerSeriesOnBall.continuousOn

/-- **`log` is analytic at every point of its ball.** Counterpart of
`analyticAt_exp_of_mem_ball`. -/
theorem analyticAt_log_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (1 : 𝔸) (logSeries ℚ 𝔸).radius) :
    AnalyticAt ℚ log x := by
  rw [logSeries_radius_eq_one] at hx
  exact log_hasFPowerSeriesOnBall.analyticAt_of_mem hx

end Ball

/-! ### The `ℝ`-power series of `log (1 + ·)`

These results express the same logarithm with real coefficients, as used in the term-by-term
differentiation below. -/

section BallReal

variable [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

variable [CompleteSpace 𝔸] in
/-- **`log (1 + x)` is the sum of the `ℝ`-series inside its ball of convergence.** Counterpart of
`logSeries_hasSum_log_one_add_of_mem_ball`, specialized to real scalars. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball_real (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries ℝ 𝔸).radius) :
    HasSum (fun n => logSeries ℝ 𝔸 n fun _ => x) (log (1 + x)) :=
  logSeries_hasSum_log_one_add_of_mem_ball x hx

variable [NormOneClass 𝔸] in
/-- Any point of the open unit ball lies inside the radius of convergence, over `ℝ`. -/
theorem mem_eball_logSeries_radius_real {x : 𝔸} (hx : ‖x‖ < 1) :
    x ∈ Metric.eball (0 : 𝔸) (logSeries ℝ 𝔸).radius := by
  rwa [mem_eball_zero_iff, logSeries_radius_eq_one_real, ← ofReal_norm, ENNReal.ofReal_lt_one]

variable [CompleteSpace 𝔸] [NormOneClass 𝔸] in
/-- **`x ↦ log (1 + x)` is the sum of `logSeries ℝ 𝔸` at `0`.** -/
theorem hasFPowerSeriesOnBall_log_one_add_real :
    HasFPowerSeriesOnBall (fun y : 𝔸 => log (1 + y)) (logSeries ℝ 𝔸) 0 1 := by
  have h := log_hasFPowerSeriesOnBall_of_radius_pos (𝕂 := ℝ) (𝔸 := 𝔸)
    (by simp only [logSeries_radius_eq_one_real, zero_lt_one])
  simpa only [sub_neg_eq_add, add_neg_cancel, logSeries_radius_eq_one_real, add_comm] using
    h.comp_sub (-1 : 𝔸)

end BallReal

/-! ### Remainder bounds for `log (1 + ·)`

The logarithm is `x ↦ log (1 + x) = ∑ₙ cₙ • xⁿ` with `cₙ = (-1)^(n+1)/n`, so its remainder after
the partial sum through `x^(n-1)` is the tail of that series and is bounded by the corresponding
geometric tail. The statements here are parametrized by `n`: the nine arity-indexed lemmas of
`Lean-BCH/BCH/LogSeries.lean` (`norm_logOnePlus_le` and the `norm_logOnePlus_sub_…_le` chain
through order nine) are the cases `n = 0, 2, 3, …, 9` of `norm_log_one_add_sub_logPartialSum_le`
(there is no source lemma for `n = 1`, whose constant coefficient vanishes).

Following `exp`'s treatment in `Mathlib/Analysis/Normed/Algebra/Exponential.lean`, the *truncated*
form `1 + x` is the one used: there is deliberately no separate `logOnePlus` name. -/

section PartialSum

variable [Ring 𝔸] [Algebra ℚ 𝔸]

/-- The coefficients of the log series: `logCoeff i = (-1)^(i+1)/i`, so that
`log (1 + x) = ∑ᵢ logCoeff i • xⁱ`. Naming them keeps the coercions out of the statements below,
where `logCoeff` is only ever applied to a *natural-number* index. -/
def logCoeff (i : ℕ) : ℚ := (-1 : ℚ) ^ (i + 1) / i

@[simp] theorem logCoeff_zero : logCoeff 0 = 0 := by norm_num [logCoeff]
@[simp] theorem logCoeff_one : logCoeff 1 = 1 := by norm_num [logCoeff]
@[simp] theorem logCoeff_two : logCoeff 2 = -(2 : ℚ)⁻¹ := by norm_num [logCoeff]
@[simp] theorem logCoeff_three : logCoeff 3 = (3 : ℚ)⁻¹ := by norm_num [logCoeff]

/-- The partial sum `∑_{i<n} logCoeff i • xⁱ` of the log series. The subscript `n` is the degree of
the *first omitted* term, which is what makes it line up with the split point of
`Summable.sum_add_tsum_nat_add`: `logPartialSum 𝔸 0 x = 0`, `logPartialSum 𝔸 1 x = 0` (the constant
coefficient is `(-1)/0 = 0`), `logPartialSum 𝔸 2 x = x`, `logPartialSum 𝔸 3 x = x - x²/2`. -/
def logPartialSum (𝔸 : Type*) [Ring 𝔸] [Algebra ℚ 𝔸] (n : ℕ)
    (x : 𝔸) : 𝔸 :=
  ∑ i ∈ Finset.range n, logCoeff i • x ^ i

@[simp]
theorem logPartialSum_zero (x : 𝔸) : logPartialSum 𝔸 0 x = 0 :=
  Finset.sum_range_zero _

/-- **The next partial sum adds the term of degree `n`.** -/
theorem logPartialSum_succ (n : ℕ) (x : 𝔸) :
    logPartialSum 𝔸 (n + 1) x = logPartialSum 𝔸 n x + logCoeff n • x ^ n :=
  Finset.sum_range_succ _ _

/-- The first partial sum of the log series vanishes: its constant coefficient is `(-1)/0 = 0`. -/
@[simp]
theorem logPartialSum_one (x : 𝔸) : logPartialSum 𝔸 1 x = 0 := by
  simp only [logPartialSum_succ, logPartialSum_zero, logCoeff_zero, zero_smul, add_zero]

/-- The second partial sum of the log series is the linear term `x`. -/
@[simp]
theorem logPartialSum_two (x : 𝔸) : logPartialSum 𝔸 2 x = x := by
  rw [logPartialSum_succ, logPartialSum_one, logCoeff_one, one_smul, pow_one, zero_add]

/-- The third partial sum of the log series is `x - x²/2`. -/
@[simp]
theorem logPartialSum_three (x : 𝔸) :
    logPartialSum 𝔸 3 x = x - (2 : ℚ)⁻¹ • x ^ 2 := by
  rw [logPartialSum_succ, logPartialSum_two, logCoeff_two, neg_smul, sub_eq_add_neg]

/-- The fourth partial sum of the log series is `x - x²/2 + x³/3`. -/
@[simp]
theorem logPartialSum_four (x : 𝔸) :
    logPartialSum 𝔸 4 x = x - (2 : ℚ)⁻¹ • x ^ 2 + (3 : ℚ)⁻¹ • x ^ 3 := by
  rw [logPartialSum_succ, logPartialSum_three, logCoeff_three]

end PartialSum

section PartialSumNorm

variable [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- **The log coefficients have norm at most `1`.** -/
theorem norm_logCoeff_le_one (i : ℕ) : ‖logCoeff i‖ ≤ 1 := by
  rw [logCoeff, norm_logSeries_coeff]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]
    norm_num
  · rw [inv_le_one₀ (by positivity)]
    exact_mod_cast (Nat.succ_le_iff.mpr h)

/-- **Each logarithm term is bounded by the corresponding power of the norm.** The constant
coefficient vanishes, so this estimate does not require `‖1‖ = 1`. -/
theorem norm_logCoeff_smul_pow_le (x : 𝔸) (i : ℕ) :
    ‖logCoeff i • x ^ i‖ ≤ ‖x‖ ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · calc ‖logCoeff i • x ^ i‖ = ‖logCoeff i‖ * ‖x ^ i‖ := norm_smul _ _
      _ ≤ 1 * ‖x‖ ^ i :=
        mul_le_mul (norm_logCoeff_le_one i) (norm_pow_le' x hi) (norm_nonneg _) zero_le_one
      _ = ‖x‖ ^ i := one_mul _

/-- **A tail of the log series is bounded by the geometric tail of `x`.** The `k`-th term is
`logCoeff (k + n) • x^(k + n)`, and `‖logCoeff i‖ ≤ 1`. -/
private lemma norm_logSeries_tail_le (x : 𝔸) {n : ℕ} (hx : ‖x‖ < 1) :
    ‖∑' k : ℕ, logCoeff (k + n) • x ^ (k + n)‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹ := by
  have hterm : ∀ k : ℕ, ‖logCoeff (k + n) • x ^ (k + n)‖ ≤ ‖x‖ ^ n * ‖x‖ ^ k := by
    intro k
    simpa only [pow_add, mul_comm] using norm_logCoeff_smul_pow_le x (k + n)
  exact tsum_of_norm_bounded
    (f := fun k : ℕ => logCoeff (k + n) • x ^ (k + n))
    ((hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖ ^ n)) hterm

variable [CompleteSpace 𝔸]

/-- The log series is summable on the unit ball: each term is dominated by the geometric series.
This avoids the radius API, which would need `‖1‖ = 1`. -/
private lemma summable_logCoeff_smul (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable fun i : ℕ => logCoeff i • x ^ i :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx)
    (norm_logCoeff_smul_pow_le x)

/-- `log (1 + x)` is the partial sum through degree `n - 1` plus the tail of the log series. -/
theorem log_one_add_eq_logPartialSum_add_tsum (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    log (1 + x) = logPartialSum 𝔸 n x
      + ∑' k : ℕ, logCoeff (k + n) • x ^ (k + n) := by
  have hS := summable_logCoeff_smul x hx
  rw [congrFun (log_eq_tsum ℚ) (1 + x), add_sub_cancel_left]
  exact (hS.sum_add_tsum_nat_add n).symm

/-- **The `n`-th remainder of `log (1 + ·)` is bounded by `‖x‖ ^ n · (1 - ‖x‖)⁻¹`.**
Each term satisfies `‖logCoeff i • x ^ i‖ ≤ ‖x‖ ^ i`, including the vanishing constant term.
Summing these bounds gives the geometric tail. At `n = 0`, the statement bounds the norm of
`log (1 + x)` itself.

This is the parametrized form of the nine arity-indexed lemmas of
`Lean-BCH/BCH/LogSeries.lean` (`norm_logOnePlus_le` and the `norm_logOnePlus_sub_…_le` chain
through order nine). Only `‖cᵢ‖ = 1/i ≤ 1` enters, so no arithmetic identity of the coefficients
is used, and the dominating series is the geometric one. -/
theorem norm_log_one_add_sub_logPartialSum_le (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - logPartialSum 𝔸 n x‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹ := by
  rw [log_one_add_eq_logPartialSum_add_tsum x n hx, add_sub_cancel_left]
  exact norm_logSeries_tail_le x hx

/-- **`log (1 + x)` is bounded by `1 / (1 - ‖x‖)` on the unit ball.** -/
theorem norm_log_one_add_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x)‖ ≤ 1 / (1 - ‖x‖) := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 0 hx
  rw [logPartialSum_zero, sub_zero, pow_zero, one_mul] at h
  simpa only [one_div] using h

/-- `‖log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 2 hx
  rwa [logPartialSum_two] at h

/-- `‖log (1 + x) - x + x²/2‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_add_sq_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ := by
  simpa only [logPartialSum_three, sub_eq_add_neg, neg_add, neg_neg, add_assoc] using
    norm_log_one_add_sub_logPartialSum_le x 3 hx

/-- `‖log (1 + x) - x + x²/2 - x³/3‖ ≤ ‖x‖ ^ 4 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_add_sq_sub_cube_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2 - (3 : ℚ)⁻¹ • x ^ 3‖
      ≤ ‖x‖ ^ 4 * (1 - ‖x‖)⁻¹ := by
  simpa only [logPartialSum_four, sub_eq_add_neg, neg_add, neg_neg, add_assoc] using
    norm_log_one_add_sub_logPartialSum_le x 4 hx

end PartialSumNorm

/-! ### The derivative at the center

The derivative is read off the power series rather than computed: the differential of a power series
at its center is its linear coefficient, and the linear coefficient of the log series is the
identity. -/

section Deriv

variable [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- **The linear coefficient of the log series is the identity.** -/
@[simp]
theorem continuousMultilinearCurryFin1_logSeries_apply_one :
    continuousMultilinearCurryFin1 ℚ 𝔸 𝔸 (logSeries ℚ 𝔸 1) = 1 := by
  ext y
  rw [one_apply_eq_self, continuousMultilinearCurryFin1_apply, Fin.snoc_zero]
  exact logSeries_apply_one y

/-- **The first coefficient of the log series, as a multilinear map.** Restates
`continuousMultilinearCurryFin1_logSeries_apply_one` in the uncurried form used when composing with
another series. -/
theorem logSeries_apply_one_const (v : 𝔸) :
    (logSeries ℚ 𝔸) 1 (fun _ : Fin 1 => v) = v :=
  logSeries_apply_one v

/-! #### The differential at `1`

Completeness and `‖1‖ = 1` enter only in the identification of the differential with the linear
coefficient, so they are introduced only for the following declarations. -/

variable [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **`log` is strictly differentiable at `1`, with derivative the identity.** Counterpart of
`hasStrictFDerivAt_exp_zero_of_radius_pos`. -/
theorem hasStrictFDerivAt_log_one :
    HasStrictFDerivAt (log : 𝔸 → 𝔸) (1 : 𝔸 →L[ℚ] 𝔸) 1 := by
  have hf : HasFPowerSeriesAt (log : 𝔸 → 𝔸) (logSeries ℚ 𝔸) 1 := log_hasFPowerSeriesAt_one
  simpa only [hf.fderiv_eq, continuousMultilinearCurryFin1_logSeries_apply_one] using
    hf.analyticAt.hasStrictFDerivAt

/-- **`log` has derivative the identity at `1`.** Counterpart of
`hasFDerivAt_exp_zero_of_radius_pos`. -/
theorem hasFDerivAt_log_one :
    HasFDerivAt (log : 𝔸 → 𝔸) (1 : 𝔸 →L[ℚ] 𝔸) 1 :=
  hasStrictFDerivAt_log_one.hasFDerivAt

end Deriv

/-! ### The exponential of the logarithm

We prove `exp (log (1 + x)) = 1 + x` for `‖x‖ < 1` by showing that
`t ↦ exp (-log (1 + t • x)) * (1 + t • x)` is constant on `[0, 1]`.

Term-by-term differentiation gives
`Dₓ(t) = ∑' n, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)`
as the derivative of `t ↦ log (1 + t • x)`. The geometric-series identity gives
`Dₓ(t) * (1 + t • x) = x`, so the derivative of the product vanishes. Its value at `t = 0` is `1`.

Values of `t ↦ log (1 + t • x)` commute. This allows the derivative of the exponential along the
curve to be obtained from its derivative at `0` using
`exp (f s) = exp (f t) * exp (f s - f t)`.

The real scalar structure used by the curve is constructed internally from completeness and the
normed rational algebra structure. -/

section ExpLog

variable [NormedRing 𝔸]

/-- The dominating series for the term-wise derivatives is summable when `r ‖x‖ < 1`. -/
private lemma summable_logTerm_deriv_bound (x : 𝔸) {r : ℝ} (hr : 0 < r) (hrx : r * ‖x‖ < 1) :
    Summable fun n : ℕ => r ^ n * ‖x‖ ^ (n + 1) :=
  ((summable_geometric_of_lt_one (mul_nonneg hr.le (norm_nonneg x)) hrx).mul_left
    ‖x‖).congr fun n => by ring

variable [NormedAlgebra ℝ 𝔸]

/-- **The log series along the curve `s ↦ s • x` as an explicit `tsum`.**

`log (1 + s • x) = ∑' n, ((-1)^(n+1)/n) • (s • x)^n`, which is `log_eq_tsum` with the center
shifted. This is the form in which the term-by-term differentiation is stated; the `n = 0` term
vanishes, its coefficient being `(-1)/0 = 0`, so no reindexing is needed. -/
private lemma log_one_add_smul_eq_tsum (x : 𝔸) (s : ℝ) :
    log (1 + s • x) = ∑' n : ℕ, (((-1 : ℝ) ^ (n + 1) / n) • (s • x) ^ n) := by
  rw [congrFun (log_eq_tsum ℝ) (1 + s • x), add_sub_cancel_left]

/-- Term-by-term derivative of the log series along `s ↦ s • x`. -/
private lemma hasDerivAt_logTerm_smul (x : 𝔸) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • (s • x) ^ (n + 1))
      (((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) t := by
  have heq : (fun s : ℝ => ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • (s • x) ^ (n + 1)) =
      fun s : ℝ => (((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) * s ^ (n + 1)) • x ^ (n + 1) := by
    ext s
    rw [smul_pow, smul_smul]
  rw [heq]
  exact ((hasDerivAt_pow (n + 1) t).const_mul
    ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹))).smul_const (x ^ (n + 1)) |>.congr_deriv (by
    congr 1
    rw [show n + 1 - 1 = n from by lia]
    field_simp
    push_cast
    ring)

/-- The series of logarithm terms is summable at `t = 0`, where every term vanishes. -/
private lemma summable_logTerm_smul_zero (x : 𝔸) :
    Summable fun n : ℕ => ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • ((0 : ℝ) • x) ^ (n + 1) := by
  simpa only [zero_smul, zero_pow (Nat.succ_ne_zero _), smul_zero] using
    (summable_zero : Summable (fun _ : ℕ => (0 : 𝔸)))

/-- **Two points of the curve `s ↦ log (1 + s • x)` commute**: both are limits of polynomials in
`x`. -/
private lemma commute_log_one_add_smul (x : 𝔸) (t s : ℝ) :
    Commute (log (1 + t • x)) (log (1 + s • x)) :=
  (((Commute.one_left (1 + s • x)).add_left
    ((Commute.one_right (t • x)).add_right
      (((Commute.refl x).smul_left t).smul_right s)))).log

/-- Uniform bound for the term-wise derivative on `Ioo (-r) r`. -/
private lemma norm_hasDerivAt_logTerm_le (x : 𝔸) (n : ℕ) {r : ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (-r) r) :
    ‖((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)‖ ≤ r ^ n * ‖x‖ ^ (n + 1) := by
  have htabs : |t| < r := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  calc ‖((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)‖
      ≤ ‖(-1 : ℝ) ^ n * t ^ n‖ * ‖x ^ (n + 1)‖ := norm_smul_le _ _
    _ = |t| ^ n * ‖x ^ (n + 1)‖ := by
        congr 1
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    _ ≤ |t| ^ n * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos n))
          (pow_nonneg (abs_nonneg t) n)
    _ ≤ r ^ n * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) htabs.le n)
          (pow_nonneg (norm_nonneg x) (n + 1))

variable [CompleteSpace 𝔸]

/-- **The derivative series cancels the factor `1 + t • x` on the right.** -/
private lemma log_one_add_smul_deriv_mul (x : 𝔸) (t : ℝ) (ht : |t| * ‖x‖ < 1) :
    (∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) * (1 + t • x) = x := by
  have htx : ‖-(t • x)‖ < 1 := by rwa [norm_neg, norm_smul, Real.norm_eq_abs]
  have hgeom := summable_geometric_of_norm_lt_one htx
  have hseries : (∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) =
      (∑' n : ℕ, (-(t • x)) ^ n) * x := by
    calc _ = ∑' n : ℕ, (-(t • x)) ^ n * x := tsum_congr fun n => by
          conv_rhs => rw [show -(t • x) = (-t) • x from (neg_smul t x).symm, smul_pow,
            smul_mul_assoc, ← pow_succ, neg_pow]
      _ = (∑' n : ℕ, (-(t • x)) ^ n) * x := hgeom.tsum_mul_right x
  rw [hseries, mul_assoc,
    ((Commute.one_right x).add_right ((Commute.refl x).smul_right t)).eq,
    ← mul_assoc, show (1 : 𝔸) + t • x = 1 - -(t • x) from by simp,
    geom_series_mul_neg _ htx, one_mul]

section ExpLogDerivative

variable [NormOneClass 𝔸]

/-- **The log series along the curve, reindexed to start at the linear term**,
`log (1 + s • x) = ∑' n, ((-1)^n / (n+1)) • (s • x)^(n+1)`: the `0`-th term of the unshifted form
vanishes, so this is `Summable.tsum_eq_zero_add`. -/
private lemma log_one_add_smul_eq_tsum' (x : 𝔸) (s : ℝ) (hs : ‖s • x‖ < 1) :
    log (1 + s • x) = ∑' n : ℕ, (((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • (s • x) ^ (n + 1)) := by
  have hsumm : Summable fun n : ℕ => ((-1 : ℝ) ^ (n + 1) / n) • (s • x) ^ n :=
    logSeries_summable_of_mem_ball' _ (mem_eball_logSeries_radius_real hs)
  have hzero : ((-1 : ℝ) ^ (0 + 1) / ((0 : ℕ) : ℝ)) • (s • x) ^ 0 = 0 := by simp
  rw [log_one_add_smul_eq_tsum x s, hsumm.tsum_eq_zero_add, hzero, zero_add]
  refine tsum_congr fun n => ?_
  rw [show n + 1 + 1 = n + 2 from rfl, pow_add, show ((-1 : ℝ) ^ 2) = 1 by norm_num, mul_one,
    div_eq_mul_inv, Nat.cast_add, Nat.cast_one]

/-- **The derivative of `s ↦ log (1 + s • x)` at any point of the unit ball**, as the `tsum` of the
term-wise derivatives. -/
private lemma hasDerivAt_log_one_add_smul_tsum (x : 𝔸) (t : ℝ) (ht : |t| * ‖x‖ < 1) :
    HasDerivAt (fun s : ℝ => log (1 + s • x))
      (∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) t := by
  obtain ⟨δ, hδ, hδx⟩ := exists_pos_mul_lt (sub_pos.mpr ht) ‖x‖
  obtain ⟨r, htr, hrx⟩ : ∃ r : ℝ, |t| < r ∧ r * ‖x‖ < 1 :=
    ⟨|t| + δ, by linarith, by nlinarith⟩
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (abs_nonneg t) htr
  have htsum : HasDerivAt (fun s : ℝ => ∑' n : ℕ,
      ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • (s • x) ^ (n + 1))
      (∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1)) t :=
    hasDerivAt_tsum_of_isPreconnected (summable_logTerm_deriv_bound x hr0 hrx) isOpen_Ioo
      isPreconnected_Ioo (fun n s _ => hasDerivAt_logTerm_smul x n s)
      (fun n s hs => norm_hasDerivAt_logTerm_le x n hs) ⟨by linarith, by linarith⟩
      (summable_logTerm_smul_zero x)
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  refine htsum.congr_of_eventuallyEq ?_
  have hopen : IsOpen {s : ℝ | ‖s • x‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds (by simpa only [Set.mem_ofPred_eq, norm_smul,
    Real.norm_eq_abs] using ht)] with s hs
  exact log_one_add_smul_eq_tsum' x s hs

end ExpLogDerivative

variable [NormedAlgebra ℚ 𝔸]

/-- **The chain rule for `exp` along a curve whose increment commutes with the value.**

Writing `exp (f s) = exp (f t) * exp (f s - f t)` reduces the derivative of `exp ∘ f` to the
derivative of `exp` at `0`, which is the identity — so no general Fréchet derivative of `exp` is
needed. -/
private lemma hasDerivAt_exp_of_hasDerivAt_commute {f : ℝ → 𝔸} {f' : 𝔸} {t : ℝ}
    (hf : HasDerivAt f f' t) (hcomm : ∀ s : ℝ, Commute (f t) (f s - f t)) :
    HasDerivAt (fun s => exp (f s)) (exp (f t) * f') t := by
  suffices h : HasDerivAt (fun s => exp (f s - f t)) f' t by
    rw [show (fun s => exp (f s)) = fun s => exp (f t) * exp (f s - f t) from by
      ext s
      rw [← exp_add_of_commute (hcomm s)]
      congr 1
      abel]
    exact h.const_mul (exp (f t))
  have hinner : HasDerivAt (fun s => f s - f t) f' t :=
    hf.sub_const (f t)
  have := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).comp_hasDerivAt_of_eq t hinner
    (sub_self (f t)).symm
  simpa only [Function.comp_def, one_apply_eq_self] using this

end ExpLog

section ExpLogMain

variable [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **`exp (log (1 + x)) = 1 + x` for `‖x‖ < 1`.**

The ODE/constancy argument: `Q t = exp (-(log (1 + t • x))) * (1 + t • x)` has `Q 0 = 1` and
`Q' = 0`, because the derivative of `log (1 + t • x)` is the `tsum` whose product with `1 + t • x`
is `x` (`geom_series_mul_neg`). -/
theorem exp_log_one_add (x : 𝔸) (hx : ‖x‖ < 1) : exp (log (1 + x)) = 1 + x := by
  have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸
  suffices h : exp (-(log (1 + x))) * (1 + x) = 1 by
    apply (isUnit_exp (-log (1 + x))).mul_left_cancel
    rw [← exp_add_of_commute (Commute.refl (log (1 + x))).neg_left,
      neg_add_cancel, exp_zero, h]
  let Q : ℝ → 𝔸 := fun t => exp (-(log (1 + t • x))) * (1 + t • x)
  have hQ0 : Q 0 = 1 := by simp [Q]
  have hQ1 : Q 1 = exp (-(log (1 + x))) * (1 + x) := by simp [Q]
  rw [← hQ1, show Q 1 = Q 0 from ?_, hQ0]
  have hQderiv : ∀ t : ℝ, |t| * ‖x‖ < 1 → HasDerivAt Q 0 t := by
    intro t ht
    let L : ℝ → 𝔸 := fun s => log (1 + s • x)
    have hL' := hasDerivAt_log_one_add_smul_tsum x t ht
    have hcomm_exp : ∀ s : ℝ, Commute (-L t) (-L s - -L t) := by
      intro s
      simp only [neg_sub_neg]
      exact (Commute.refl (L t)).neg_left.sub_right (commute_log_one_add_smul x t s).neg_left
    have hexp' := hasDerivAt_exp_of_hasDerivAt_commute hL'.neg hcomm_exp
    have hlin : HasDerivAt (fun s : ℝ => 1 + s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x |>.const_add 1
    refine (hexp'.mul hlin).congr_deriv ?_
    change exp (-L t) * (-(∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1))) *
      (1 + t • x) + exp (-L t) * x = 0
    rw [mul_assoc, neg_mul, ← mul_add, log_one_add_smul_deriv_mul x t ht,
      neg_add_cancel, mul_zero]
  have hQderivOn : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Q 0 t := by
    intro t ht
    apply hQderiv
    rw [abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx
  exact constant_of_has_deriv_right_zero
    (fun t ht => (hQderivOn t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hQderivOn t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt)
    1 (Set.right_mem_Icc.mpr zero_le_one)

/-- **`exp (log y) = y` for `‖y - 1‖ < 1`.** The form of `exp_log_one_add` at center `1`. -/
theorem exp_log {y : 𝔸} (hy : ‖y - 1‖ < 1) : exp (log y) = y := by
  simpa only [← add_sub_assoc, add_sub_cancel_left] using exp_log_one_add (y - 1) hy

end ExpLogMain

end FQFP
