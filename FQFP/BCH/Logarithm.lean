/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential

import FQFP.BCH.RealScalar

/-!
# The Banach-algebra logarithm

`log x = ∑' n, (-1)^(n+1)/n • (x - 1)^n`, built on the pattern of `NormedSpace.expSeries`.

## Design

`NormedSpace.exp` is defined as the sum of the `FormalMultilinearSeries`
`NormedSpace.expSeries ℚ 𝔸`, and its properties are read off that series. This file takes the same
route for the logarithm: `logSeries` is the `FormalMultilinearSeries` whose `n`-th term is
`((-1)^(n+1) / n) • ∏ xᵢ`, and `log` is its sum at `x - 1`, taken at `ℚ` exactly as `exp` is.

Following `exp`, the *definition* needs no norm — `IsTopologicalRing` suffices — so `logSeries` and
`log` are independent of a particular choice of norm. Only the convergence results need one.

The series is the one for `log (1 + t)` at `t = x - 1`, and its constant term vanishes, since
`((-1) : 𝕂) / 0 = 0`; that is what distinguishes it from `expSeries`, where `(0 !)⁻¹ = 1` there.

This mirrors `NormedSpace.log` from
[mathlib4#43670](https://github.com/leanprover-community/mathlib4/pull/43670), with proofs written
independently. The algebraic half here (`logSeries`, `log`, `log_one`, `log_op`, `star_log`,
`log_mem`, `Commute.log_right` and friends) is what that PR provides, so it is expected to become
redundant when the pin moves past it. The analytic half — the radius of convergence, summability,
`HasFPowerSeriesOnBall`, the derivative at `1`, analyticity — is what that PR leaves to later files,
and is the reason this file exists.

## Main definitions

* `logSeries 𝕂 𝔸` — the formal multilinear series `∑ n, ((-1)^(n+1)/n) • ∏ xᵢ`.
* `log x` — its sum at `x - 1`.
* `logCoeff i = (-1)^(i+1)/i` — the `i`-th coefficient of the series, as a function of a *natural*
  index, which keeps the coercions out of the statements below.
* `logPartialSum 𝔸 n x = ∑_{i<n} logCoeff i • xⁱ` — the partial sum whose first omitted term is the
  one of degree `n`.

Statements near `0` are phrased directly as `log (1 + x)`; there is deliberately no separate
origin-centered name for the same function.

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

/-! ### The formal multilinear series -/

/-- `logSeries 𝕂 𝔸` is the `FormalMultilinearSeries` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ ((-1)^(n+1) / n) • ∏ xᵢ`; its `0`-th term is `0` since `(-1)^1 / 0 = 0`. Its sum
evaluated at `x - 1` is `log x`.

Counterpart of `NormedSpace.expSeries`. No norm appears: as for `NormedSpace.exp`,
`IsTopologicalRing` suffices for the definition. -/
def logSeries (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
    [IsTopologicalRing 𝔸] : FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 fun n => ((-1 : 𝕂) ^ (n + 1) / n)

section Series

variable {𝔸 𝕂 : Type*} [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The log series as an `ofScalars` series. -/
theorem logSeries_eq_ofScalars :
    logSeries 𝕂 𝔸 = ofScalars 𝔸 (fun n => (-1 : 𝕂) ^ (n + 1) / n) :=
  rfl

/-- **The `n`-th term on the diagonal.** Counterpart of `NormedSpace.expSeries_apply_eq`. -/
theorem logSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (logSeries 𝕂 𝔸 n fun _ => x) = ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n := by
  simp [logSeries, ofScalars]

/-- Function form of `logSeries_apply_eq`. -/
theorem logSeries_apply_eq' (x : 𝔸) :
    (fun n => logSeries 𝕂 𝔸 n fun _ => x)
      = fun n : ℕ => ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n :=
  funext (logSeries_apply_eq x)

/-- **Every term vanishes at `0`.** Counterpart of `NormedSpace.expSeries_apply_zero`, whose value
is instead the `Pi.single` term. This is what makes `log 1 = 0`. -/
theorem logSeries_apply_zero (n : ℕ) : logSeries 𝕂 𝔸 n (fun _ => (0 : 𝔸)) = 0 := by
  rw [logSeries_apply_eq]
  rcases n with - | n
  · simp
  · rw [zero_pow (Nat.succ_ne_zero n), smul_zero]

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

/-- **The sum as an explicit `tsum`.** Counterpart of `NormedSpace.expSeries_sum_eq`. -/
theorem logSeries_sum_eq (x : 𝔸) :
    (logSeries 𝕂 𝔸).sum x = ∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • x ^ n :=
  tsum_congr fun n => logSeries_apply_eq x n

/-- **The series does not depend on the scalar field.** Counterpart of
`NormedSpace.expSeries_sum_eq_rat`. -/
theorem logSeries_sum_eq_rat [Algebra ℚ 𝔸] : (logSeries 𝕂 𝔸).sum = (logSeries ℚ 𝔸).sum := by
  ext; simp_rw [logSeries_sum_eq, neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]

/-- **The series does not depend on the scalar field, term by term.** Counterpart of
`NormedSpace.expSeries_eq_expSeries_rat`. -/
theorem logSeries_eq_logSeries_rat [Algebra ℚ 𝔸] (n : ℕ) :
    (⇑(logSeries 𝕂 𝔸 n) : (Fin n → 𝔸) → 𝔸) = logSeries ℚ 𝔸 n := by
  ext c
  simp [logSeries, ofScalars, neg_one_pow_div_natCast_smul_eq 𝕂 ℚ]

/-- A version of `logSeries_eq_logSeries_rat` for two arbitrary scalar fields. Counterpart of
`NormedSpace.expSeries_eq_expSeries`. -/
theorem logSeries_eq_logSeries {𝕂' : Type*} [Field 𝕂'] [Algebra 𝕂' 𝔸] (n : ℕ) (x : 𝔸) :
    (logSeries 𝕂 𝔸 n fun _ => x) = logSeries 𝕂' 𝔸 n fun _ => x := by
  rw [logSeries_apply_eq, logSeries_apply_eq, neg_one_pow_div_natCast_smul_eq 𝕂 𝕂']

end Series

/-! ### The logarithm -/

section Log

variable {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

open scoped Classical in
/-- `log : 𝔸 → 𝔸` is the logarithm `log x = ∑' n, (-1)^(n+1)/n • (x - 1)^n`, defined as the sum of
the `FormalMultilinearSeries` `logSeries ℚ 𝔸` at `x - 1`, following `NormedSpace.exp`.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `0`. -/
noncomputable irreducible_def log (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (logSeries ℚ 𝔸).sum (x - 1)
  else
    0

/-- The junk value. Counterpart of `NormedSpace.exp_of_isEmpty_algebra_rat`. -/
@[simp]
theorem log_of_isEmpty_algebra_rat [IsEmpty (Algebra ℚ 𝔸)] (x : 𝔸) : log x = 0 := by
  rw [log, dite_eq_right (not_nonempty_iff.mpr ‹IsEmpty (Algebra ℚ 𝔸)›)]

section General

variable {𝕂 : Type*} [Field 𝕂] [Algebra 𝕂 𝔸]

variable (𝕂) in
/-- **`log` as the sum of its series.** Counterpart of `NormedSpace.exp_eq_expSeries_sum`. -/
theorem log_eq_logSeries_sum [CharZero 𝕂] :
    log = fun x : 𝔸 => (logSeries 𝕂 𝔸).sum (x - 1) := by
  ext x
  rw [log, dite_eq_left ⟨RestrictScalars.algebra ℚ 𝕂 𝔸⟩, ← @logSeries_sum_eq_rat (𝕂 := 𝕂)]

variable (𝕂) in
/-- **`log` as an explicit `tsum`.** Counterpart of `NormedSpace.exp_eq_tsum`. -/
theorem log_eq_tsum [CharZero 𝕂] :
    log = fun x : 𝔸 => ∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • (x - 1) ^ n := by
  simp_rw [log_eq_logSeries_sum 𝕂, logSeries_sum_eq]

end General

/-- **`log 1 = 0`.** The constant term of the log series vanishes, so the sum at the center is `0`.
Counterpart of `NormedSpace.exp_zero`; this is the center condition `HasFPowerSeriesAt.comp` needs
when composing with `exp`. -/
@[simp]
theorem log_one : log (1 : 𝔸) = 0 := by
  rw [log]
  split_ifs with h
  · let inst : Algebra ℚ 𝔸 := h.some
    change (logSeries ℚ 𝔸).sum (1 - 1) = 0
    rw [sub_self, logSeries_sum_eq]
    rw [show (fun n : ℕ => ((-1 : ℚ) ^ (n + 1) / n) • (0 : 𝔸) ^ n) = fun _ => 0 from
      funext fun n => by rw [← logSeries_apply_eq]; exact logSeries_apply_zero n]
    exact tsum_zero
  · rfl

/-- **`log` commutes with the opposite ring.** Counterpart of `NormedSpace.exp_op`. -/
@[simp]
theorem log_op [T2Space 𝔸] (x : 𝔸) :
    log (MulOpposite.op x) = MulOpposite.op (log x) := by
  obtain h | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · have : IsEmpty (Algebra ℚ 𝔸ᵐᵒᵖ) := ⟨fun _ => h.elim <| (RingEquiv.opOp 𝔸).algebra ℚ⟩
    simp
  · rw [log_eq_tsum ℚ, log_eq_tsum ℚ]
    simp_rw [← MulOpposite.op_one, ← MulOpposite.op_sub, ← MulOpposite.op_pow,
      ← MulOpposite.op_smul, tsum_op]

/-- **`log` commutes with `star`.** Counterpart of `NormedSpace.star_exp`. -/
theorem star_log [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 𝔸] (x : 𝔸) :
    star (log x) = log (star x) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · simp [log_eq_tsum ℚ, tsum_star]

/-- A subring of `𝔸` that is closed topologically and under `ℚ`-scaling is closed under `log`.
Counterpart of `NormedSpace.exp_mem`, which needs only a `SubsemiringClass`; `log` subtracts `1`,
so closure under negation is required here. -/
theorem log_mem
    {R S : Type*} [Monoid R] [SMul ℚ R] [MulAction R 𝔸] [Algebra ℚ 𝔸] [IsScalarTower ℚ R 𝔸]
    [SetLike S 𝔸] [SubringClass S 𝔸] [SMulMemClass S R 𝔸] {s : S}
    (h_closed : IsClosed (s : Set 𝔸)) {x : 𝔸} (h : x ∈ s) : log x ∈ s := by
  have := SMulMemClass.ofIsScalarTower S ℚ R 𝔸
  rw [log_eq_tsum ℚ]
  exact tsum_mem h_closed fun i => SMulMemClass.smul_mem _ <| pow_mem (sub_mem h (one_mem s)) _

end Log

/-! ### `Commute`

These mirror `Commute.exp_right` and friends. They live in the root `Commute` namespace because
that is where dot notation for `h.log_right` resolves, matching `NormedSpace`'s treatment of `exp`
and upstream's treatment of `log` in mathlib4#43670. -/

section Commute

variable {𝔸 : Type*} [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

theorem _root_.Commute.log_right [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute x (log y) := by
  obtain _ | ⟨⟨_⟩⟩ := isEmpty_or_nonempty (Algebra ℚ 𝔸)
  · simp
  · rw [log_eq_tsum ℚ]
    exact Commute.tsum_right x fun n =>
      ((h.sub_right (Commute.one_right x)).pow_right n).smul_right _

theorem _root_.Commute.log_left [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (log x) y :=
  h.symm.log_right.symm

theorem _root_.Commute.log [T2Space 𝔸] {x y : 𝔸} (h : Commute x y) :
    Commute (log x) (log y) :=
  h.log_left.log_right

end Commute

/-! ### The radius of convergence

Unlike `expSeries`, whose radius is infinite (`expSeries_radius_eq_top`), the log series has radius
`1`: its coefficients are `1/n`, so the ratio test tends to `1`.

The coefficient norms and the ratio tests mention only `ℚ` and `ℝ`, so they carry no algebra
variables at all. The radius itself is then computed separately over the two scalar fields, since
`logSeries ℚ 𝔸` and `logSeries ℝ 𝔸` are different series: the ODE route below differentiates along a
real parameter and so needs the `ℝ` one, while `log` itself is defined through the `ℚ` one. -/

section CoeffNorm

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
  have key : ∀ n : ℕ, 0 < n →
      ‖((-1 : ℚ) ^ (n + 1) / n)‖ / ‖((-1 : ℚ) ^ (n + 1 + 1) / (n + 1))‖
        = ((n : ℝ) + 1) / (n : ℝ) := by
    intro n _
    have hnext : ‖((-1 : ℚ) ^ (n + 1 + 1) / (n + 1))‖ = ((n : ℝ) + 1)⁻¹ := by
      simpa using norm_logSeries_coeff (n + 1)
    rw [norm_logSeries_coeff n, hnext, div_eq_mul_inv, inv_inv]
    ring
  have hlim : Tendsto (fun n : ℕ => (((n : ℝ) / ((n : ℝ) + 1))⁻¹)) atTop (𝓝 1) := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1
    simpa using hbase.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)
  have hlim' : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    simpa [inv_div] using hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [Nat.succ_eq_add_one] using (key n hn).symm

/-- **The ratio of consecutive coefficient norms tends to `1`**, over `ℝ`. The two coefficient norms
are the same function of `n`, so this follows from the `ℚ` statement by rewriting. -/
theorem tendsto_norm_logSeries_coeff_ratio_real :
    Tendsto (fun n : ℕ => ‖((-1 : ℝ) ^ (n + 1) / n)‖ / ‖((-1 : ℝ) ^ (n.succ + 1) / n.succ)‖)
      atTop (𝓝 1) := by
  simpa only [norm_logSeries_coeff, norm_logSeries_coeff_real] using
    tendsto_norm_logSeries_coeff_ratio

end CoeffNorm

section Radius

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]

/-- **The radius of `logSeries ℚ 𝔸` is `1`.** Counterpart of `expSeries_radius_eq_top`. -/
theorem logSeries_radius_eq_one : (logSeries ℚ 𝔸).radius = 1 := by
  rw [logSeries_eq_ofScalars]
  convert FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (E := 𝔸)
    (fun n : ℕ => ((-1 : ℚ) ^ (n + 1) / n)) (r := 1) one_ne_zero
    tendsto_norm_logSeries_coeff_ratio using 1

end Radius

section RadiusReal

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]

/-- **The radius of `logSeries ℝ 𝔸` is `1`.** Counterpart of `logSeries_radius_eq_one`. -/
theorem logSeries_radius_eq_one_real : (logSeries ℝ 𝔸).radius = 1 := by
  rw [logSeries_eq_ofScalars]
  convert FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (E := 𝔸)
    (fun n : ℕ => ((-1 : ℝ) ^ (n + 1) / n)) (r := 1) one_ne_zero
    tendsto_norm_logSeries_coeff_ratio_real using 1

end RadiusReal

/-! ### Summability inside the ball

`logSeries` is an `ofScalars` series like `expSeries`, so summability inside the ball is read off
`FormalMultilinearSeries.summable_norm_apply`. Unlike `expSeries`, whose radius is infinite, these
are the only summability statements available here: there is no counterpart of `expSeries_summable`
without the ball hypothesis. -/

section Summable

variable {𝔸 𝕂 : Type*} [NontriviallyNormedField 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

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

section CompleteAlgebra

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

end CompleteAlgebra

end Summable

/-! ### The power series

`log` is the sum of its own power series on the open unit ball around `1`. Unlike `exp`, whose ball
of convergence is everything (`exp_hasFPowerSeriesOnBall`), the ball here is genuinely bounded: the
series diverges at `x = 2`. -/

section BallHasSum

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- **`log (1 + x)` is the sum of the log series inside the unit ball.** Counterpart of
`expSeries_hasSum_exp_of_mem_ball`; this is where `log` is identified with the sum of `logSeries`,
and hence where the two `ℚ`-algebra structures meet. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries ℚ 𝔸).radius) :
    HasSum (fun n => logSeries ℚ 𝔸 n fun _ => x) (log (1 + x)) := by
  simpa only [← logSeries_sum_eq x, congrFun (log_eq_tsum ℚ) (1 + x), add_sub_cancel_left] using
    FormalMultilinearSeries.hasSum (logSeries ℚ 𝔸) hx

/-- Diagonal form of `logSeries_hasSum_log_one_add_of_mem_ball`. Counterpart of
`expSeries_hasSum_exp_of_mem_ball'`. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball' (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries ℚ 𝔸).radius) :
    HasSum (fun n : ℕ => ((-1 : ℚ) ^ (n + 1) / n) • x ^ n) (log (1 + x)) := by
  rw [← logSeries_apply_eq']
  exact logSeries_hasSum_log_one_add_of_mem_ball x hx

end BallHasSum

section BallRadius

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]

/-- Any point of the open unit ball lies inside the radius of convergence. -/
theorem mem_eball_logSeries_radius {x : 𝔸} (hx : ‖x‖ < 1) :
    x ∈ Metric.eball (0 : 𝔸) (logSeries ℚ 𝔸).radius := by
  rw [mem_eball_zero_iff, logSeries_radius_eq_one, ← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hx

end BallRadius

section Ball

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- **`log` is the sum of its power series on the open unit ball around `1`.** Counterpart of
`exp_hasFPowerSeriesOnBall`, whose ball is instead all of `𝔸`. -/
theorem log_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall log (logSeries ℚ 𝔸) 1 1 where
  r_le := by rw [logSeries_radius_eq_one]
  r_pos := by norm_num
  hasSum := fun {y} hy => by
    have hy' : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] at hy
      exact hy
    exact logSeries_hasSum_log_one_add_of_mem_ball (𝔸 := 𝔸) y
      (mem_eball_logSeries_radius hy')

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

The `ℝ` counterpart of the power series used above, recentered at `0`. It is what the derivative
along a real parameter is read off. -/

section BallRealHasSum

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **`log (1 + x)` is the sum of the `ℝ`-series inside the unit ball.** Counterpart of
`logSeries_hasSum_log_one_add_of_mem_ball`, which is over `ℚ`; the sums agree because
`logSeries_sum_eq_rat` compares the two series and `log` is defined through the `ℚ` one. -/
theorem logSeries_hasSum_log_one_add_of_mem_ball_real (x : 𝔸)
    (hx : x ∈ Metric.eball (0 : 𝔸) (logSeries ℝ 𝔸).radius) :
    HasSum (fun n => logSeries ℝ 𝔸 n fun _ => x) (log (1 + x)) := by
  simpa only [← logSeries_sum_eq_rat (𝕂 := ℝ), congrFun (log_eq_logSeries_sum ℚ) (1 + x),
    add_sub_cancel_left] using FormalMultilinearSeries.hasSum (logSeries ℝ 𝔸) hx

end BallRealHasSum

section BallRealRadius

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]

/-- Any point of the open unit ball lies inside the radius of convergence, over `ℝ`. -/
theorem mem_eball_logSeries_radius_real {x : 𝔸} (hx : ‖x‖ < 1) :
    x ∈ Metric.eball (0 : 𝔸) (logSeries ℝ 𝔸).radius := by
  rw [mem_eball_zero_iff, logSeries_radius_eq_one_real, ← ofReal_norm, ENNReal.ofReal_lt_one]
  exact hx

end BallRealRadius

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

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- The coefficients of the log series: `logCoeff i = (-1)^(i+1)/i`, so that
`log (1 + x) = ∑ᵢ logCoeff i • xⁱ`. Naming them keeps the coercions out of the statements below,
where `logCoeff` is only ever applied to a *natural-number* index. -/
noncomputable def logCoeff (i : ℕ) : ℚ := (-1 : ℚ) ^ (i + 1) / i

@[simp] theorem logCoeff_zero : logCoeff 0 = 0 := by norm_num [logCoeff]
@[simp] theorem logCoeff_one : logCoeff 1 = 1 := by norm_num [logCoeff]
@[simp] theorem logCoeff_two : logCoeff 2 = -(2 : ℚ)⁻¹ := by norm_num [logCoeff]
@[simp] theorem logCoeff_three : logCoeff 3 = (3 : ℚ)⁻¹ := by norm_num [logCoeff]

/-- **The log coefficients have norm at most `1`.** -/
theorem norm_logCoeff_le_one (i : ℕ) : ‖logCoeff i‖ ≤ 1 := by
  rw [logCoeff, norm_logSeries_coeff]
  rcases Nat.eq_zero_or_pos i with h | h
  · rw [h]; norm_num
  · rw [inv_le_one₀ (by positivity)]
    exact_mod_cast (Nat.succ_le_iff.mpr h)

/-- The partial sum `∑_{i<n} logCoeff i • xⁱ` of the log series. The subscript `n` is the degree of
the *first omitted* term, which is what makes it line up with the split point of
`Summable.sum_add_tsum_nat_add`: `logPartialSum 𝔸 0 x = 0`, `logPartialSum 𝔸 1 x = 0` (the constant
coefficient is `(-1)/0 = 0`), `logPartialSum 𝔸 2 x = x`, `logPartialSum 𝔸 3 x = x - x²/2`. -/
noncomputable def logPartialSum (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (n : ℕ)
    (x : 𝔸) : 𝔸 :=
  ∑ i ∈ Finset.range n, logCoeff i • x ^ i

@[simp]
theorem logPartialSum_zero (x : 𝔸) : logPartialSum 𝔸 0 x = 0 :=
  Finset.sum_range_zero _

/-- **A tail of the log series is bounded by the geometric tail of `x`.** The `k`-th term is
`logCoeff (k + n) • x^(k + n)`, and `‖logCoeff i‖ ≤ 1`. -/
private lemma norm_logSeries_tail_le (x : 𝔸) {n : ℕ} (hx : ‖x‖ < 1) :
    ‖∑' k : ℕ, logCoeff (k + n) • x ^ (k + n)‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹ := by
  have hterm : ∀ k : ℕ, ‖logCoeff (k + n) • x ^ (k + n)‖ ≤ ‖x‖ ^ n * ‖x‖ ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos (k + n) with hzero | hpos
    · -- `k + n = 0`: the coefficient is `(-1)/0 = 0`, so the term vanishes.
      have hk : k = 0 := by lia
      have hn : n = 0 := by lia
      subst hk; subst hn
      simp
    · -- Otherwise `norm_pow_le'` applies; `norm_pow` would need `‖1‖ = 1`, which a bare
      -- `NormedRing` does not supply, and the inequality is all that is used here.
      calc ‖logCoeff (k + n) • x ^ (k + n)‖
          = ‖logCoeff (k + n)‖ * ‖x ^ (k + n)‖ := norm_smul _ _
        _ ≤ 1 * ‖x‖ ^ (k + n) :=
            mul_le_mul (norm_logCoeff_le_one (k + n)) (norm_pow_le' x hpos) (norm_nonneg _)
              (by norm_num)
        _ = ‖x‖ ^ n * ‖x‖ ^ k := by rw [one_mul, pow_add]; ring
  exact tsum_of_norm_bounded
    (f := fun k : ℕ => logCoeff (k + n) • x ^ (k + n))
    ((hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖ ^ n)) hterm

end PartialSum

section PartialSumTsum

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- The log series is summable on the unit ball: each term is dominated by the geometric series.
This avoids the radius API, which would need `‖1‖ = 1`. -/
private lemma summable_logCoeff_smul (x : 𝔸) (hx : ‖x‖ < 1) :
    Summable fun i : ℕ => logCoeff i • x ^ i := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx) fun i => ?_
  rcases Nat.eq_zero_or_pos i with hzero | hpos
  · subst hzero; simp
  · calc ‖logCoeff i • x ^ i‖ = ‖logCoeff i‖ * ‖x ^ i‖ := norm_smul _ _
      _ ≤ 1 * ‖x‖ ^ i :=
          mul_le_mul (norm_logCoeff_le_one i) (norm_pow_le' x hpos) (norm_nonneg _) (by norm_num)
      _ = ‖x‖ ^ i := one_mul _

/-- `log (1 + x)` is the partial sum through degree `n - 1` plus the tail of the log series. -/
theorem log_one_add_eq_logPartialSum_add_tsum (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    log (1 + x) = logPartialSum 𝔸 n x
      + ∑' k : ℕ, logCoeff (k + n) • x ^ (k + n) := by
  have hS := summable_logCoeff_smul x hx
  rw [congrFun (log_eq_tsum ℚ) (1 + x), add_sub_cancel_left]
  exact (hS.sum_add_tsum_nat_add n).symm

/-- **The `n`-th remainder of `log (1 + ·)` is bounded by `‖x‖ ^ n · (1 - ‖x‖)⁻¹`.**
For `n ≥ 1` the first omitted term is `cₙ • xⁿ`, of norm `(1/n) ‖x‖ⁿ ≤ ‖x‖ⁿ`, and the remaining
tail is smaller by at least the factor `n/(n+1)`; both are dominated by the geometric tail of
`x`. At `n = 0` the statement is the bound `‖log (1 + x)‖ ≤ (1 - ‖x‖)⁻¹` on the function itself.

This is the parametrized form of the nine arity-indexed lemmas of
`Lean-BCH/BCH/LogSeries.lean` (`norm_logOnePlus_le` and the `norm_logOnePlus_sub_…_le` chain
through order nine). Only `‖cᵢ‖ = 1/i ≤ 1` enters, so no arithmetic identity of the coefficients
is used, and the dominating series is the geometric one. -/
theorem norm_log_one_add_sub_logPartialSum_le (x : 𝔸) (n : ℕ) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - logPartialSum 𝔸 n x‖ ≤ ‖x‖ ^ n * (1 - ‖x‖)⁻¹ := by
  rw [log_one_add_eq_logPartialSum_add_tsum x n hx, add_sub_cancel_left]
  exact norm_logSeries_tail_le x hx

end PartialSumTsum

section PartialSumExplicit

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- The first partial sum of the log series vanishes: its constant coefficient is `(-1)/0 = 0`. -/
@[simp]
theorem logPartialSum_one (x : 𝔸) : logPartialSum 𝔸 1 x = 0 := by
  rw [logPartialSum, Finset.sum_range_one, logCoeff_zero, zero_smul]

/-- The second partial sum of the log series is the linear term `x`. -/
@[simp]
theorem logPartialSum_two (x : 𝔸) : logPartialSum 𝔸 2 x = x := by
  rw [logPartialSum, Finset.sum_range_succ, Finset.sum_range_one, logCoeff_zero, zero_smul,
    zero_add, logCoeff_one, one_smul, pow_one]

/-- The third partial sum of the log series is `x - x²/2`. -/
@[simp]
theorem logPartialSum_three (x : 𝔸) :
    logPartialSum 𝔸 3 x = x - (2 : ℚ)⁻¹ • x ^ 2 := by
  rw [logPartialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    logCoeff_zero, logCoeff_one, logCoeff_two, zero_smul, one_smul, zero_add, pow_one, pow_two,
    neg_smul, sub_eq_add_neg]

/-- The fourth partial sum of the log series is `x - x²/2 + x³/3`. -/
@[simp]
theorem logPartialSum_four (x : 𝔸) :
    logPartialSum 𝔸 4 x = x - (2 : ℚ)⁻¹ • x ^ 2 + (3 : ℚ)⁻¹ • x ^ 3 := by
  rw [logPartialSum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, logCoeff_zero, logCoeff_one, logCoeff_two, logCoeff_three,
    zero_smul, one_smul, zero_add, pow_one, pow_two, pow_succ, neg_smul, sub_eq_add_neg]

end PartialSumExplicit

section PartialSumBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- **`log (1 + x)` is bounded by `1 / (1 - ‖x‖)` on the unit ball.** -/
theorem norm_log_one_add_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x)‖ ≤ 1 / (1 - ‖x‖) := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 0 hx
  rw [logPartialSum_zero, sub_zero, pow_zero, one_mul] at h
  rw [one_div]
  exact h

/-- `‖log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x‖ ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 2 hx
  rwa [logPartialSum_two] at h

/-- `‖log (1 + x) - x + x²/2‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_add_sq_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2‖ ≤ ‖x‖ ^ 3 * (1 - ‖x‖)⁻¹ := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 3 hx
  rw [logPartialSum_three] at h
  have hsub : log (1 + x) - (x - (2 : ℚ)⁻¹ • x ^ 2)
      = log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2 := by abel
  rwa [hsub] at h

/-- `‖log (1 + x) - x + x²/2 - x³/3‖ ≤ ‖x‖ ^ 4 * (1 - ‖x‖)⁻¹` for `‖x‖ < 1`. -/
theorem norm_log_one_add_sub_add_sq_sub_cube_le (x : 𝔸) (hx : ‖x‖ < 1) :
    ‖log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2 - (3 : ℚ)⁻¹ • x ^ 3‖
      ≤ ‖x‖ ^ 4 * (1 - ‖x‖)⁻¹ := by
  have h := norm_log_one_add_sub_logPartialSum_le (𝔸 := 𝔸) x 4 hx
  rw [logPartialSum_four] at h
  have hsub : log (1 + x) - (x - (2 : ℚ)⁻¹ • x ^ 2 + (3 : ℚ)⁻¹ • x ^ 3)
      = log (1 + x) - x + (2 : ℚ)⁻¹ • x ^ 2 - (3 : ℚ)⁻¹ • x ^ 3 := by abel
  rwa [hsub] at h

end PartialSumBounds

section BallReal

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
  [NormOneClass 𝔸]

/-- **`x ↦ log (1 + x)` is the sum of `logSeries ℝ 𝔸` at `0`.** -/
theorem hasFPowerSeriesOnBall_log_one_add_real :
    HasFPowerSeriesOnBall (fun y : 𝔸 => log (1 + y)) (logSeries ℝ 𝔸) 0 1 where
  r_le := by rw [logSeries_radius_eq_one_real]
  r_pos := by norm_num
  hasSum := fun {y} hy => by
    have hy' : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] at hy
      exact hy
    simpa only [zero_add] using
      logSeries_hasSum_log_one_add_of_mem_ball_real y (mem_eball_logSeries_radius_real hy')

end BallReal

/-! ### The derivative at the center

The derivative is read off the power series rather than computed: the differential of a power series
at its center is its linear coefficient, and the linear coefficient of the log series is the
identity. -/

section Deriv

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

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
    (logSeries ℚ 𝔸) 1 (fun _ : Fin 1 => v) = v := by
  change continuousMultilinearCurryFin1 ℚ 𝔸 𝔸 (logSeries ℚ 𝔸 1) v = v
  rw [continuousMultilinearCurryFin1_logSeries_apply_one, one_apply_eq_self]

/-! #### The differential at `1`

Completeness and `‖1‖ = 1` enter only in the identification of the differential with the linear
coefficient, so they are confined to this section. -/

section DerivAtOne

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

end DerivAtOne

end Deriv

/-! ### The exponential of the logarithm

The target is `exp (log x) = x` for `‖x - 1‖ < 1`. The route is the ODE one: the curve
`t ↦ exp (-(log (1 + t • x))) * (1 + t • x)` is constant, because the derivative of
`t ↦ log (1 + t • x)` is `(1 + t • x)⁻¹ * x`, and `(1 + t • x)⁻¹ * x * (1 + t • x) = x`, so the
derivative of the product vanishes; at `t = 0` the curve is `exp (-(log 1)) * 1 = 1`.

The derivative of the curve is obtained at a *general* point of the ball by differentiating the
series term by term with `hasDerivAt_tsum_of_isPreconnected`; the general Fréchet derivative of
`exp` is never needed, because `exp (f s) = exp (f t) * exp (f s - f t)` holds for the increment,
whose commutativity is what `commute_log_one_add_smul` supplies.

This follows `Lean-BCH/BCH/LogSeries.lean`, where the same argument is verified in an older setting
(term-wise defined `logOnePlus` over an `RCLike` field). Since the ODE parameter is real, the
differentiability facts are needed over `ℝ`, whereas `logSeries` is taken over `ℚ` (as `log` itself
is); they are therefore read off the `ℝ` power series, `hasFPowerSeriesOnBall_log_one_add_real`.

The sections below are split by hypothesis rather than by topic, so that each lemma carries exactly
the algebra structure it uses and no `omit` is needed: the term-wise lemmas need only the norm and
the `ℝ`-scalar action, the uniform bound for their derivatives additionally needs `‖1‖ = 1`, the
derivative of the `tsum` needs that and completeness, the chain rule for `exp` needs the `ℚ`-scalar
action, and only the main theorem needs everything. -/

section ExpLogBound

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The dominating series for the term-wise derivatives is summable when `r ‖x‖ < 1`. -/
private lemma summable_logTerm_deriv_bound (x : 𝔸) {r : ℝ} (hr : 0 < r) (hrx : r * ‖x‖ < 1) :
    Summable fun n : ℕ => r ^ n * ‖x‖ ^ (n + 1) :=
  ((summable_geometric_of_lt_one (mul_nonneg hr.le (norm_nonneg x)) hrx).mul_left
    ‖x‖).congr fun n => by ring

end ExpLogBound

section ExpLogCurve

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

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

/-- The series of term-wise derivatives is summable at `t = 0`. -/
private lemma summable_logTerm_smul_zero (x : 𝔸) :
    Summable fun n : ℕ => ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • ((0 : ℝ) • x) ^ (n + 1) := by
  have hzero : (fun n : ℕ => ((-1 : ℝ) ^ n * ((n + 1 : ℝ)⁻¹)) • ((0 : ℝ) • x) ^ (n + 1)) =
      fun _ => 0 := by
    ext n
    simp [zero_smul, zero_pow (show n + 1 ≠ 0 by lia)]
  rw [hzero]
  exact summable_zero

/-- **Two points of the curve `s ↦ log (1 + s • x)` commute**: both are limits of polynomials in
`x`. -/
private lemma commute_log_one_add_smul (x : 𝔸) (t s : ℝ) :
    Commute (log (1 + t • x)) (log (1 + s • x)) :=
  (((Commute.one_left (1 + s • x)).add_left
    ((Commute.one_right (t • x)).add_right
      (((Commute.refl x).smul_left t).smul_right s)))).log

end ExpLogCurve

section ExpLogTermBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]

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
        mul_le_mul_of_nonneg_left (norm_pow_le x (n + 1)) (pow_nonneg (abs_nonneg t) n)
    _ ≤ r ^ n * ‖x‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg t) htabs.le n)
          (pow_nonneg (norm_nonneg x) (n + 1))

end ExpLogTermBound

section ExpLogDerivative

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

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
  have hr : ∃ r : ℝ, |t| < r ∧ r * ‖x‖ < 1 := by
    by_cases hx0 : ‖x‖ = 0
    · exact ⟨|t| + 1, by linarith, by simp [hx0]⟩
    · have hxp : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
      exact ⟨(|t| + 1 / ‖x‖) / 2, by linarith [(lt_div_iff₀ hxp).mpr ht, one_div_pos.mpr hxp],
        by rw [div_mul_eq_mul_div]
           linarith [show (|t| + 1 / ‖x‖) * ‖x‖ = |t| * ‖x‖ + 1 from by field_simp]⟩
  obtain ⟨r, htr, hrx⟩ := hr
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

section ExpLogExp

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

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
    (hf.sub (hasDerivAt_const t (f t))).congr_deriv (by simp)
  have := (hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)).comp_hasDerivAt_of_eq t hinner
    (sub_self (f t)).symm
  simpa only [Function.comp_def, one_apply_eq_self] using this

end ExpLogExp

section ExpLogMain

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-- **`exp (log (1 + x)) = 1 + x` for `‖x‖ < 1`.**

The ODE/constancy argument: `Q t = exp (-(log (1 + t • x))) * (1 + t • x)` has `Q 0 = 1` and
`Q' = 0`, because the derivative of `log (1 + t • x)` is the `tsum` whose product with `1 + t • x`
is `x` (`geom_series_mul_neg`). -/
theorem exp_log_one_add (x : 𝔸) (hx : ‖x‖ < 1) : exp (log (1 + x)) = 1 + x := by
  have : NormedAlgebra ℝ 𝔸 := normedAlgebraReal 𝔸
  suffices h : exp (-(log (1 + x))) * (1 + x) = 1 by
    have hinv : exp (log (1 + x)) * exp (-(log (1 + x))) = 1 := by
      rw [← exp_add_of_commute (Commute.neg_right (Commute.refl _)), add_neg_cancel, exp_zero]
    calc exp (log (1 + x)) = exp (log (1 + x)) * 1 := (mul_one _).symm
      _ = exp (log (1 + x)) * (exp (-(log (1 + x))) * (1 + x)) := by rw [h]
      _ = exp (log (1 + x)) * exp (-(log (1 + x))) * (1 + x) := (mul_assoc _ _ _).symm
      _ = 1 * (1 + x) := by rw [hinv]
      _ = 1 + x := one_mul _
  let Q : ℝ → 𝔸 := fun t => exp (-(log (1 + t • x))) * (1 + t • x)
  have hQ0 : Q 0 = 1 := by simp [Q]
  have hQ1 : Q 1 = exp (-(log (1 + x))) * (1 + x) := by simp [Q]
  rw [← hQ1, show Q 1 = Q 0 from ?_, hQ0]
  have hQderiv : ∀ t : ℝ, |t| * ‖x‖ < 1 → HasDerivAt Q 0 t := by
    intro t ht
    set L : ℝ → 𝔸 := fun s => log (1 + s • x) with hL_def
    have hL' := hasDerivAt_log_one_add_smul_tsum x t ht
    have hcomm_exp : ∀ s : ℝ, Commute (-L t) (-L s - -L t) := by
      intro s
      simp only [neg_sub_neg]
      exact (Commute.refl (L t)).neg_left.sub_right (commute_log_one_add_smul x t s).neg_left
    have hexp' := hasDerivAt_exp_of_hasDerivAt_commute hL'.neg hcomm_exp
    have hlin : HasDerivAt (fun s : ℝ => 1 + s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x |>.const_add 1
    have hQ' := hexp'.mul hlin
    set L't : 𝔸 := ∑' n : ℕ, ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1) with hL't_def
    have hgeom : Summable fun n : ℕ => (-(t • x)) ^ n :=
      summable_geometric_of_norm_lt_one (by rwa [norm_neg, norm_smul, Real.norm_eq_abs])
    have hL'_eq : L't = (∑' n : ℕ, (-(t • x)) ^ n) * x := by
      calc L't = ∑' n : ℕ, (-(t • x)) ^ n * x := tsum_congr fun n => by
            show ((-1 : ℝ) ^ n * t ^ n) • x ^ (n + 1) = (-(t • x)) ^ n * x
            conv_rhs => rw [show -(t • x) = (-t) • x from (neg_smul t x).symm, smul_pow,
              smul_mul_assoc, ← pow_succ, neg_pow]
        _ = (∑' n : ℕ, (-(t • x)) ^ n) * x := hgeom.tsum_mul_right x
    have htx : ‖-(t • x)‖ < 1 := by rwa [norm_neg, norm_smul, Real.norm_eq_abs]
    have hcancel : L't * (1 + t • x) = x := by
      rw [hL'_eq, mul_assoc,
        show x * (1 + t • x) = (1 + t • x) * x from
          (Commute.one_right x).add_right ((Commute.refl x).smul_right t),
        ← mul_assoc, show (1 : 𝔸) + t • x = 1 - -(t • x) from by simp,
        geom_series_mul_neg _ htx, one_mul]
    refine hQ'.congr_deriv ?_
    change exp (-L t) * (-L't) * (1 + t • x) + exp (-L t) * x = 0
    rw [mul_assoc, neg_mul, ← mul_add, hcancel, neg_add_cancel, mul_zero]
  by_cases hx0 : x = 0
  · subst hx0
    change Q 1 = Q 0
    simp [Q]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hR : 1 < 1 / ‖x‖ := (one_lt_div₀ hxn).mpr hx
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(1 / ‖x‖)) (1 / ‖x‖) := ⟨by linarith, by linarith⟩
    have h1mem : (1 : ℝ) ∈ Set.Ioo (-(1 / ‖x‖)) (1 / ‖x‖) := ⟨by linarith, by linarith⟩
    have hbound : ∀ t ∈ Set.Ioo (-(1 / ‖x‖)) (1 / ‖x‖), |t| * ‖x‖ < 1 := by
      intro t ht
      have := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
      calc |t| * ‖x‖ < 1 / ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_right this hxn
        _ = 1 := by field_simp
    exact IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo
      (fun t ht => (hQderiv t (hbound t ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => (hQderiv t (hbound t ht)).deriv) h1mem h0mem

/-- **`exp (log y) = y` for `‖y - 1‖ < 1`.** The form of `exp_log_one_add` at center `1`. -/
theorem exp_log {y : 𝔸} (hy : ‖y - 1‖ < 1) : exp (log y) = y := by
  have h := exp_log_one_add (y - 1) hy
  rwa [show (1 : 𝔸) + (y - 1) = y from by rw [add_comm]; exact sub_add_cancel y 1] at h

end ExpLogMain

end FQFP
