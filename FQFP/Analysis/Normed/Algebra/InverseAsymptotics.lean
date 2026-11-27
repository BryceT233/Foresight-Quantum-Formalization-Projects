/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.RealScalar
public import FQFP.Analysis.Asymptotics.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local asymptotics of algebra inverses

A continuous function through a unit has a locally bounded pointwise ring inverse.
Multiplication by such a function preserves asymptotic order.

## Main results

* `TrotterError.inverse_isBigO_one_of_continuous_unit`.
* `TrotterError.isTheta_mul_left_of_continuousAt_isUnit`.
-/

@[expose] public section

namespace TrotterError

open Asymptotics Filter
open scoped Topology

/-- A bounded multiplier with an eventually defined, bounded left inverse preserves
asymptotic order under left multiplication. -/
theorem isTheta_mul_left_of_eventually_mul_eq_one {ι A : Type*} [SeminormedRing A]
    {l : Filter ι} {u v : ι → A} (f : ι → A)
    (hu : u =O[l] (fun _ => (1 : ℝ))) (hv : v =O[l] (fun _ => (1 : ℝ)))
    (hvu : ∀ᶠ t in l, v t * u t = 1) : (fun t => u t * f t) =Θ[l] f := by
  have mul_bigO {a b : ι → A} (ha : a =O[l] (fun _ => (1 : ℝ))) :
      (fun t => a t * b t) =O[l] b := by
    rw [← isBigO_norm_right]
    simpa only [one_mul] using ha.mul (isBigO_refl b l).norm_right
  refine ⟨mul_bigO hu, (mul_bigO hv).congr' ?_ EventuallyEq.rfl⟩
  exact hvu.mono fun t ht => by simp only [← mul_assoc, ht, one_mul]

variable {𝔸 : Type*} [NormedRing 𝔸]

private lemma continuousAt_inverse_comp [HasSummableGeomSeries 𝔸] {ι : Type*} [TopologicalSpace ι]
    {U : ι → 𝔸} {x : ι} (hU : ContinuousAt U x) (hx : IsUnit (U x)) :
    ContinuousAt (fun t => Ring.inverse (U t)) x := by
  obtain ⟨u, hu⟩ := hx
  exact (hu ▸ NormedRing.inverse_continuousAt u).comp hU

/-- A left multiplier continuous at `x` and taking a unit value there preserves asymptotic
order near `x`. -/
theorem isTheta_mul_left_of_continuousAt_isUnit [HasSummableGeomSeries 𝔸]
    {ι : Type*} [TopologicalSpace ι] {x : ι} {U : ι → 𝔸} (f : ι → 𝔸)
    (hU : ContinuousAt U x) (hx : IsUnit (U x)) :
    (fun t => U t * f t) =Θ[𝓝 x] f := by
  have hu : ∀ᶠ y in 𝓝 (U x), IsUnit y := Units.isOpen.mem_nhds hx
  exact isTheta_mul_left_of_eventually_mul_eq_one f (hU.isBigO_one (F := ℝ))
    ((continuousAt_inverse_comp hU hx).isBigO_one (F := ℝ))
    ((hU.eventually hu).mono fun y hy => Ring.inverse_mul_cancel (U y) hy)

/-- If a continuous operator-valued function `U` is a unit at `0`, then its pointwise inverse
`Ring.inverse (U τ)` is `O(1)` as `τ → 0`. -/
lemma inverse_isBigO_one_of_continuous_unit [HasSummableGeomSeries 𝔸]
    {U : ℝ → 𝔸} (hU : Continuous U) (hU0 : IsUnit (U 0)) :
    (fun τ => ‖Ring.inverse (U τ)‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) :=
  (continuousAt_inverse_comp hU.continuousAt hU0).norm.isBigO_one (F := ℝ)

end TrotterError
