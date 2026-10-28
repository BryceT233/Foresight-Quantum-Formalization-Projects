/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Asymptotics.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local asymptotics of algebra inverses

A continuous function through a unit has a locally bounded pointwise ring inverse.

## Main results

* `TrotterError.inverse_isBigO_one_of_continuous_unit`.
-/

@[expose] public section

namespace TrotterError

open Asymptotics
open scoped Topology

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- If a continuous operator-valued function `U` is a unit at `0`, then its pointwise inverse
`Ring.inverse (U τ)` is `O(1)` as `τ → 0`. -/
lemma inverse_isBigO_one_of_continuous_unit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {U : ℝ → 𝔸} (hU : Continuous U) (hU0 : IsUnit (U 0)) :
    (fun τ => ‖Ring.inverse (U τ)‖) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := by
  have hcont : ContinuousAt (fun τ => Ring.inverse (U τ)) 0 :=
    (differentiableAt_inverse (𝕜 := ℝ) hU0).continuousAt.comp hU.continuousAt
  exact hcont.norm.isBigO_one (F := ℝ)

end TrotterError
