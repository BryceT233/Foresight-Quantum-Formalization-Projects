/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Basic.Real.Basic

/-!
# Coordinates of algebraic dual endomorphisms

## Main results

* `LinearMap.dualMap_coordinates`: transposition computes the dual action in basis coordinates.
  The observable space has no topology or norm.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace LinearMap
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma dualMap_coordinates (B : Module.Basis ι ℝ E) (T : Module.End ℝ E)
    (ℓ : Module.Dual ℝ E) (i : ι) :
    ((LinearMap.toMatrix B B T).transpose).mulVec (fun j => ℓ (B j)) i =
      T.dualMap ℓ (B i) := by
  change _ = ℓ (T (B i))
  calc
    _ = ∑ j, B.repr (T (B i)) j * ℓ (B j) := by
      simp [Matrix.mulVec, dotProduct, toMatrix_apply]
    _ = ℓ (∑ j, B.repr (T (B i)) j • B j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ℓ (T (B i)) := congrArg ℓ (B.sum_repr (T (B i)))

end LinearMap
