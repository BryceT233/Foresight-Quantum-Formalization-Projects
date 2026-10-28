/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Norm bounds from finite algebraic dual coordinates

Only the coordinate vector carries a norm; the underlying real module remains algebraic.

## Main results

* `LinearMap.abs_apply_le_sum_abs_repr_mul_norm_coordinates`: evaluation is bounded by the
  coefficient sum times the maximum dual coordinate.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace LinearMap
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Recovering an observable from finite dual coordinates costs its coefficient `ℓ¹` norm. -/
lemma abs_apply_le_sum_abs_repr_mul_norm_coordinates
    (B : Module.Basis ι ℝ E) (ℓ : Module.Dual ℝ E) (p : E) :
    |ℓ p| ≤ (∑ i, |B.repr p i|) * ‖fun i => ℓ (B i)‖ := by
  classical
  calc
    |ℓ p| = |∑ i, B.repr p i * ℓ (B i)| := by
      conv_lhs => rw [← B.sum_repr p]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ ∑ i, |B.repr p i * ℓ (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |B.repr p i| * ‖fun i => ℓ (B i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm (fun i => ℓ (B i)) i)
        (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

end LinearMap
