/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Matrix row sums and operator norms

## Main results

* `Matrix.norm_mulVec_toContinuousLinearMap_le_of_row_sum_le`: absolute row sums bound
  the operator norm for maximum coordinates.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Matrix
variable {ι : Type*} [Fintype ι]

/-- Absolute row sums bound the generator norm in maximum coordinates. -/
lemma norm_mulVec_toContinuousLinearMap_le_of_row_sum_le
    (A : Matrix ι ι ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hrows : ∀ i, ∑ j, |A i j| ≤ K) :
    ‖LinearMap.toContinuousLinearMap A.mulVecLin‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg v))).mpr
  intro i
  change ‖A.mulVec v i‖ ≤ K * ‖v‖
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrows i) (norm_nonneg v)

end Matrix
