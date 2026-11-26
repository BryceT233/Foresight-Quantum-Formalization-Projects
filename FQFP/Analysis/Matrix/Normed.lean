/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Matrix row sums and operator norms

## Main results

* `Matrix.norm_mulVec_toContinuousLinearMap_le_iff`: row sums characterize operator norm
  bounds for the maximum norm on coordinates.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Matrix
variable {ι : Type*} [Fintype ι]

open scoped Matrix.Norms.Operator in
/-- A nonnegative constant bounds the maximum-norm operator exactly when it bounds every
row sum of entry norms. -/
lemma norm_mulVec_toContinuousLinearMap_le_iff {m n 𝕜 : Type*} [Fintype m] [Fintype n]
    [RCLike 𝕜] (A : Matrix m n 𝕜) {K : ℝ} (hK : 0 ≤ K) :
    ‖LinearMap.toContinuousLinearMap A.mulVecLin‖ ≤ K ↔ ∀ i, ∑ j, ‖A i j‖ ≤ K := by
  have hnorm : ‖LinearMap.toContinuousLinearMap A.mulVecLin‖ = ‖A‖ :=
    (linfty_opNorm_eq_opNorm A).symm
  rw [hnorm]
  change ‖fun i => WithLp.toLp 1 (A i)‖ ≤ K ↔ _
  rw [pi_norm_le_iff_of_nonneg hK]
  simp only [PiLp.norm_eq_of_L1]

/-- Absolute row sums bound the generator norm in maximum coordinates. -/
lemma norm_mulVec_toContinuousLinearMap_le_of_row_sum_le
    (A : Matrix ι ι ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hrows : ∀ i, ∑ j, |A i j| ≤ K) :
    ‖LinearMap.toContinuousLinearMap A.mulVecLin‖ ≤ K :=
  (norm_mulVec_toContinuousLinearMap_le_iff A hK).2 hrows

end Matrix
