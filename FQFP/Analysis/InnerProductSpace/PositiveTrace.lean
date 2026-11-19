/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Traces of products of positive operators

The trace of the product of two positive operators is nonnegative, even though their
product need not be positive. This supplies positivity of mixed-state expectations.

## Main results

* `LinearMap.IsPositive.trace_mul_nonneg` gives nonnegativity of the trace of a product of two
  positive operators.
-/

@[expose] public section

open scoped ComplexOrder

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The trace of the product of two positive operators is nonnegative. -/
lemma IsPositive.trace_mul_nonneg {A B : E →ₗ[𝕜] E}
    (hA : A.IsPositive) (hB : B.IsPositive) : 0 ≤ trace 𝕜 E (A * B) := by
  classical
  rw [trace_eq_sum_inner _ (hB.isSymmetric.eigenvectorBasis rfl)]
  apply Finset.sum_nonneg
  intro i _
  rw [mul_apply_eq_comp, hB.isSymmetric.apply_eigenvectorBasis,
    map_smul, inner_smul_right]
  exact mul_nonneg (RCLike.ofReal_nonneg.mpr (hB.nonneg_eigenvalues rfl i))
    (hA.inner_nonneg_right _)

end LinearMap
