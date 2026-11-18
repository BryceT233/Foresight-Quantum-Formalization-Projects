/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite.Basic
public import FQFP.CQM.Qudit.State.OperatorNorm
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Positive square roots of qudit operators

The continuous functional calculus gives positive square roots, including for singular
operators. This common API supports both measurement updates and mixed-state fidelity.

## Main definitions and results

* `Qudit.Operator.sqrt`: the positive square root from continuous functional calculus.
* `Qudit.Operator.sqrt_mul_sqrt`: squaring recovers a positive operator.
* `Qudit.Operator.sqrt_unique`: uniqueness among positive square roots.
* `Qudit.Operator.sqrt_tensor`: positive square roots commute with tensor products.
-/

@[expose] public section

open scoped ComplexOrder

namespace Qudit

noncomputable section

namespace Operator

variable {H : Qudit}

/-- Positive square root in the operator algebra. -/
def sqrt (A : Operator H) : Operator H :=
  CFC.sqrt A

/-- The functional-calculus square root is positive, including at singular operators. -/
lemma sqrt_positive (A : Operator H) : A.sqrt.IsPositive :=
  LinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)

/-- The positive square root is self-adjoint. -/
lemma adjoint_sqrt (A : Operator H) : A.sqrt.adjoint = A.sqrt :=
  A.sqrt_positive.adjoint_eq

/-- Squaring the positive square root recovers a positive operator. -/
lemma sqrt_mul_sqrt (A : Operator H) (hA : A.IsPositive) : A.sqrt * A.sqrt = A :=
  CFC.sqrt_mul_sqrt_self A (LinearMap.nonneg_iff_isPositive.mpr hA)

/-- A qudit arrow is dagger-positive exactly when its linear map is positive. -/
theorem _root_.Qudit.isPositive_iff_hom_isPositive (f : H ⟶ H) :
    CategoryTheory.DaggerCategory.IsPositive f ↔ f.hom.IsPositive := by
  refine ⟨fun hf ↦ hom_isPositive_of_isPositive f, fun hf ↦ ?_⟩
  refine ⟨H, ofHom (Operator.sqrt f.hom), hom_ext ?_⟩
  change f.hom = (Operator.sqrt f.hom).adjoint * Operator.sqrt f.hom
  rw [adjoint_sqrt, sqrt_mul_sqrt _ hf]

/-- The quadratic form of a positive operator is the squared norm of its square root. -/
lemma re_inner_apply_eq_norm_sqrt_sq (A : Operator H) (hA : A.IsPositive) (v : H.state) :
    (inner ℂ v (A v)).re = ‖A.sqrt v‖ ^ 2 := by
  calc
    _ = (inner ℂ v (A.sqrt.adjoint (A.sqrt v))).re := by
      rw [adjoint_sqrt, ← Module.End.mul_apply, sqrt_mul_sqrt A hA]
    _ = _ := by
      rw [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      norm_cast

/-- A positive operator annihilates a vector exactly when its quadratic form vanishes. -/
lemma apply_eq_zero_iff_re_inner_eq_zero (A : Operator H) (hA : A.IsPositive) (v : H.state) :
    A v = 0 ↔ (inner ℂ v (A v)).re = 0 := by
  constructor
  · intro h
    simp [h]
  · intro h
    rw [A.re_inner_apply_eq_norm_sqrt_sq hA, sq_eq_zero_iff, norm_eq_zero] at h
    rw [← A.sqrt_mul_sqrt hA, Module.End.mul_apply, h, map_zero]

/-- A positive operator whose square is `A` is the positive square root of `A`. -/
lemma sqrt_unique {A B : Operator H} (hsq : B * B = A) (hB : B.IsPositive) :
    A.sqrt = B :=
  CFC.sqrt_unique hsq (LinearMap.nonneg_iff_isPositive.mpr hB)

/-- A positive projection is its own positive square root. -/
lemma sqrt_eq_self (A : Operator H) (hA : A.IsPositive) (hsq : A * A = A) :
    A.sqrt = A := sqrt_unique hsq hA

/-- Positive square roots commute with tensor products, including singular operators. -/
lemma sqrt_tensor {K : Qudit} (A : Operator H) (B : Operator K)
    (hA : A.IsPositive) (hB : B.IsPositive) :
    (tensor A B).sqrt = tensor A.sqrt B.sqrt := by
  apply sqrt_unique _ (isPositive_tensor A.sqrt_positive B.sqrt_positive)
  change TensorProduct.map A.sqrt B.sqrt * TensorProduct.map A.sqrt B.sqrt = _
  rw [← TensorProduct.map_mul, A.sqrt_mul_sqrt hA, B.sqrt_mul_sqrt hB]
  rfl

end Operator

end

end Qudit
