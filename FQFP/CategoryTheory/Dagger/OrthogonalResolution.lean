/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import FQFP.CategoryTheory.Semiadditive.Basic

/-!
# Orthogonal resolutions of the identity

Definitions 0.59–0.61 of Heunen and Vicary's *Categorical Quantum Mechanics*
use only a dagger, zero morphisms and finite sums of morphisms.
-/

@[expose] public section

namespace CategoryTheory

open DaggerCategory Limits

variable {C : Type*} [Category* C] [DaggerCategory C] [Semiadditive C]

/-- A finite family of pairwise orthogonal dagger projections resolving the identity. -/
structure OrthogonalResolution (X : C) (ι : Type*) [Fintype ι] where
  /-- The projection indexed by an outcome. -/
  proj : ι → (X ⟶ X)
  /-- Every component is an idempotent self-adjoint arrow. -/
  isProj : ∀ i, IsProj (proj i)
  /-- Distinct components annihilate one another. -/
  orthogonal : Pairwise (fun i j ↦ proj i ≫ proj j = 0)
  /-- The components sum to the identity. -/
  sum_proj : ∑ i, proj i = 𝟙 X

attribute [instance] OrthogonalResolution.isProj

namespace OrthogonalResolution

variable {X : C} {ι : Type*} [Fintype ι] (P : OrthogonalResolution X ι)

/-- Each projection factors through its own dagger. -/
instance (i : ι) : IsPositive (P.proj i) :=
  ⟨X, P.proj i, by rw [IsProj.selfAdjoint, IsProj.comp_self]⟩

/-- Two successive projections retain exactly the common outcome. -/
theorem proj_comp_proj [DecidableEq ι] (i j : ι) :
    P.proj i ≫ P.proj j = if i = j then P.proj i else 0 := by
  split_ifs with h
  · subst j
    exact IsProj.comp_self _
  · exact P.orthogonal h

/-- Projecting both sides of an endomorphism twice retains precisely the first block
when the outcomes agree. -/
theorem sandwich_sandwich [DecidableEq ι] (i j : ι) (f : X ⟶ X) :
    P.proj j ≫ (P.proj i ≫ f ≫ P.proj i) ≫ P.proj j =
      if i = j then P.proj i ≫ f ≫ P.proj i else 0 := by
  calc
    _ = (P.proj j ≫ P.proj i) ≫ f ≫ (P.proj i ≫ P.proj j) := by simp only [Category.assoc]
    _ = _ := by
      rw [P.proj_comp_proj, P.proj_comp_proj]
      by_cases h : i = j <;> simp [h, Ne.symm]

/-- The sum of the diagonal blocks of an endomorphism with respect to a resolution. -/
def diagonalPart (f : X ⟶ X) : X ⟶ X := ∑ i, P.proj i ≫ f ≫ P.proj i

/-- Keeping only diagonal blocks is idempotent. -/
theorem diagonalPart_idempotent (f : X ⟶ X) :
    P.diagonalPart (P.diagonalPart f) = P.diagonalPart f := by
  classical
  simp only [diagonalPart, Semiadditive.sum_comp, Semiadditive.comp_sum, P.sandwich_sandwich]
  simp

end OrthogonalResolution

end CategoryTheory
