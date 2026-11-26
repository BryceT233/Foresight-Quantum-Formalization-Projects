/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
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
  /-- The operator indexed by an outcome. -/
  op : ι → End X
  /-- Every outcome operator is a projection. -/
  isStarProjection : ∀ i, IsStarProjection (op i)
  /-- Distinct components annihilate one another. -/
  orthogonal : Pairwise (fun i j ↦ (op i).asHom ≫ (op j).asHom = 0)
  /-- The components sum to the identity. -/
  sum_proj : ∑ i, (op i).asHom = 𝟙 X

namespace OrthogonalResolution

variable {X : C} {ι : Type*} [Fintype ι] (P : OrthogonalResolution X ι)

/-- The outcome projection as an arrow, for composition with states and processes. -/
abbrev proj (i : ι) : X ⟶ X := (P.op i).asHom

/-- Each outcome operator admits a dagger factorization. -/
theorem isPositive (i : ι) : (P.op i).IsPositive := (P.isStarProjection i).isPositive

/-- Two successive projections retain exactly the common outcome. -/
theorem proj_comp_proj [DecidableEq ι] (i j : ι) :
    P.proj i ≫ P.proj j = if i = j then P.proj i else 0 := by
  split_ifs with h
  · subst j
    exact (P.isStarProjection i).isIdempotentElem.asHom_comp_self
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

/-- Taking the diagonal part retains a diagonal block and annihilates a cross block. -/
theorem diagonalPart_block [DecidableEq ι] (i j : ι) (f : X ⟶ X) :
    P.diagonalPart (P.proj i ≫ f ≫ P.proj j) =
      if i = j then P.proj i ≫ f ≫ P.proj j else 0 := by
  calc
    _ = ∑ k, (P.proj k ≫ P.proj i) ≫ f ≫ (P.proj j ≫ P.proj k) := by
      simp only [diagonalPart, Category.assoc]
    _ = _ := by
      rw [Finset.sum_eq_single i]
      · by_cases h : i = j <;> simp [P.proj_comp_proj, h, Ne.symm]
      · intro k _ h
        rw [P.proj_comp_proj, ite_eq_right h, zero_comp]
      · simp

/-- Keeping only diagonal blocks is idempotent. -/
theorem diagonalPart_idempotent (f : X ⟶ X) :
    P.diagonalPart (P.diagonalPart f) = P.diagonalPart f := by
  classical
  simp only [diagonalPart, Semiadditive.sum_comp, Semiadditive.comp_sum, P.sandwich_sandwich]
  simp

end OrthogonalResolution

end CategoryTheory
