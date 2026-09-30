/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Dagger biproducts

This file develops Definition 2.39 of the source notes — dagger biproducts — together with
the two results the notes draw from it: Lemma 2.41 (the adjoint of a matrix is its conjugate
transpose) and Corollary 2.42 (daggers distribute over addition).

A biproduct `⨁ f` is a *dagger biproduct* when every injection is the dagger of the
corresponding projection. The condition is stated both for an arbitrary finite family
(`IsDaggerBiproduct`) and in the binary form matching Mathlib's `biprod`
(`IsDaggerBinaryBiproduct`).

## Main definitions

* `DaggerCategory.IsDaggerBiproduct`: a biproduct whose injections are the daggers of its
  projections.
* `DaggerCategory.IsDaggerBinaryBiproduct`: the binary form of the same condition.
* `DaggerCategory.entry`: the `(i, j)` entry of a morphism of biproducts.

## Main results

* `DaggerCategory.dagger_entry`: **Lemma 2.41** in intrinsic form — transposing a morphism
  of biproducts daggers every entry.
* `DaggerCategory.dagger_biproduct_matrix`: **Lemma 2.41** in `biproduct.matrix` form.
* `DaggerCategory.dagger_add`: **Corollary 2.42** — `(f + g)† = f† + g†`.

## Implementation notes

Mathlib's `biproduct.matrix` is monomorphic in its index types (`J : Type`, not `Type*`),
so `dagger_biproduct_matrix` is stated at `Type 0`. The intrinsic `dagger_entry` form has no
such restriction and is the one to use for general statements.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.DaggerCategory

universe u v

section Family

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- A biproduct `⨁ f` is a **dagger biproduct** when every injection is the dagger of the
corresponding projection. -/
class IsDaggerBiproduct {ι : Type*} (f : ι → C) [HasBiproduct f] : Prop where
  /-- Every injection is the dagger of the corresponding projection. -/
  dagger_ι : ∀ i, (biproduct.ι f i)† = biproduct.π f i

namespace IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]

/-- The stated condition, read the other way: every projection is the dagger of the
corresponding injection. -/
lemma dagger_π (i : ι) : (biproduct.π f i)† = biproduct.ι f i := by
  rw [← dagger_ι i]
  simp

end IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]
variable {κ : Type*} {G : κ → C} [HasBiproduct G] [IsDaggerBiproduct G]

/-- The `(i, j)` entry of a morphism of biproducts. Unlike Mathlib's
`biproduct.components`, this needs neither `HasFiniteBiproducts` nor index types at
`Type 0`. -/
noncomputable def entry (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) : f i ⟶ G j :=
  biproduct.ι f i ≫ x ≫ biproduct.π G j

/-- **Lemma 2.41**, intrinsic (universe-polymorphic) form: transposing a morphism of
biproducts daggers every entry. -/
theorem dagger_entry (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) :
    entry (x†) j i = (entry x i j)† := by
  rw [entry, entry, ← IsDaggerBiproduct.dagger_π (f := G) j,
    ← IsDaggerBiproduct.dagger_ι (f := f) i]
  rw [← dagger_comp, ← dagger_comp, Category.assoc]

end Family

section MatrixForm

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- **Lemma 2.41** in `biproduct.matrix` form: the adjoint of a matrix is its conjugate
transpose. -/
theorem dagger_biproduct_matrix {ι κ : Type} [Finite ι] [Finite κ]
    {F : ι → C} {G : κ → C} [HasFiniteBiproducts C]
    [IsDaggerBiproduct F] [IsDaggerBiproduct G]
    (m : ∀ i j, F i ⟶ G j) :
    (biproduct.matrix m)†
      = biproduct.matrix (f := G) (g := F) (fun (j : κ) (i : ι) => (m i j)†) := by
  apply biproduct.matrixEquiv.injective
  funext j i
  change biproduct.components ((biproduct.matrix m)†) j i
      = biproduct.components (biproduct.matrix fun (j : κ) (i : ι) => (m i j)†) j i
  rw [biproduct.matrix_components, biproduct.components]
  rw [← IsDaggerBiproduct.dagger_π (f := G) j, ← IsDaggerBiproduct.dagger_ι (f := F) i]
  rw [← dagger_comp, ← dagger_comp]
  rw [Category.assoc, ← biproduct.components, biproduct.matrix_components]

end MatrixForm

section Additive

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Preadditive C]

/-- Binary form of Definition 2.39, matching Mathlib's `biprod`. -/
class IsDaggerBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : Prop where
  /-- The first injection is the dagger of the first projection. -/
  dagger_inl : (biprod.inl : X ⟶ X ⊞ Y)† = biprod.fst
  /-- The second injection is the dagger of the second projection. -/
  dagger_inr : (biprod.inr : Y ⟶ X ⊞ Y)† = biprod.snd

section

variable {X Y Z : C} [HasBinaryBiproduct X Y] [IsDaggerBinaryBiproduct X Y]

lemma IsDaggerBinaryBiproduct.dagger_fst : (biprod.fst : X ⊞ Y ⟶ X)† = biprod.inl := by
  rw [← IsDaggerBinaryBiproduct.dagger_inl]
  simp

lemma IsDaggerBinaryBiproduct.dagger_snd : (biprod.snd : X ⊞ Y ⟶ Y)† = biprod.inr := by
  rw [← IsDaggerBinaryBiproduct.dagger_inr]
  simp

/-- Dagger of a row matrix is the column matrix of daggers. -/
lemma IsDaggerBinaryBiproduct.dagger_desc (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprod.desc f g)† = biprod.lift f† g† := by
  refine (biprod.ext_to_iff (X := X) (Y := Y) (Z := Z)).mpr ⟨?_, ?_⟩
  · rw [← IsDaggerBinaryBiproduct.dagger_inl, ← dagger_comp]
    simp [IsDaggerBinaryBiproduct.dagger_inl]
  · rw [← IsDaggerBinaryBiproduct.dagger_inr, ← dagger_comp]
    simp [IsDaggerBinaryBiproduct.dagger_inr]

/-- Dagger of a column matrix is the row matrix of daggers. -/
lemma IsDaggerBinaryBiproduct.dagger_lift (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprod.lift f g)† = biprod.desc f† g† := by
  refine (biprod.ext_from_iff (X := X) (Y := Y) (Z := Z)).mpr ⟨?_, ?_⟩
  · rw [← IsDaggerBinaryBiproduct.dagger_fst, ← dagger_comp]
    simp [IsDaggerBinaryBiproduct.dagger_fst]
  · rw [← IsDaggerBinaryBiproduct.dagger_snd, ← dagger_comp]
    simp [IsDaggerBinaryBiproduct.dagger_snd]

end

/-- **Corollary 2.42**: in a dagger category with dagger biproducts, daggers distribute
over addition. The book's equation (2.20), `f + g = (f g) ∘ (id_A; id_A)`, is Mathlib's
`biprod.add_eq_lift_id_desc`.

Note that `Preadditive C` must be the *only* route to `HasZeroMorphisms C` in scope:
`biprod.ext_to_iff` is elaborated against `Preadditive.preadditiveHasZeroMorphisms`, so an
additional explicit `[HasZeroMorphisms C]` builds `HasBinaryBiproduct` from the wrong
instance and instance synthesis fails. -/
theorem dagger_add {X Y : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    [IsDaggerBinaryBiproduct X X] [IsDaggerBinaryBiproduct Y Y] (f g : X ⟶ Y) :
    (f + g)† = f† + g† := by
  rw [biprod.add_eq_lift_id_desc f g, dagger_comp,
    IsDaggerBinaryBiproduct.dagger_desc (X := X) (Y := X) (Z := Y),
    IsDaggerBinaryBiproduct.dagger_lift (X := X) (Y := X) (Z := X)]
  simp only [dagger_id]
  exact (biprod.add_eq_lift_desc_id f† g†).symm

end Additive

end CategoryTheory.DaggerCategory
