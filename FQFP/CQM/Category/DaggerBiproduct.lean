/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerCategory
public import FQFP.CQM.Category.Semiadditive
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
* `DaggerCategory.dagger_biproduct_desc`, `DaggerCategory.dagger_biproduct_lift`: dagger
  exchanges row and column maps of a dagger biproduct.
* `DaggerCategory.dagger_add`: **Corollary 2.42** — `(f + g)† = f† + g†`.

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

attribute [simp] IsDaggerBiproduct.dagger_ι

namespace IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]

/-- The stated condition, read the other way: every projection is the dagger of the
corresponding injection. -/
@[simp]
lemma dagger_π (i : ι) : (biproduct.π f i)† = biproduct.ι f i := by
  simpa only [involutive_dagger] using (congrArg dagger (dagger_ι (f := f) i)).symm

end IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]

/-- Dagger of a row map is the column map of daggers. -/
@[simp]
lemma dagger_biproduct_desc {X : C} (x : ∀ i, f i ⟶ X) :
    (biproduct.desc x)† = biproduct.lift (fun i ↦ (x i)†) := by
  apply biproduct.hom_ext
  intro i
  rw [biproduct.lift_π, ← IsDaggerBiproduct.dagger_ι, ← dagger_comp, biproduct.ι_desc]

/-- Dagger of a column map is the row map of daggers. -/
@[simp]
lemma dagger_biproduct_lift {X : C} (x : ∀ i, X ⟶ f i) :
    (biproduct.lift x)† = biproduct.desc (fun i ↦ (x i)†) := by
  have h := congrArg dagger (dagger_biproduct_desc (fun i ↦ (x i)†))
  simpa only [involutive_dagger] using h.symm

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
  simp [entry, Category.assoc]

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
      = biproduct.matrix (f := G) (g := F) (fun (j : κ) (i : ι) ↦ (m i j)†) := by
  apply biproduct.matrixEquiv.injective
  funext j i
  change biproduct.components ((biproduct.matrix m)†) j i
      = biproduct.components (biproduct.matrix fun (j : κ) (i : ι) ↦ (m i j)†) j i
  rw [biproduct.matrix_components, biproduct.components]
  rw [← IsDaggerBiproduct.dagger_π (f := G) j, ← IsDaggerBiproduct.dagger_ι (f := F) i]
  rw [← dagger_comp, ← dagger_comp]
  rw [Category.assoc, ← biproduct.components, biproduct.matrix_components]

end MatrixForm

section Binary

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- Binary form of Definition 2.39, matching Mathlib's `biprod`. -/
class IsDaggerBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : Prop where
  /-- The first injection is the dagger of the first projection. -/
  dagger_inl : (biprod.inl : X ⟶ X ⊞ Y)† = biprod.fst
  /-- The second injection is the dagger of the second projection. -/
  dagger_inr : (biprod.inr : Y ⟶ X ⊞ Y)† = biprod.snd

attribute [simp] IsDaggerBinaryBiproduct.dagger_inl IsDaggerBinaryBiproduct.dagger_inr

section

variable {X Y Z : C} [HasBinaryBiproduct X Y] [IsDaggerBinaryBiproduct X Y]

@[simp]
lemma IsDaggerBinaryBiproduct.dagger_fst : (biprod.fst : X ⊞ Y ⟶ X)† = biprod.inl := by
  simpa only [involutive_dagger] using
    (congrArg dagger (IsDaggerBinaryBiproduct.dagger_inl (X := X) (Y := Y))).symm

@[simp]
lemma IsDaggerBinaryBiproduct.dagger_snd : (biprod.snd : X ⊞ Y ⟶ Y)† = biprod.inr := by
  simpa only [involutive_dagger] using
    (congrArg dagger (IsDaggerBinaryBiproduct.dagger_inr (X := X) (Y := Y))).symm

/-- Dagger of a row matrix is the column matrix of daggers. -/
@[simp]
lemma IsDaggerBinaryBiproduct.dagger_desc (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprod.desc f g)† = biprod.lift f† g† := by
  apply biprod.hom_ext
  · rw [biprod.lift_fst, ← IsDaggerBinaryBiproduct.dagger_inl, ← dagger_comp, biprod.inl_desc]
  · rw [biprod.lift_snd, ← IsDaggerBinaryBiproduct.dagger_inr, ← dagger_comp, biprod.inr_desc]

/-- Dagger of a column matrix is the row matrix of daggers. -/
@[simp]
lemma IsDaggerBinaryBiproduct.dagger_lift (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprod.lift f g)† = biprod.desc f† g† := by
  have h := congrArg dagger (IsDaggerBinaryBiproduct.dagger_desc f† g†)
  simpa only [involutive_dagger] using h.symm

end

end Binary

section Additive

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [Semiadditive C]

/-- **Corollary 2.42**: in a dagger category with dagger biproducts, daggers distribute
over addition. The superposition rule need not have additive inverses; addition is determined
by the given binary biproduct, as in equation (2.20). -/
theorem dagger_add {X Y : C} [HasBinaryBiproduct X X]
    [IsDaggerBinaryBiproduct X X] (f g : X ⟶ Y) :
    (f + g)† = f† + g† := by
  rw [Semiadditive.add_eq_lift_id_desc f g, dagger_comp,
    IsDaggerBinaryBiproduct.dagger_desc (X := X) (Y := X) (Z := Y),
    IsDaggerBinaryBiproduct.dagger_lift (X := X) (Y := X) (Z := X)]
  simp only [dagger_id]
  exact (Semiadditive.add_eq_lift_desc_id f† g†).symm

end Additive

end CategoryTheory.DaggerCategory
