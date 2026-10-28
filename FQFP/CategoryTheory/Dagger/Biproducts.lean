/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import FQFP.CategoryTheory.Semiadditive.Biproducts
public import FQFP.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Dagger biproducts

This file develops Definition 2.39 of the source notes — dagger biproducts — together with
the two results the notes draw from it: Lemma 2.41 (the adjoint of a matrix is its conjugate
transpose) and Corollary 2.42 (daggers distribute over addition).

A biproduct is a *dagger biproduct* when every injection is the dagger of the corresponding
projection. The core condition is attached to a concrete bicone; the existing conditions on
Mathlib's chosen biproducts are convenient special cases. Existence of a normalized bicone
does not imply that an independently chosen ordinary biproduct is normalized.

## Main definitions

* `DaggerCategory.IsDaggerBiproduct`: a biproduct whose injections are the daggers of its
  projections.
* `DaggerCategory.IsDaggerBinaryBiproduct`: the binary form of the same condition.
* `Limits.Bicone.IsDagger` and `Limits.BinaryBicone.IsDagger`: the conditions on explicit
  biproduct bicones.
* `DaggerCategory.DaggerBiproductData` and `DaggerCategory.HasDaggerBiproduct`: normalized
  bicone data and its existence, independently of Mathlib's chosen ordinary biproduct.
* `DaggerCategory.DaggerBinaryBiproductData` and `DaggerCategory.HasDaggerBinaryBiproduct`:
  the corresponding binary witnesses.
* `DaggerCategory.entry`: the `(i, j)` entry of a morphism of biproducts.

## Main results

* `Limits.Bicone.dagger_desc`, `Limits.Bicone.dagger_matrix`, and
  `Limits.Bicone.isUnitary_iso`: dagger calculus for explicit normalized bicones.
* `Limits.BinaryBicone.dagger_desc` and `Limits.BinaryBicone.isUnitary_iso`: the binary form.
* `DaggerCategory.dagger_entry`: **Lemma 2.41** in intrinsic form — transposing a morphism
  of biproducts daggers every entry.
* `DaggerCategory.dagger_biproduct_matrix`: **Lemma 2.41** in `biproduct.matrix` form.
* `DaggerCategory.dagger_biproduct_desc`, `DaggerCategory.dagger_biproduct_lift`: dagger
  exchanges row and column maps of a dagger biproduct.
* `DaggerCategory.dagger_add`: **Corollary 2.42** — `(f + g)† = f† + g†`.

-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Limits.Bicone

open DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {ι : Type*} {F : ι → C} (b : Bicone F)

section Dagger

variable [DaggerCategory C]

/-- A bicone is a dagger bicone when each injection is the dagger of its projection. -/
class IsDagger {ι : Type*} {F : ι → C} (b : Bicone F) : Prop where
  /-- The injection and projection at each index are adjoints. -/
  dagger_ι (i : ι) : (b.ι i)† = b.π i

variable [b.IsDagger]

/-- The projection of a dagger bicone is the dagger of its injection. -/
@[simp]
lemma IsDagger.dagger_π (i : ι) : (b.π i)† = b.ι i := by
  simpa only [involutive_dagger] using (congrArg dagger (IsDagger.dagger_ι (b := b) i)).symm

end Dagger

variable (hb : b.IsBilimit)

section Dagger

variable [DaggerCategory C]
variable [b.IsDagger]

/-- Dagger exchanges the row and column maps of an explicit dagger biproduct. -/
theorem dagger_desc {X : C} (x : ∀ i, F i ⟶ X) :
    (b.desc hb x)† = b.lift hb (fun i ↦ (x i)†) := by
  apply hb.isLimit.hom_ext
  intro i
  change (b.desc hb x)† ≫ b.π i.as = b.lift hb (fun i ↦ (x i)†) ≫ b.π i.as
  rw [lift_π, ← IsDagger.dagger_ι (b := b) i.as, ← dagger_comp, ι_desc]

/-- Dagger exchanges the column and row maps of an explicit dagger biproduct. -/
theorem dagger_lift {X : C} (x : ∀ i, X ⟶ F i) :
    (b.lift hb x)† = b.desc hb (fun i ↦ (x i)†) := by
  have h := congrArg dagger (b.dagger_desc hb (fun i ↦ (x i)†))
  simpa only [involutive_dagger] using h.symm

end Dagger

section Matrix

variable {κ : Type*} {G : κ → C} (c : Bicone G) (hc : c.IsBilimit)

section Dagger

variable [DaggerCategory C] [b.IsDagger] [c.IsDagger]

/-- The dagger of a map of dagger bicones transposes and daggers its entries. -/
theorem dagger_entry (x : b.pt ⟶ c.pt) (i : ι) (j : κ) :
    c.entry b x† j i = (b.entry c x i j)† := by
  simp only [entry, dagger_comp, IsDagger.dagger_ι, IsDagger.dagger_π, Category.assoc]

/-- The matrix assembled from daggered entries is the dagger of the original matrix. -/
theorem dagger_matrix (m : ∀ i j, F i ⟶ G j) :
    (b.matrix hb c hc m)† =
      c.matrix hc b hb (fun j i ↦ (m i j)†) := by
  apply hb.isLimit.hom_ext
  intro i
  apply hc.isColimit.hom_ext
  intro j
  change c.entry b (b.matrix hb c hc m)† j.as i.as =
    c.entry b (c.matrix hc b hb (fun j i ↦ (m i j)†)) j.as i.as
  rw [b.dagger_entry c, b.entry_matrix hb c hc, c.entry_matrix hc b hb]

end Dagger

end Matrix

section Comparison

variable (c : Bicone F) (hc : c.IsBilimit)

section Dagger

variable [DaggerCategory C] [b.IsDagger] [c.IsDagger]

/-- The canonical comparison of two dagger biproducts is unitary. -/
theorem isUnitary_iso : IsUnitary (b.iso hb c hc).hom := by
  rw [isUnitary_hom_iff_dagger_hom_eq_inv]
  apply hc.isColimit.hom_ext
  intro i
  change c.ι i.as ≫ (b.iso hb c hc).hom† = c.ι i.as ≫ (b.iso hb c hc).inv
  calc
    c.ι i.as ≫ (b.iso hb c hc).hom†
        = ((b.iso hb c hc).hom ≫ c.π i.as)† := by
            rw [dagger_comp, IsDagger.dagger_π]
    _ = (b.π i.as)† := by rw [b.iso_hom_π hb c hc i.as]
    _ = b.ι i.as := IsDagger.dagger_π b i.as
    _ = c.ι i.as ≫ (b.iso hb c hc).inv := by
      change b.ι i.as = c.ι i.as ≫ c.desc hc b.ι
      rw [ι_desc]

end Dagger

end Comparison

end CategoryTheory.Limits.Bicone

namespace CategoryTheory.Limits.BinaryBicone

open DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {X Y : C} (b : BinaryBicone X Y)

section Dagger

variable [DaggerCategory C]

/-- A binary bicone whose injections are adjoint to its projections. -/
class IsDagger : Prop where
  /-- The first injection and projection are adjoints. -/
  dagger_inl : b.inl† = b.fst
  /-- The second injection and projection are adjoints. -/
  dagger_inr : b.inr† = b.snd

variable [b.IsDagger]

/-- The first projection is the dagger of the first injection. -/
@[simp]
lemma IsDagger.dagger_fst : b.fst† = b.inl := by
  simpa only [involutive_dagger] using (congrArg dagger (IsDagger.dagger_inl (b := b))).symm

/-- The second projection is the dagger of the second injection. -/
@[simp]
lemma IsDagger.dagger_snd : b.snd† = b.inr := by
  simpa only [involutive_dagger] using (congrArg dagger (IsDagger.dagger_inr (b := b))).symm

end Dagger

variable (hb : b.IsBilimit)

section Dagger

variable [DaggerCategory C] [b.IsDagger]

/-- Dagger exchanges the row and column maps of a binary dagger biproduct. -/
theorem dagger_desc {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (b.desc hb f g)† = b.lift hb f† g† := by
  apply BinaryFan.IsLimit.hom_ext hb.isLimit
  · change (b.desc hb f g)† ≫ b.fst = b.lift hb f† g† ≫ b.fst
    rw [lift_fst, ← IsDagger.dagger_inl (b := b), ← dagger_comp, inl_desc]
  · change (b.desc hb f g)† ≫ b.snd = b.lift hb f† g† ≫ b.snd
    rw [lift_snd, ← IsDagger.dagger_inr (b := b), ← dagger_comp, inr_desc]

/-- Dagger exchanges the column and row maps of a binary dagger biproduct. -/
theorem dagger_lift {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) :
    (b.lift hb f g)† = b.desc hb f† g† := by
  have h := congrArg dagger (b.dagger_desc hb f† g†)
  simpa only [involutive_dagger] using h.symm

end Dagger

section Comparison

variable [DaggerCategory C] [b.IsDagger]

/-- The family view of a binary dagger bicone is still a dagger bicone. -/
instance toBiconeIsDagger : b.toBicone.IsDagger where
  dagger_ι i := by
    cases i with
    | left => exact IsDagger.dagger_inl (b := b)
    | right => exact IsDagger.dagger_inr (b := b)

variable (c : BinaryBicone X Y) (hc : c.IsBilimit) [c.IsDagger]

/-- The canonical comparison of two binary dagger biproducts is unitary. -/
theorem isUnitary_iso : IsUnitary (b.iso hb c hc).hom :=
  b.toBicone.isUnitary_iso ((b.toBiconeIsBilimit).symm hb) c.toBicone
    ((c.toBiconeIsBilimit).symm hc)

end Comparison

end CategoryTheory.Limits.BinaryBicone

namespace CategoryTheory.DaggerCategory

universe u v

section Family

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- A specific dagger biproduct, with its bilimit and dagger witnesses. -/
structure DaggerBiproductData {ι : Type*} (F : ι → C) where
  /-- The bicone carrying the orthogonal direct sum. -/
  bicone : Bicone F
  /-- The bicone is both a limit and a colimit. -/
  isBilimit : bicone.IsBilimit
  /-- Its injections are adjoint to its projections. -/
  isDagger : bicone.IsDagger

/-- Existence of a dagger biproduct without normalizing Mathlib's chosen biproduct. -/
class HasDaggerBiproduct {ι : Type*} (F : ι → C) : Prop where
  /-- A normalized bilimit bicone exists. -/
  exists_daggerBiproduct : Nonempty (DaggerBiproductData F)

/-- A chosen dagger biproduct, selected together with its normalization. -/
noncomputable def daggerBiproduct {ι : Type*} (F : ι → C)
    [HasDaggerBiproduct F] : DaggerBiproductData F :=
  Classical.choice HasDaggerBiproduct.exists_daggerBiproduct

/-- A dagger biproduct supplies an ordinary biproduct, without normalizing its choice. -/
instance {ι : Type*} (F : ι → C) [HasDaggerBiproduct F] : HasBiproduct F where
  exists_biproduct := ⟨⟨(daggerBiproduct F).bicone, (daggerBiproduct F).isBilimit⟩⟩

namespace DaggerBiproductData

variable {ι : Type*} {F : ι → C} (d : DaggerBiproductData F)

/-- The chosen dagger bicone carries its dagger property. -/
instance : d.bicone.IsDagger := d.isDagger

end DaggerBiproductData

/-- A biproduct `⨁ f` is a **dagger biproduct** when every injection is the dagger of the
corresponding projection. -/
class IsDaggerBiproduct {ι : Type*} (f : ι → C) [HasBiproduct f] : Prop where
  /-- Every injection is the dagger of the corresponding projection. -/
  dagger_ι : ∀ i, (biproduct.ι f i)† = biproduct.π f i

attribute [simp] IsDaggerBiproduct.dagger_ι

/-- The chosen ordinary bicone inherits an explicitly assumed dagger condition. -/
instance chosenBiconeIsDagger {ι : Type*} {F : ι → C} [HasBiproduct F]
    [IsDaggerBiproduct F] : (biproduct.bicone F).IsDagger where
  dagger_ι := IsDaggerBiproduct.dagger_ι

namespace IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]

/-- The stated condition, read the other way: every projection is the dagger of the
corresponding injection. The explicit-bicone lemma supplies the simp rule. -/
lemma dagger_π (i : ι) : (biproduct.π f i)† = biproduct.ι f i := by
  simpa only [involutive_dagger] using (congrArg dagger (dagger_ι (f := f) i)).symm

end IsDaggerBiproduct

variable {ι : Type*} {f : ι → C} [HasBiproduct f] [IsDaggerBiproduct f]

/-- Dagger of a row map is the column map of daggers. -/
@[simp]
lemma dagger_biproduct_desc {X : C} (x : ∀ i, f i ⟶ X) :
    (biproduct.desc x)† = biproduct.lift (fun i ↦ (x i)†) :=
  (biproduct.bicone f).dagger_desc (biproduct.isBilimit f) x

/-- Dagger of a column map is the row map of daggers. -/
@[simp]
lemma dagger_biproduct_lift {X : C} (x : ∀ i, X ⟶ f i) :
    (biproduct.lift x)† = biproduct.desc (fun i ↦ (x i)†) :=
  (biproduct.bicone f).dagger_lift (biproduct.isBilimit f) x

variable {κ : Type*} {G : κ → C} [HasBiproduct G] [IsDaggerBiproduct G]

/-- The `(i, j)` entry of a morphism of biproducts. Unlike Mathlib's
`biproduct.components`, this needs neither `HasFiniteBiproducts` nor index types at
`Type 0`. -/
noncomputable def entry (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) : f i ⟶ G j :=
  biproduct.ι f i ≫ x ≫ biproduct.π G j

/-- **Lemma 2.41**, intrinsic (universe-polymorphic) form: transposing a morphism of
biproducts daggers every entry. -/
theorem dagger_entry (x : ⨁ f ⟶ ⨁ G) (i : ι) (j : κ) :
    entry (x†) j i = (entry x i j)† :=
  (biproduct.bicone f).dagger_entry (biproduct.bicone G) x i j

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
      = biproduct.matrix (f := G) (g := F) (fun (j : κ) (i : ι) ↦ (m i j)†) :=
  (biproduct.bicone F).dagger_matrix (biproduct.isBilimit F)
    (biproduct.bicone G) (biproduct.isBilimit G) m

end MatrixForm

section Binary

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]

/-- A specific binary dagger biproduct with its bilimit and dagger witnesses. -/
structure DaggerBinaryBiproductData (X Y : C) where
  /-- The bicone carrying the orthogonal binary sum. -/
  bicone : BinaryBicone X Y
  /-- The bicone is both a limit and a colimit. -/
  isBilimit : bicone.IsBilimit
  /-- Its injections are adjoint to its projections. -/
  isDagger : bicone.IsDagger

/-- Existence of a binary dagger biproduct without normalizing the ordinary choice. -/
class HasDaggerBinaryBiproduct (X Y : C) : Prop where
  /-- A normalized binary bilimit bicone exists. -/
  exists_daggerBinaryBiproduct : Nonempty (DaggerBinaryBiproductData X Y)

/-- A chosen binary dagger biproduct together with its normalization. -/
noncomputable def daggerBinaryBiproduct (X Y : C) [HasDaggerBinaryBiproduct X Y] :
    DaggerBinaryBiproductData X Y :=
  Classical.choice HasDaggerBinaryBiproduct.exists_daggerBinaryBiproduct

/-- A binary dagger biproduct supplies an ordinary binary biproduct. -/
instance (X Y : C) [HasDaggerBinaryBiproduct X Y] : HasBinaryBiproduct X Y where
  exists_binary_biproduct :=
    ⟨⟨(daggerBinaryBiproduct X Y).bicone, (daggerBinaryBiproduct X Y).isBilimit⟩⟩

namespace DaggerBinaryBiproductData

variable {X Y : C} (d : DaggerBinaryBiproductData X Y)

/-- The chosen binary dagger bicone carries its dagger property. -/
instance : d.bicone.IsDagger := d.isDagger

end DaggerBinaryBiproductData

/-- Binary form of Definition 2.39, matching Mathlib's `biprod`. -/
class IsDaggerBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : Prop where
  /-- The first injection is the dagger of the first projection. -/
  dagger_inl : (biprod.inl : X ⟶ X ⊞ Y)† = biprod.fst
  /-- The second injection is the dagger of the second projection. -/
  dagger_inr : (biprod.inr : Y ⟶ X ⊞ Y)† = biprod.snd

attribute [simp] IsDaggerBinaryBiproduct.dagger_inl IsDaggerBinaryBiproduct.dagger_inr

/-- The chosen ordinary binary bicone inherits an explicitly assumed dagger condition. -/
instance chosenBinaryBiconeIsDagger {X Y : C} [HasBinaryBiproduct X Y]
    [IsDaggerBinaryBiproduct X Y] : (BinaryBiproduct.bicone X Y).IsDagger where
  dagger_inl := IsDaggerBinaryBiproduct.dagger_inl
  dagger_inr := IsDaggerBinaryBiproduct.dagger_inr

section

variable {X Y Z : C} [HasBinaryBiproduct X Y] [IsDaggerBinaryBiproduct X Y]

/-- The explicit binary-bicone lemma supplies the simp rule for this equality. -/
lemma IsDaggerBinaryBiproduct.dagger_fst : (biprod.fst : X ⊞ Y ⟶ X)† = biprod.inl := by
  simpa only [involutive_dagger] using
    (congrArg dagger (IsDaggerBinaryBiproduct.dagger_inl (X := X) (Y := Y))).symm

/-- The explicit binary-bicone lemma supplies the simp rule for this equality. -/
lemma IsDaggerBinaryBiproduct.dagger_snd : (biprod.snd : X ⊞ Y ⟶ Y)† = biprod.inr := by
  simpa only [involutive_dagger] using
    (congrArg dagger (IsDaggerBinaryBiproduct.dagger_inr (X := X) (Y := Y))).symm

/-- Dagger of a row matrix is the column matrix of daggers. -/
@[simp]
lemma IsDaggerBinaryBiproduct.dagger_desc (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprod.desc f g)† = biprod.lift f† g† :=
  (BinaryBiproduct.bicone X Y).dagger_desc (BinaryBiproduct.isBilimit X Y) f g

/-- Dagger of a column matrix is the row matrix of daggers. -/
@[simp]
lemma IsDaggerBinaryBiproduct.dagger_lift (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprod.lift f g)† = biprod.desc f† g† :=
  (BinaryBiproduct.bicone X Y).dagger_lift (BinaryBiproduct.isBilimit X Y) f g

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
