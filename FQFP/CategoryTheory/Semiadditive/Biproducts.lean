/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Semiadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.OfBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Semiadditive categories and biproducts

Biproducts determine addition, and finite bilimit bicones resolve the identity.

## Main results

* `Semiadditive.ofHasBinaryBiproducts`: the explicit superposition construction.
* `Semiadditive.add_eq_lift_id_desc`: addition via a binary biproduct.
* `Limits.Bicone.total`: the finite identity resolution.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe u v

namespace Semiadditive

variable {C : Type u} [Category.{v} C]

/-- Binary biproducts determine a superposition rule. This explicit construction uses Mathlib's
commutative-monoid addition; it does not replace any existing addition by instance search. -/
@[instance_reducible]
noncomputable def ofHasBinaryBiproducts [HasZeroMorphisms C] [HasBinaryBiproducts C] :
    Semiadditive C where
  homMonoid := SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBiproducts
  add_comp _ _ _ f g h := SemiadditiveOfBinaryBiproducts.add_comp f g h
  comp_add _ _ _ f g h := SemiadditiveOfBinaryBiproducts.comp_add f g h
  zero_comp _ _ _ f := Limits.zero_comp (f := f)
  comp_zero _ _ _ f := Limits.comp_zero (f := f)

variable [Semiadditive C]

/-- A binary biproduct's row map is the sum of its two components. -/
lemma desc_eq_add {X Y Z : C} [HasBinaryBiproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by
  ext <;> simp

/-- A binary biproduct's column map is the sum of its two components. -/
lemma lift_eq_add {X Y Z : C} [HasBinaryBiproduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
  ext <;> simp

/-- Addition is the diagonal followed by the row map of a binary biproduct. -/
lemma add_eq_lift_id_desc {X Y : C} [HasBinaryBiproduct X X] (f g : X ⟶ Y) :
    f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by
  simp [desc_eq_add]

/-- Addition is the column map followed by the codiagonal of a binary biproduct. -/
lemma add_eq_lift_desc_id {X Y : C} [HasBinaryBiproduct Y Y] (f g : X ⟶ Y) :
    f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by
  simp [lift_eq_add, Category.assoc]

end Semiadditive

namespace Limits.Bicone

variable {C : Type u} [Category.{v} C] [Semiadditive C]
  {ι : Type*} [Fintype ι] {F : ι → C} (b : Bicone F)

/-- The coordinate projections and injections of a finite bilimit resolve its identity.
Additive inverses are unnecessary. -/
theorem total (hb : b.IsBilimit) : ∑ i, b.π i ≫ b.ι i = 𝟙 b.pt := by
  apply hb.isLimit.hom_ext
  rintro ⟨j⟩
  change (∑ i, b.π i ≫ b.ι i) ≫ b.π j = 𝟙 b.pt ≫ b.π j
  rw [Semiadditive.sum_comp, Finset.sum_eq_single j]
  · simp only [Category.assoc, bicone_ι_π_self, Category.comp_id, Category.id_comp]
  · intro i _ hij
    rw [Category.assoc, bicone_ι_π_ne b hij, comp_zero]
  · intro h
    exact (h (Finset.mem_univ j)).elim

end Limits.Bicone

end CategoryTheory
