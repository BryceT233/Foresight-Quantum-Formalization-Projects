/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.OfBiproducts

/-!
# Semiadditive categories

A superposition rule, as in Definition 2.12, equips each hom-set with a commutative monoid
whose addition and zero are preserved by composition in both variables. This is weaker than
Mathlib's `Preadditive`, which requires additive inverses. In particular, it includes the union
of relations as well as the sum of linear maps.

## Main definitions

* `Semiadditive`: commutative-monoid superposition compatible with composition.
* `Semiadditive.ofPreadditive`: the superposition rule of a preadditive category.
* `Semiadditive.ofHasBinaryBiproducts`: the commutative-monoid superposition determined by
  binary biproducts, selected explicitly.

## Main results

* `Semiadditive.add_eq_lift_id_desc`, `Semiadditive.add_eq_lift_desc_id`: addition is determined
  by binary biproducts, without requiring additive inverses or changing the given addition.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe u v

/-- A **semiadditive category** has commutative-monoid hom-sets, and composition preserves
addition and zero in each variable. This is the superposition rule of Definition 2.12. -/
class Semiadditive (C : Type u) [Category.{v} C] where
  /-- The commutative monoid structure on each hom-set. -/
  homMonoid : ∀ X Y : C, AddCommMonoid (X ⟶ Y) := by infer_instance
  /-- Composition distributes over addition in its first variable. -/
  add_comp : ∀ (X Y Z : C) (f g : X ⟶ Y) (h : Y ⟶ Z),
    (f + g) ≫ h = f ≫ h + g ≫ h
  /-- Composition distributes over addition in its second variable. -/
  comp_add : ∀ (X Y Z : C) (f : X ⟶ Y) (g h : Y ⟶ Z),
    f ≫ (g + h) = f ≫ g + f ≫ h
  /-- Composition preserves zero in its first variable. -/
  zero_comp : ∀ (X Y Z : C) (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = 0
  /-- Composition preserves zero in its second variable. -/
  comp_zero : ∀ (X Y Z : C) (f : X ⟶ Y), f ≫ (0 : Y ⟶ Z) = 0

attribute [instance_reducible, instance 100] Semiadditive.homMonoid

namespace Semiadditive

variable {C : Type u} [Category.{v} C]

/-- Additive inverses are unnecessary for a preadditive category's superposition rule. -/
instance (priority := 100) ofPreadditive [Preadditive C] : Semiadditive C where
  homMonoid X Y := (Preadditive.homGroup X Y).toAddCommMonoid
  add_comp _ _ _ f g h := Preadditive.add_comp _ _ _ f g h
  comp_add _ _ _ f g h := Preadditive.comp_add _ _ _ f g h
  zero_comp _ _ _ f := Limits.zero_comp (f := f)
  comp_zero _ _ _ f := Limits.comp_zero (f := f)

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

/-- The zeros of the hom-set monoids are zero morphisms. -/
instance (priority := 90) hasZeroMorphisms : HasZeroMorphisms C where
  zero X Y := (homMonoid X Y).toZero
  zero_comp _ _ _ f := Semiadditive.zero_comp _ _ _ f
  comp_zero f _ := Semiadditive.comp_zero _ _ _ f

attribute [reassoc, simp] add_comp
attribute [simp] comp_add

/-- Endomorphisms in a semiadditive category form a semiring. Its addition is the given
superposition rule, and its multiplication is reversed categorical composition. -/
instance (priority := 100) endSemiring {X : C} : Semiring (End X) :=
  { End.monoid, (homMonoid X X : AddCommMonoid (End X)) with
    zero_mul := fun _ ↦ Limits.comp_zero
    mul_zero := fun _ ↦ Limits.zero_comp
    left_distrib := fun f g h ↦ Semiadditive.add_comp X X X g h f
    right_distrib := fun f g h ↦ Semiadditive.comp_add X X X h f g }

/-- Precomposition with a morphism as a homomorphism of commutative monoids. -/
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →+ (X ⟶ Z) where
  toFun g := f ≫ g
  map_zero' := Limits.comp_zero
  map_add' _ _ := Semiadditive.comp_add _ _ _ _ _ _

/-- Postcomposition with a morphism as a homomorphism of commutative monoids. -/
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →+ (X ⟶ Z) where
  toFun f := f ≫ g
  map_zero' := Limits.zero_comp
  map_add' _ _ := Semiadditive.add_comp _ _ _ _ _ _

/-- Composition distributes over a finite sum in its second variable. -/
@[reassoc]
lemma comp_sum {X Y Z : C} {ι : Type*} (s : Finset ι) (f : X ⟶ Y) (g : ι → (Y ⟶ Z)) :
    f ≫ ∑ i ∈ s, g i = ∑ i ∈ s, f ≫ g i :=
  map_sum (leftComp Z f) g s

/-- Composition distributes over a finite sum in its first variable. -/
@[reassoc]
lemma sum_comp {X Y Z : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) (g : Y ⟶ Z) :
    (∑ i ∈ s, f i) ≫ g = ∑ i ∈ s, f i ≫ g :=
  map_sum (rightComp X g) f s

/-- A binary biproduct's row map is the sum of its two components. -/
lemma desc_eq_add {X Y Z : C} [HasBinaryBiproduct X Y] (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g := by
  apply biprod.hom_ext'
  · simp
  · simp

/-- A binary biproduct's column map is the sum of its two components. -/
lemma lift_eq_add {X Y Z : C} [HasBinaryBiproduct X Y] (f : Z ⟶ X) (g : Z ⟶ Y) :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
  apply biprod.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

/-- Addition is the diagonal followed by the row map of a binary biproduct. -/
lemma add_eq_lift_id_desc {X Y : C} [HasBinaryBiproduct X X] (f g : X ⟶ Y) :
    f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g := by
  simp [desc_eq_add]

/-- Addition is the column map followed by the codiagonal of a binary biproduct. -/
lemma add_eq_lift_desc_id {X Y : C} [HasBinaryBiproduct Y Y] (f g : X ⟶ Y) :
    f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) := by
  simp [lift_eq_add, Category.assoc]

end Semiadditive

end CategoryTheory
