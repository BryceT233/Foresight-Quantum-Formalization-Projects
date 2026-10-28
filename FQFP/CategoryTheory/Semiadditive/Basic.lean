/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Semiadditive categories

Hom-sets carry commutative-monoid addition compatible with composition, without inverses.

## Main results

* `Semiadditive`: commutative-monoid superposition.
* `Semiadditive.ofPreadditive`: the preadditive specialization.
* `Semiadditive.endSemiring`: the semiring of endomorphisms.
* `Semiadditive.comp_sum`, `Semiadditive.sum_comp`: finite-sum composition.
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

variable [Semiadditive C]

/-- The zeros of the hom-set monoids are zero morphisms. -/
instance (priority := 90) hasZeroMorphisms : HasZeroMorphisms C where
  zero X Y := (homMonoid X Y).toZero
  zero_comp _ _ _ f := Semiadditive.zero_comp _ _ _ f
  comp_zero f _ := Semiadditive.comp_zero _ _ _ f

attribute [reassoc, simp] add_comp
attribute [simp] comp_add

/-- Endomorphisms inherit the commutative-monoid superposition rule of their hom-set. -/
@[simps!]
instance (priority := 100) endAddCommMonoid {X : C} : AddCommMonoid (End X) :=
  End.homEquiv.addCommMonoid

/-- The additive bijection between endomorphisms and their underlying morphisms. -/
@[simps!]
def endAddEquiv {X : C} : End X ≃+ (X ⟶ X) where
  toEquiv := End.homEquiv
  map_add' _ _ := rfl

/-- Taking the underlying morphism preserves finite sums of endomorphisms. -/
@[simp]
lemma end_sum_asHom {X : C} {ι : Type*} (s : Finset ι) (f : ι → End X) :
    (∑ i ∈ s, f i).asHom = ∑ i ∈ s, (f i).asHom :=
  map_sum endAddEquiv ..

/-- Endomorphisms in a semiadditive category form a semiring. Its addition is the given
superposition rule, and its multiplication is reversed categorical composition. -/
instance (priority := 100) endSemiring {X : C} : Semiring (End X) :=
  { End.monoid, (inferInstance : AddCommMonoid (End X)) with
    zero_mul := fun f ↦ End.ext (Limits.comp_zero (f := f.asHom))
    mul_zero := fun f ↦ End.ext (Limits.zero_comp (f := f.asHom))
    left_distrib := fun f g h ↦ End.ext (Semiadditive.add_comp X X X g.asHom h.asHom f.asHom)
    right_distrib := fun f g h ↦ End.ext (Semiadditive.comp_add X X X h.asHom f.asHom g.asHom) }

/-- Precomposition with a morphism as a homomorphism of commutative monoids. -/
def leftComp {X Y : C} (Z : C) (f : X ⟶ Y) : (Y ⟶ Z) →+ (X ⟶ Z) where
  toFun g := f ≫ g
  map_zero' := Limits.comp_zero
  map_add' _ _ := Semiadditive.comp_add ..

/-- Postcomposition with a morphism as a homomorphism of commutative monoids. -/
def rightComp (X : C) {Y Z : C} (g : Y ⟶ Z) : (X ⟶ Y) →+ (X ⟶ Z) where
  toFun f := f ≫ g
  map_zero' := Limits.zero_comp
  map_add' _ _ := Semiadditive.add_comp ..

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

end Semiadditive

end CategoryTheory
