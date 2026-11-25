/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Scalars in a monoidal category

Scalars are endomorphisms of the tensor unit. They commute and act on morphisms.

## Main definitions

* `MonoidalCategory.Scalar`: the endomorphisms of the tensor unit.

## Main results

* `MonoidalCategory.smul_assoc`: associativity of the scalar action.
* `MonoidalCategory.smul_comp_smul`: interchange with composition.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section Scalars

/-- The scalars of a monoidal category `C`, i.e. the endomorphisms of its monoidal unit
`𝟙_ C`. They form a commutative monoid (see the instance below) and act on every hom-set by
scalar multiplication (see the `SMul` instance below). -/
abbrev Scalar (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] : Type _ := End (𝟙_ C)

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance : CommMonoid (Scalar C) where
  mul_comm s t := by
    ext
    simpa [unitors_equal, unitors_inv_equal] using
      congrArg (fun f => (ρ_ (𝟙_ C)).inv ≫ f ≫ (ρ_ (𝟙_ C)).hom)
        (whisker_exchange s.asHom t.asHom)

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s.asHom ⊗ₘ f) ≫ (λ_ c₂).hom

/-- The scalar action of `s : Scalar C` on a morphism `f : c₁ ⟶ c₂` is given by tensoring
with `s` and transporting across the left unitors. -/
lemma smul_def {c₁ c₂ : C} {s : Scalar C} {f : c₁ ⟶ c₂} :
    s • f = (λ_ c₁).inv ≫ (s.asHom ⊗ₘ f) ≫ (λ_ c₂).hom := rfl

/-- Scalar multiplication is associative: acting on a morphism by `s` then `t` agrees with
acting by the scalar product `t * s`. -/
lemma smul_assoc {c₁ c₂ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} : s • t • f = (t * s) • f := by
  simp [smul_def, tensorHom_def, End.mul_asHom]

/-- The action of categorical scalars on each hom-set (Lemma 2.6). -/
instance {X Y : C} : MulAction (Scalar C) (X ⟶ Y) where
  one_smul f := by simp [smul_def]
  mul_smul s t f := by rw [smul_assoc, mul_comm]

/-- Acting on a scalar arrow gives multiplication in the scalar monoid (Lemma 2.6(b)). -/
lemma scalar_smul_asHom (s t : Scalar C) : s • t.asHom = (s * t).asHom := by
  rw [mul_comm, End.mul_asHom, smul_def, tensorHom_def, Category.assoc, leftUnitor_naturality,
    unitors_equal, unitors_inv_equal, rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

/-- Scalar multiplication satisfies the interchange law with composition:
`(s • f) ≫ (t • g) = (s * t) • (f ≫ g)`. -/
lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  rw [mul_comm s t]
  simp [smul_def, End.mul_asHom]

/-- A scalar on the first process scales the composite. -/
lemma scalar_smul_comp {X Y Z : C} (s : Scalar C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (s • f) ≫ g = s • (f ≫ g) := by
  simpa only [one_smul, mul_one] using smul_comp_smul (s := s) (t := 1) (f := f) (g := g)

/-- A scalar on the second process scales the composite. -/
lemma comp_scalar_smul {X Y Z : C} (s : Scalar C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ (s • g) = s • (f ≫ g) := by
  simpa only [one_smul, one_mul] using smul_comp_smul (s := 1) (t := s) (f := f) (g := g)

/-- A scalar followed by a preparation is the scalar action on that preparation. -/
lemma scalar_asHom_comp {X : C} (s : Scalar C) (a : 𝟙_ C ⟶ X) : s.asHom ≫ a = s • a := by
  have h := scalar_smul_comp s (1 : Scalar C).asHom a
  rwa [scalar_smul_asHom, mul_one, End.one_asHom, Category.id_comp] at h

/-- A left scalar on the first tensor factor scales the whole process. -/
lemma scalar_smul_whiskerRight {X Y : C} (s : Scalar C) (f : X ⟶ Y) (Z : C) :
    (s • f) ▷ Z = s • (f ▷ Z) := by
  simp only [smul_def, comp_whiskerRight, leftUnitor_tensor_inv, leftUnitor_tensor_hom,
    Category.assoc]
  simp only [← tensorHom_id, associator_inv_naturality_assoc, Iso.hom_inv_id_assoc]

/-- Braiding allows a left scalar on the second factor to pass the first factor. -/
lemma whiskerLeft_scalar_smul [BraidedCategory C] (X : C) {Y Z : C} (s : Scalar C) (f : Y ⟶ Z) :
    X ◁ (s • f) = s • (X ◁ f) := by
  apply (cancel_mono (β_ X Z).hom).mp
  rw [BraidedCategory.braiding_naturality_right, scalar_smul_whiskerRight, comp_scalar_smul,
    scalar_smul_comp, BraidedCategory.braiding_naturality_right]

/-- In a braided category, parallel processes contribute the product of their scalars. -/
lemma scalar_smul_tensorHom_scalar_smul [BraidedCategory C] {X Y X' Y' : C} (s t : Scalar C)
    (f : X ⟶ Y) (g : X' ⟶ Y') : (s • f) ⊗ₘ (t • g) = (s * t) • (f ⊗ₘ g) := by
  simp only [tensorHom_def, scalar_smul_whiskerRight, whiskerLeft_scalar_smul, smul_comp_smul]

end Scalars

end CategoryTheory.MonoidalCategory
