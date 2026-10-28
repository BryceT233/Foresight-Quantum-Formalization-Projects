/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Endomorphism
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

/-- Scalar multiplication satisfies the interchange law with composition:
`(s • f) ≫ (t • g) = (s * t) • (f ≫ g)`. -/
lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  rw [mul_comm s t]
  simp [smul_def, End.mul_asHom]

end Scalars

end CategoryTheory.MonoidalCategory
