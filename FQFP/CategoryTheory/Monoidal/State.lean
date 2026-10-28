/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# States and effects in a monoidal category

States are arrows from the tensor unit and effects are arrows into it.
These notions and product-state entanglement require only a monoidal category.

## Main definitions

* `MonoidalCategory.State`, `MonoidalCategory.JointState`: states and joint states.
* `MonoidalCategory.JointState.Entangled`: a joint state that is not a product state.
* `MonoidalCategory.Effect`: an arrow to the tensor unit.

## Main results

* `MonoidalCategory.JointState.not_entangled_iff`: a non-entangled state is a product state.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section States

/-- A state of an object `c` is a morphism from the monoidal unit `𝟙_ C` into `c`. -/
abbrev State (c : C) : Type _ := 𝟙_ C ⟶ c

/-- A joint state of two objects `c₁` and `c₂` is a morphism from the monoidal unit `𝟙_ C`
into their tensor product `c₁ ⊗ c₂`. -/
abbrev JointState (c₁ c₂ : C) : Type _ := 𝟙_ C ⟶ c₁ ⊗ c₂

/-- A joint state `f : JointState c₁ c₂` is entangled if it is not a product state, i.e. if
it cannot be written as `(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g : State c₁` and
`h : State c₂`. -/
def JointState.Entangled {c₁ c₂ : C} (f : JointState c₁ c₂) : Prop :=
  ∀ (g : State c₁) (h : State c₂), f ≠ (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)

/-- A joint state is not entangled iff it is a product state, i.e. of the form
`(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g` and `h`. -/
lemma JointState.not_entangled_iff {c₁ c₂ : C} (f : JointState c₁ c₂) :
    ¬ f.Entangled ↔ ∃ (g : State c₁) (h : State c₂), f = (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h) := by
  simp [JointState.Entangled]

end States

/-- An effect on an object `c` is a morphism from `c` into the monoidal unit `𝟙_ C`. -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

end CategoryTheory.MonoidalCategory
