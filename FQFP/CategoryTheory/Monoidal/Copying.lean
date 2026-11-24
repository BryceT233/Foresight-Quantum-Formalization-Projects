/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.State

/-!
# Copyable states

The tensor product of preparations gives the product states of §1.1.3 of
*Categorical Quantum Mechanics*. Definition 4.23 asks whether a specified map
prepares this product from a single input.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- A state is copyable by a given map when its output is two independent copies
(Definition 4.23). The equation makes sense in any monoidal category. -/
def State.IsCopyable {X : C} (a : State X) (d : X ⟶ X ⊗ X) : Prop :=
  a ≫ d = a.tensor a

/-- A map intertwining two copying maps takes copyable states to copyable states. -/
lemma State.IsCopyable.comp {X Y : C} {a : State X} {d : X ⟶ X ⊗ X} {e : Y ⟶ Y ⊗ Y}
    (ha : a.IsCopyable d) (f : X ⟶ Y) (hf : f ≫ e = d ≫ (f ⊗ₘ f)) :
    State.IsCopyable (a ≫ f) e := by
  change (a ≫ f) ≫ e = _
  rw [Category.assoc, hf, ← Category.assoc, show a ≫ d = _ from ha, State.tensor_comp]

/-- A natural family of copying maps with the prescribed map on the tensor unit
copies every state (the forward implication of Proposition 4.24). -/
lemma State.isCopyable_of_natural (d : (X : C) → (X ⟶ X ⊗ X))
    (hnat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ d Y = d X ≫ (f ⊗ₘ f))
    (hunit : d (𝟙_ C) = (λ_ (𝟙_ C)).inv) {X : C} (a : State X) : a.IsCopyable (d X) := by
  rw [State.IsCopyable, State.tensor, hnat a, hunit]

end CategoryTheory.MonoidalCategory
