/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Sliding along an explicit exact pairing

The identity uses an arbitrary exact pairing and does not require a dagger.

## Main results

* `tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing`: sliding a map past evaluation.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {L R : C} [ExactPairing R L]

/-- Sliding an effect along the pairing: the transposed branch effect `V ▷ R ≫ ε` is the
transpose of `V`. This is the explicit-pairing form of Mathlib's
`tensorRightHomEquiv_whiskerRight_comp_evaluation`. -/
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing (V : L ⟶ L) :
    (tensorRightHomEquiv L R L (𝟙_ C)) ((V ▷ R) ≫ ε_ R L) = V ≫ (λ_ L).inv := by
  calc
    _ = 𝟙 _ ⊗≫ (L ◁ η_ R L ≫ V ▷ (R ⊗ L)) ⊗≫ ε_ R L ▷ L := by
      dsimp [tensorRightHomEquiv]
      monoidal
    _ = V ⊗≫ (L ◁ η_ R L ⊗≫ ε_ R L ▷ L) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

end CategoryTheory
