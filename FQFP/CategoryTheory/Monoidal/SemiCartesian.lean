/-
Copyright (c) 2019 Kim Morrison, Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon, Adam Topaz, Robin Carlier
-/

/-
leanprover-community/mathlib4 @ fc4f59e577feb1a4956671bc04ac18aaaf8cd842
Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean
Generalize the tensorHom, associator and braiding projection laws to a terminal tensor unit.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Marginals in a semicartesian monoidal category

The projections discard one output of a tensor. Their naturality applies even when
a joint process is not determined by its marginals, as happens for quantum channels.
-/

@[expose] public section

namespace CategoryTheory.SemiCartesianMonoidalCategory

open MonoidalCategory

variable {C : Type*} [Category* C] [SemiCartesianMonoidalCategory C]

/-- The first output marginal depends only on the first local process. -/
lemma tensorHom_fst {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ fst X' Y' = fst X Y ≫ f := by
  simp [fst_def, tensorHom_def, ← whiskerLeft_comp_assoc, ← whisker_exchange_assoc]

/-- The second output marginal depends only on the second local process. -/
lemma tensorHom_snd {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ snd X' Y' = snd X Y ≫ g := by
  simp [snd_def, tensorHom_def', ← comp_whiskerRight_assoc, whisker_exchange_assoc]

/-- Discarding two outputs together agrees with discarding them in succession. -/
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst X (Y ⊗ Z) = fst (X ⊗ Y) Z ≫ fst X Y := by
  simp [fst_def, ← whiskerLeft_rightUnitor_assoc, -whiskerLeft_rightUnitor,
    ← whiskerLeft_comp_assoc]

/-- Discarding the first output commutes with reassociation. -/
lemma associator_hom_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd X (Y ⊗ Z) = snd X Y ▷ Z := by
  simp [snd_def, comp_whiskerRight]

/-- Discarding the last output commutes with inverse reassociation. -/
lemma associator_inv_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst (X ⊗ Y) Z = X ◁ fst Y Z := by
  simp [fst_def, whiskerLeft_comp]

variable [BraidedCategory C]

/-- Exchanging outputs turns the first projection into the second. -/
lemma braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst Y X = snd X Y := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

/-- Exchanging outputs turns the second projection into the first. -/
lemma braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd Y X = fst X Y := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

end CategoryTheory.SemiCartesianMonoidalCategory
