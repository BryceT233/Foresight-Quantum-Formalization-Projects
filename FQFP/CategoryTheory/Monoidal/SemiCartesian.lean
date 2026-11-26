/-
Copyright (c) 2019 Kim Morrison, Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Simon Hudon, Adam Topaz, Robin Carlier
-/

/-
leanprover-community/mathlib4 @ fc4f59e577feb1a4956671bc04ac18aaaf8cd842
Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean
Generalize the tensorHom, associator and braiding projection laws to a terminal tensor unit.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
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

/-- Discarding the second joint output and an independent output keeps the first marginal. -/
lemma tensorHom_associator_hom_fst {S X Y R R' : C} (j : S ⟶ X ⊗ Y) (k : R ⟶ R') :
    ((j ⊗ₘ k) ≫ (α_ X Y R').hom) ≫ fst X (Y ⊗ R') = fst S R ≫ j ≫ fst X Y := by
  rw [Category.assoc, associator_hom_fst, ← Category.assoc, tensorHom_fst, Category.assoc]

/-- Discarding the first joint output retains the second marginal in parallel with
the independent process. -/
lemma tensorHom_associator_hom_snd {S X Y R R' : C} (j : S ⟶ X ⊗ Y) (k : R ⟶ R') :
    ((j ⊗ₘ k) ≫ (α_ X Y R').hom) ≫ snd X (Y ⊗ R') = (j ≫ snd X Y) ⊗ₘ k := by
  rw [Category.assoc, associator_hom_snd, ← tensorHom_id, tensorHom_comp_tensorHom,
    Category.comp_id]

/-- Keeping the first output of a coassociative splitting gives an idempotent.
This only requires coassociativity and the terminal tensor unit. -/
lemma comp_fst_idempotent_of_coassoc {X : C} (d : X ⟶ X ⊗ X)
    (hd : d ≫ (X ◁ d) = d ≫ (d ▷ X) ≫ (α_ X X X).hom) :
    (d ≫ fst X X) ≫ (d ≫ fst X X) = d ≫ fst X X := by
  have h := congrArg (· ≫ fst X (X ⊗ X)) hd
  simpa only [Category.assoc, associator_hom_fst, ← id_tensorHom, ← tensorHom_id,
    ← Category.assoc (d ⊗ₘ 𝟙 X), tensorHom_fst, Category.comp_id] using h.symm

variable [BraidedCategory C]

/-- Exchanging outputs turns the first projection into the second. -/
lemma braiding_hom_fst (X Y : C) : (β_ X Y).hom ≫ fst Y X = snd X Y := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_left_assoc]

/-- Exchanging outputs turns the second projection into the first. -/
lemma braiding_hom_snd (X Y : C) : (β_ X Y).hom ≫ snd Y X = fst X Y := by
  simp [fst_def, snd_def, ← BraidedCategory.braiding_naturality_right_assoc]

/-- Regrouping two pairs before discarding their second components gives the
tensor product of the two first projections. -/
lemma tensorμ_fst (W X Y Z : C) :
    tensorμ W X Y Z ≫ fst (W ⊗ Y) (X ⊗ Z) = fst W X ⊗ₘ fst Y Z := by
  let I := 𝟙_ C
  have hu : isTerminalTensorUnit.from (X ⊗ Z) = (toUnit X ⊗ₘ toUnit Z) ≫ (λ_ I).hom :=
    toUnit_unique ..
  simp only [fst_def]
  rw [hu, whiskerLeft_comp_assoc, ← id_tensorHom (W ⊗ Y),
    ← id_tensorHom_id W Y, ← tensorμ_natural_assoc, ← id_tensorHom, ← id_tensorHom,
    ← tensorHom_comp_tensorHom]
  congr 1
  · simp only [id_tensorHom, toUnit]
  · dsimp only [tensorμ, I]
    simp only [braiding_tensorUnit_left]
    monoidal

/-- Regrouping two pairs before discarding their first components gives the
tensor product of the two second projections. -/
lemma tensorμ_snd (W X Y Z : C) :
    tensorμ W X Y Z ≫ snd (W ⊗ Y) (X ⊗ Z) = snd W X ⊗ₘ snd Y Z := by
  let I := 𝟙_ C
  have hu : isTerminalTensorUnit.from (W ⊗ Y) = (toUnit W ⊗ₘ toUnit Y) ≫ (λ_ I).hom :=
    toUnit_unique ..
  simp only [snd_def]
  rw [hu, comp_whiskerRight_assoc, ← tensorHom_id, ← id_tensorHom_id X Z,
    ← tensorμ_natural_assoc, ← tensorHom_id, ← tensorHom_id, ← tensorHom_comp_tensorHom]
  congr 1
  · simp only [tensorHom_id, toUnit]
  · dsimp only [tensorμ, I]
    simp only [braiding_tensorUnit_right]
    monoidal

/-- A joint process invariant under exchange of its outputs has equal marginals. -/
lemma comp_fst_eq_comp_snd_of_swap {S X : C} (j : S ⟶ X ⊗ X)
    (hj : j ≫ (β_ X X).hom = j) : j ≫ fst X X = j ≫ snd X X := by
  rw [← braiding_hom_fst, ← Category.assoc, hj]

end CategoryTheory.SemiCartesianMonoidalCategory
