/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal dagger categories

The dagger respects tensor products and the associator and unitors are unitary.

## Main definitions

* `MonoidalDaggerCategory`: a monoidal category with a compatible dagger.

## Main results

* `MonoidalDaggerCategory.dagger_whiskerLeft` and
  `MonoidalDaggerCategory.dagger_whiskerRight`: the dagger respects whiskering.
-/

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

open DaggerCategory MonoidalCategory

/-- A dagger category that is also monoidal, with the dagger compatible with the tensor product
and the structural isomorphisms. -/
class CategoryTheory.MonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    DaggerCategory C, MonoidalCategory C where
  dagger_tensor {H₁ H₂ K₁ K₂ : C} (f₁ : H₁ ⟶ K₁) (f₂ : H₂ ⟶ K₂) : (f₁ ⊗ₘ f₂)† = f₁† ⊗ₘ f₂†
  isUnitary_associator (H₁ H₂ H₃ : C) : DaggerCategory.IsUnitary (α_ H₁ H₂ H₃).hom
  isUnitary_leftUnitor (H : C) : DaggerCategory.IsUnitary (λ_ H).hom
  isUnitary_rightUnitor (H : C) : DaggerCategory.IsUnitary (ρ_ H).hom

attribute [simp] MonoidalDaggerCategory.dagger_tensor

attribute [instance] MonoidalDaggerCategory.isUnitary_associator
MonoidalDaggerCategory.isUnitary_leftUnitor MonoidalDaggerCategory.isUnitary_rightUnitor

namespace CategoryTheory.MonoidalDaggerCategory

variable [MonoidalDaggerCategory C]

/-- Tensor products preserve self-adjointness. -/
theorem isSelfAdjoint_tensorHom {X Y : C} {A : End X} {B : End Y}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (End.of (A.asHom ⊗ₘ B.asHom)) := by
  apply End.ext
  change (A.asHom ⊗ₘ B.asHom)† = _
  rw [dagger_tensor, hA.dagger_asHom, hB.dagger_asHom]

/-- The tensor product of isometries is an isometry. -/
instance isIsometry_tensorHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsIsometry f] [IsIsometry g] : IsIsometry (f ⊗ₘ g) where
  comp_dagger_eq_id := by rw [dagger_tensor, tensorHom_comp_tensorHom]; simp

/-- The tensor product of unitaries is unitary. -/
instance isUnitary_tensorHom {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsUnitary f] [IsUnitary g] : IsUnitary (f ⊗ₘ g) where
  dagger_comp_eq_id := by rw [dagger_tensor, tensorHom_comp_tensorHom]; simp

/-- The dagger of a left whiskering is the left whiskering of the dagger. -/
@[simp]
lemma dagger_whiskerLeft {X Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : (X ◁ f)† = X ◁ f† := by
  have h : (X ◁ f : X ⊗ Y₁ ⟶ X ⊗ Y₂) = 𝟙 X ⊗ₘ f := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

/-- The dagger of a right whiskering is the right whiskering of the dagger. -/
@[simp]
lemma dagger_whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : (f ▷ Y)† = f† ▷ Y := by
  have h : (f ▷ Y : X₁ ⊗ Y ⟶ X₂ ⊗ Y) = f ⊗ₘ 𝟙 Y := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

end CategoryTheory.MonoidalDaggerCategory
