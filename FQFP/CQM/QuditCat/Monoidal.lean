/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.QuditCat.Basic
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The monoidal structure on the category of qudits

`FQFP.CQM.QuditCat.Basic` sets up `QuditCat`, the category of finite-dimensional complex
Hilbert spaces, together with its dagger structure. This file adds the tensor product: the
tensor product of two state spaces carries an inner product and a norm, so it is again an
object of `QuditCat`. The dagger is compatible with it, making `QuditCat` a monoidal dagger
category, and the monoidal structure is braided and symmetric.

## Main definitions

* The `MonoidalCategoryStruct`, `MonoidalCategory`, `MonoidalDaggerCategory`,
  `BraidedCategory` and `SymmetricCategory` instances on `QuditCat`.

## Main results

* `QuditCat` is a braided monoidal category, a symmetric monoidal category and a monoidal
  dagger category.
* `QuditCat.hom_tensorHom`, `QuditCat.hom_whiskerLeft`, `QuditCat.hom_whiskerRight` and the
  `hom_hom_*` and `hom_inv_*` companions compute the tensor product, the whiskerings, the
  associator and the unitors on underlying linear maps.
* `QuditCat.tensorHom_tmul`, `QuditCat.whiskerLeft_apply`, `QuditCat.associator_hom_apply`
  and `QuditCat.leftUnitor_hom_apply`, together with their companions, compute them on pure
  tensors of state spaces.

## Implementation notes

The whiskerings are the primitive data of the `MonoidalCategoryStruct` instance, and its
default then defines `tensorHom` from them. This is why `hom_tensorHom` is a proof rather
than `rfl`, in contrast with `Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`, which
supplies `tensorHom` explicitly.

Every lemma below is `rfl`; they nevertheless have to be stated. `simp` and `rw` match
syntactically and cannot unfold the `MonoidalCategoryStruct` projection, so without them a
goal such as `(f ⊗ₘ g) (x ⊗ₜ y) = f x ⊗ₜ g y` is definitionally true yet no rewrite fires.

`leftUnitor_inv_apply` and `rightUnitor_inv_apply` are deliberately not `@[simp]`, although
their `ModuleCat` counterparts are: expanding `(λ_ X).inv` to `1 ⊗ₜ ·` blocks
`leftUnitor_hom_apply` on the `𝟙_ ◁ f` normal form that `MonoidalCategory.id_whiskerLeft`
produces.
-/

@[expose] public section

open CategoryTheory

namespace QuditCat

open DaggerCategory

noncomputable section

open TensorProduct MonoidalCategory

instance : MonoidalCategoryStruct QuditCat where
  tensorObj H₁ H₂ := of (H₁.state ⊗[ℂ] H₂.state)
  whiskerLeft _ _ _ f := ofHom (TensorProduct.map LinearMap.id f.hom)
  whiskerRight f _ := ofHom (TensorProduct.map f.hom LinearMap.id)
  tensorUnit := of ℂ
  associator X Y Z := isoMk (TensorProduct.assoc ℂ X.state Y.state Z.state)
  leftUnitor X := isoMk (TensorProduct.lid ℂ X.state)
  rightUnitor X := isoMk (TensorProduct.rid ℂ X.state)

lemma hom_tensorHom {X₁ Y₁ X₂ Y₂ : QuditCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom := by
  change ((f ▷ X₂) ≫ (Y₁ ◁ g)).hom = _
  simp only [hom_comp]
  apply TensorProduct.ext'
  intros; rfl

lemma state_tensorObj (X Y : QuditCat) : (X ⊗ Y).state = X.state ⊗[ℂ] Y.state := rfl

lemma state_tensorUnit : (𝟙_ QuditCat : QuditCat).state = ℂ := rfl

lemma hom_whiskerLeft (X : QuditCat) {Y Z : QuditCat} (f : Y ⟶ Z) :
    (X ◁ f).hom = TensorProduct.map LinearMap.id f.hom := rfl

lemma hom_whiskerRight {X Y : QuditCat} (f : X ⟶ Y) (Z : QuditCat) :
    (f ▷ Z).hom = TensorProduct.map f.hom LinearMap.id := rfl

lemma hom_hom_associator (X Y Z : QuditCat) :
    (α_ X Y Z).hom.hom = (TensorProduct.assoc ℂ X.state Y.state Z.state).toLinearMap := rfl

lemma hom_inv_associator (X Y Z : QuditCat) :
    (α_ X Y Z).inv.hom = (TensorProduct.assoc ℂ X.state Y.state Z.state).symm.toLinearMap := rfl

lemma hom_hom_leftUnitor (X : QuditCat) :
    (λ_ X).hom.hom = (TensorProduct.lid ℂ X.state).toLinearMap := rfl

lemma hom_inv_leftUnitor (X : QuditCat) :
    (λ_ X).inv.hom = (TensorProduct.lid ℂ X.state).symm.toLinearMap := rfl

lemma hom_hom_rightUnitor (X : QuditCat) :
    (ρ_ X).hom.hom = (TensorProduct.rid ℂ X.state).toLinearMap := rfl

lemma hom_inv_rightUnitor (X : QuditCat) :
    (ρ_ X).inv.hom = (TensorProduct.rid ℂ X.state).symm.toLinearMap := rfl

@[simp]
lemma tensorHom_tmul {X₁ Y₁ X₂ Y₂ : QuditCat} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x : X₁.state) (y : X₂.state) : (f ⊗ₘ g) (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

@[simp]
lemma whiskerLeft_apply (X : QuditCat) {Y Z : QuditCat} (f : Y ⟶ Z)
    (x : X.state) (y : Y.state) : (X ◁ f) (x ⊗ₜ y) = x ⊗ₜ f y := rfl

@[simp]
lemma whiskerRight_apply {X Y : QuditCat} (f : X ⟶ Y) (Z : QuditCat)
    (x : X.state) (z : Z.state) : (f ▷ Z) (x ⊗ₜ z) = f x ⊗ₜ z := rfl

@[simp]
lemma associator_hom_apply (X Y Z : QuditCat) (x : X.state) (y : Y.state) (z : Z.state) :
    (α_ X Y Z).hom ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) := rfl

@[simp]
lemma associator_inv_apply (X Y Z : QuditCat) (x : X.state) (y : Y.state) (z : Z.state) :
    (α_ X Y Z).inv (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z := rfl

@[simp]
lemma leftUnitor_hom_apply (X : QuditCat) (c : ℂ) (x : X.state) :
    (λ_ X).hom (c ⊗ₜ x) = c • x := rfl

@[simp]
lemma rightUnitor_hom_apply (X : QuditCat) (x : X.state) (c : ℂ) :
    (ρ_ X).hom (x ⊗ₜ c) = c • x := rfl

-- Deliberately not `@[simp]`: expanding `(λ_ X).inv` to `1 ⊗ₜ ·` blocks
-- `leftUnitor_hom_apply` on the `𝟙_ ◁ f` normal form produced by
-- `MonoidalCategory.id_whiskerLeft`. Mathlib marks the `ModuleCat` versions `@[simp]`,
-- but there the trade-off does not arise.
lemma leftUnitor_inv_apply (X : QuditCat) (x : X.state) : (λ_ X).inv x = (1 : ℂ) ⊗ₜ x := rfl

lemma rightUnitor_inv_apply (X : QuditCat) (x : X.state) : (ρ_ X).inv x = x ⊗ₜ (1 : ℂ) := rfl

instance : MonoidalCategory QuditCat where
  id_tensorHom_id X₁ X₂ := hom_ext <| by
    rw [hom_tensorHom, hom_id, hom_id]
    exact TensorProduct.map_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := hom_ext <| by
    rw [hom_comp, hom_tensorHom, hom_tensorHom, hom_tensorHom, hom_comp, hom_comp]
    exact (TensorProduct.map_comp g₁.hom g₂.hom f₁.hom f₂.hom).symm
  whiskerLeft_id X Y := hom_ext <| by
    rw [hom_whiskerLeft, hom_id]
    exact TensorProduct.map_id
  id_whiskerRight X Y := hom_ext <| by
    rw [hom_whiskerRight, hom_id]
    exact TensorProduct.map_id
  associator_naturality f₁ f₂ f₃ := hom_ext <| by
    apply TensorProduct.ext_threefold
    intros; rfl
  leftUnitor_naturality {X Y} f := hom_ext <| by
    apply TensorProduct.ext'
    intro c x
    change TensorProduct.lid ℂ Y.state (TensorProduct.map LinearMap.id f.hom (c ⊗ₜ x)) =
      f.hom (TensorProduct.lid ℂ X.state (c ⊗ₜ x))
    simp
  rightUnitor_naturality {X Y} f := hom_ext <| by
    apply TensorProduct.ext'
    intro x c
    change TensorProduct.rid ℂ Y.state (TensorProduct.map f.hom LinearMap.id (x ⊗ₜ c)) =
      f.hom (TensorProduct.rid ℂ X.state (x ⊗ₜ c))
    simp
  pentagon _ _ _ _ := hom_ext <| by
    apply TensorProduct.ext_fourfold
    intros; rfl
  triangle _ _ := hom_ext <| by
    apply TensorProduct.ext_threefold
    intros; exact TensorProduct.tmul_smul ..

instance monoidalDaggerCategory : MonoidalDaggerCategory QuditCat where
  dagger_tensor f₁ f₂ := by
    apply hom_ext
    rw [hom_dagger, hom_tensorHom f₁ f₂, hom_tensorHom f₁† f₂†]
    exact adjoint_map f₁.hom f₂.hom
  isUnitary_associator H₁ H₂ H₃ := by
    dsimp [associator]
    rw [← toLinearEquiv_assocIsometry]
    exact isUnitary_isoMk_coe_LIEquiv ..
  isUnitary_leftUnitor H := by
    dsimp [leftUnitor]
    rw [← toLinearEquiv_lidIsometry]
    exact isUnitary_isoMk_coe_LIEquiv ..
  isUnitary_rightUnitor H := by
    dsimp [rightUnitor]
    rw [← toLinearEquiv_ridIsometry]
    exact isUnitary_isoMk_coe_LIEquiv ..

instance : BraidedCategory QuditCat where
  braiding H₁ H₂ := isoMk (TensorProduct.comm ..)
  braiding_naturality_left f H := hom_ext <| by
    apply TensorProduct.ext'
    intros; rfl
  braiding_naturality_right H f K g := hom_ext <| by
    apply TensorProduct.ext'
    intros; rfl
  hexagon_forward H K L := hom_ext <| by
    apply TensorProduct.ext_threefold
    intros; rfl
  hexagon_reverse H K L := hom_ext <| by
    apply TensorProduct.ext_threefold'
    intros; rfl

instance symmetricCategory : SymmetricCategory QuditCat where
  symmetry H₁ H₂ := hom_ext <| by
    rw [hom_comp, hom_id]
    exact TensorProduct.comm_comp_comm ..

end

end QuditCat
