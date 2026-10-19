/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.RelCat.SetRel
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The monoidal structure on the category of relations

The tensor product of `RelCat` is the cartesian product of types, and the tensor unit is
`PUnit`. The structural isomorphisms are the graphs of `Equiv.prodAssoc`, `Equiv.punitProd` and
`Equiv.prodPUnit`.

The monoidal structure does not use the superposition rule: `FQFP.CQM.RelCat.Semiadditive`
is an independent sibling, not a prerequisite of this file.

## Main definitions

* `RelCat.instMonoidalCategoryStructRelCat`, `RelCat.instMonoidalCategoryRelCat`: the monoidal
  structure on `RelCat`.

## Main results

* `RelCat.tensorObj_def`, `RelCat.tensorUnit_def` and the `rel_*` lemmas: the tensor product,
  whiskerings and structural isomorphisms on underlying relations.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonoidalCategory

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

/-! ### Monoidal structure and structural membership lemmas -/

/-- The monoidal category structure on `RelCat`: the tensor product is the cartesian
product of types, and the tensor unit is `PUnit`. -/
instance instMonoidalCategoryStructRelCat : MonoidalCategoryStruct RelCat.{u} where
  tensorObj X Y := X × Y
  whiskerLeft _ _ _ f := .ofRel {((x, y₁), (x', y₂)) | x = x' ∧ (y₁, y₂) ∈ f.rel}
  whiskerRight f _ := .ofRel {((x, y), (x', y')) | (x, x') ∈ f.rel ∧ y = y'}
  tensorHom f g := .ofRel {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel}
  tensorUnit := PUnit
  associator X Y Z := graphFunctor.mapIso (Equiv.prodAssoc X Y Z).toIso
  leftUnitor X := graphFunctor.mapIso (Equiv.punitProd X).toIso
  rightUnitor X := graphFunctor.mapIso (Equiv.prodPUnit X).toIso

@[simp] lemma tensorObj_def (X Y : RelCat.{u}) : (X ⊗ Y : RelCat.{u}) = (X × Y) := rfl

@[simp] lemma tensorUnit_def : (𝟙_ RelCat.{u} : RelCat.{u}) = PUnit.{u + 1} := rfl

@[simp] lemma rel_tensorHom {X₁ Y₁ X₂ Y₂ : RelCat.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel} := rfl

@[simp] lemma rel_whiskerLeft (f : Y ⟶ Z) :
    (X ◁ f).rel = {p | p.1.1 = p.2.1 ∧ (p.1.2, p.2.2) ∈ f.rel} := rfl

@[simp] lemma rel_whiskerRight (f : X ⟶ Y) :
    (f ▷ Z).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ p.1.2 = p.2.2} := rfl

@[simp] lemma rel_associator_hom :
    (α_ X Y Z).hom.rel = {p | (p.1.1.1, p.1.1.2, p.1.2) = p.2} := rfl

@[simp] lemma rel_associator_inv :
    (α_ X Y Z).inv.rel = {p | ((p.1.1, p.1.2.1), p.1.2.2) = p.2} := rfl

@[simp] lemma rel_leftUnitor_hom : (λ_ X).hom.rel = {p | p.1.2 = p.2} := rfl

@[simp] lemma rel_leftUnitor_inv : (λ_ X).inv.rel = {p | (PUnit.unit, p.1) = p.2} := rfl

@[simp] lemma rel_rightUnitor_hom : (ρ_ X).hom.rel = {p | p.1.1 = p.2} := rfl

@[simp] lemma rel_rightUnitor_inv : (ρ_ X).inv.rel = {p | (p.1, PUnit.unit) = p.2} := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `RelCat` is a monoidal category. -/
instance instMonoidalCategoryRelCat : MonoidalCategory RelCat.{u} where
  tensorHom_def f g := by
    ext ⟨u, v⟩
    simp only [Set.mem_ofPred_eq, rel_tensorHom, Hom.rel_comp, rel_whiskerRight, rel_whiskerLeft]
    constructor
    · rintro ⟨hf, hg⟩
      exact ⟨(v.1, u.2), ⟨hf, rfl⟩, ⟨rfl, hg⟩⟩
    · rintro ⟨w, ⟨hf, h₂⟩, ⟨h₁, hg⟩⟩
      exact ⟨h₁ ▸ hf, h₂ ▸ hg⟩
  id_tensorHom_id X Y := by
    ext ⟨u, v⟩
    simp only [tensorObj_def, rel_tensorHom, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext ⟨u, w⟩
    simp; grind
  whiskerLeft_id X Y := by
    ext
    simp only [tensorObj_def, rel_whiskerLeft, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  id_whiskerRight X Y := by
    ext
    simp only [tensorObj_def, rel_whiskerRight, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  associator_naturality f₁ f₂ f₃ := by
    ext ⟨u, v⟩
    simp [Prod.ext_iff, and_assoc]
  leftUnitor_naturality f := by
    ext ⟨u, v⟩
    simp [Prod.exists]
  rightUnitor_naturality f := by
    ext ⟨u, v⟩
    simp [Prod.exists]
  pentagon W X Y Z := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]
  triangle X Y := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]

end CategoryTheory.RelCat
