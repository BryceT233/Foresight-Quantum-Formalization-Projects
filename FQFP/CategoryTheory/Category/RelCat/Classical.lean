/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Monoidal.Frobenius
public import FQFP.CategoryTheory.Category.RelCat.Braided
public import FQFP.CategoryTheory.Category.RelCat.Rigid

/-!
# Discrete classical structures in relations

Every type has a classical structure given by diagonal copying and total deleting.
This is the discrete groupoid example, not a classification of relational classical structures.
In particular, no finiteness or nonemptiness assumption is imposed on the type.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DaggerCategory

namespace CategoryTheory.RelCat

-- Tensor objects are products of types behind the RelCat object wrapper.
set_option backward.isDefEq.respectTransparency.types false

/-- Diagonal copying as a relation. -/
def discreteCopy (X : RelCat.{u}) : X ⟶ X ⊗ X :=
  .ofRel {p | p.1 = p.2.1 ∧ p.1 = p.2.2}

/-- Total deleting as a relation to the tensor unit. -/
def discreteDelete (X : RelCat.{u}) : X ⟶ 𝟙_ RelCat.{u} :=
  .ofRel Set.univ

/-- Copying relates an input precisely to two equal copies of itself. -/
@[simp]
lemma mem_discreteCopy (X : RelCat.{u}) (x : X) (y : (X ⊗ X : RelCat.{u})) :
    (x, y) ∈ (discreteCopy X).rel ↔ x = y.1 ∧ x = y.2 := Iff.rfl

/-- Deleting accepts every input. -/
@[simp]
lemma mem_discreteDelete (X : RelCat.{u}) (x : X) (p : 𝟙_ RelCat.{u}) :
    (x, p) ∈ (discreteDelete X).rel := Set.mem_univ _

/-- The diagonal and total relations form a comonoid. -/
@[instance_reducible]
def discreteComonObj (X : RelCat.{u}) : ComonObj X where
  counit := discreteDelete X
  comul := discreteCopy X
  counit_comul := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp [Prod.exists, discreteCopy, discreteDelete, Prod.ext_iff]
  comul_counit := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp [Prod.exists, discreteCopy, discreteDelete, Prod.ext_iff]
  comul_assoc := by
    apply Hom.ext
    ext ⟨x, y⟩
    simp [Prod.exists, discreteCopy, Prod.ext_iff, and_assoc]

/-- The discrete classical structure on an arbitrary type. -/
def discreteClassicalStructure (X : RelCat.{u}) : ClassicalStructure X where
  toMonObj := (discreteComonObj X).dagger
  toComonObj := discreteComonObj X
  frobenius_left := by
    change (discreteCopy X ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ (discreteCopy X)†) =
      (discreteCopy X)† ≫ discreteCopy X
    apply Hom.ext
    ext ⟨x, y⟩
    simp [discreteCopy, Prod.exists, Prod.ext_iff]
    grind
  frobenius_right := by
    change (X ◁ discreteCopy X) ≫ (α_ X X X).inv ≫ ((discreteCopy X)† ▷ X) =
      (discreteCopy X)† ≫ discreteCopy X
    apply Hom.ext
    ext ⟨x, y⟩
    simp [discreteCopy, Prod.exists, Prod.ext_iff]
    grind
  dagger_mul := involutive_dagger _
  dagger_one := involutive_dagger _
  special := by
    change discreteCopy X ≫ (discreteCopy X)† = 𝟙 X
    apply Hom.ext
    ext ⟨x, y⟩
    simp [discreteCopy, Prod.exists]
  mul_comm := by
    change (β_ X X).hom ≫ (discreteCopy X)† = (discreteCopy X)†
    apply Hom.ext
    ext ⟨x, y⟩
    simp [discreteCopy, and_comm]
  comul_comm := by
    change discreteCopy X ≫ (β_ X X).hom = discreteCopy X
    apply Hom.ext
    ext ⟨x, y⟩
    simp [discreteCopy, Prod.exists, Prod.ext_iff, and_comm]

/-- The cup induced by the discrete classical structure is the existing diagonal cup. -/
lemma discreteClassicalStructure_cup (X : RelCat.{u}) :
    (discreteClassicalStructure X).cup = selfCoevaluation X := by
  change (discreteDelete X)† ≫ discreteCopy X = selfCoevaluation X
  apply Hom.ext
  ext ⟨p, y⟩
  simp [discreteCopy, discreteDelete, selfCoevaluation]

/-- The induced cap is the existing relational self-evaluation. -/
lemma discreteClassicalStructure_cap (X : RelCat.{u}) :
    (discreteClassicalStructure X).cap = selfEvaluation X := by
  rw [← (discreteClassicalStructure X).toDaggerFrobeniusObj.dagger_cup,
    discreteClassicalStructure_cup, dagger_selfCoevaluation]

end CategoryTheory.RelCat
