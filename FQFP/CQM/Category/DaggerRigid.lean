/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerCategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The dagger reverses an exact pairing

Let `C` be a monoidal dagger category and let `ExactPairing X Y` be an exact pairing of `X` with
`Y`, with coevaluation `η : 𝟙_ C ⟶ X ⊗ Y` and evaluation `ε : Y ⊗ X ⟶ 𝟙_ C`. Then
`ε† : 𝟙_ C ⟶ Y ⊗ X` and `η† : X ⊗ Y ⟶ 𝟙_ C` form an exact pairing of `Y` with `X`: this is
Lemma 3.45 of Reutter–Vicary, *Categorical Quantum Mechanics* (`L ⊣ R ⇔ R ⊣ L`), and it is the
object-level statement that a right dual is also a left dual (and conversely) in a monoidal
dagger category.

The proof is a direct computation. Daggering the two triangle identities of `ExactPairing X Y`
and pushing the dagger inside with `dagger_comp`, `dagger_whiskerLeft`, `dagger_whiskerRight`
and the unitarity of `α_`, `λ_` and `ρ_` yields exactly the two triangle identities required of
`ExactPairing Y X` — note that **the dagger swaps the two identities**: the reversed
coevaluation/evaluation axiom is the dagger of `ExactPairing.evaluation_coevaluation`, and the
reversed evaluation/coevaluation axiom is the dagger of `ExactPairing.coevaluation_evaluation`.

## Main definitions

* `exactPairingDagger`: the reversed exact pairing `ExactPairing Y X` of `ExactPairing X Y`,
  with coevaluation `ε†` and evaluation `η†`.
* `BraidedMonoidalDaggerCategory` and `SymmetricMonoidalDaggerCategory`: the extensions with
  unitary braiding from Definition 2.37.

## Main results

* `exactPairingDagger_coevaluation`, `exactPairingDagger_evaluation`: the reversed coevaluation
  and evaluation are definitionally the daggers of the evaluation and the coevaluation.
* `MonoidalDaggerCategory.hasLeftDualOfHasRightDual`,
  `MonoidalDaggerCategory.hasRightDualOfHasLeftDual`: an object with a right dual has a left
  dual (its right dual) and conversely, with the choice made explicitly.
* `MonoidalDaggerCategory.leftRigidCategoryOfRightRigidCategory`,
  `MonoidalDaggerCategory.rightRigidCategoryOfLeftRigidCategory`,
  `MonoidalDaggerCategory.nonempty_rightRigidCategory_iff_nonempty_leftRigidCategory`: a
  monoidal dagger category is right rigid iff it is left rigid.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

open DaggerCategory MonoidalDaggerCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalDaggerCategory C]

section ExactPairingDagger

/-- **Lemma 3.45** (Reutter–Vicary, *Categorical Quantum Mechanics*). In a monoidal dagger
category the dagger of an exact pairing is an exact pairing with the roles of the two objects
exchanged: the reversed evaluation is the dagger of the coevaluation, and the reversed
coevaluation is the dagger of the evaluation. -/
@[instance_reducible]
def exactPairingDagger (X Y : C) (p : ExactPairing X Y) : ExactPairing Y X :=
  letI := p
  { coevaluation' := (ExactPairing.evaluation X Y)†
    evaluation' := (ExactPairing.coevaluation X Y)†
    coevaluation_evaluation' := by
      have h := congrArg dagger (ExactPairing.evaluation_coevaluation X Y)
      simpa only [Category.assoc, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight,
        dagger_hom_eq_inv_of_isUnitary, dagger_inv_eq_hom_of_isUnitary] using h
    evaluation_coevaluation' := by
      have h := congrArg dagger (ExactPairing.coevaluation_evaluation X Y)
      simpa only [Category.assoc, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight,
        dagger_hom_eq_inv_of_isUnitary, dagger_inv_eq_hom_of_isUnitary] using h }

/-- The reversed coevaluation is the dagger of the evaluation. -/
lemma exactPairingDagger_coevaluation (X Y : C) (p : ExactPairing X Y) :
    (exactPairingDagger X Y p).coevaluation' = p.evaluation'† := rfl

/-- The reversed evaluation is the dagger of the coevaluation. -/
lemma exactPairingDagger_evaluation (X Y : C) (p : ExactPairing X Y) :
    (exactPairingDagger X Y p).evaluation' = p.coevaluation'† := rfl

end ExactPairingDagger

namespace MonoidalDaggerCategory

/-- An object with a right dual has a left dual, namely its right dual, by Lemma 3.45. -/
@[instance_reducible]
def hasLeftDualOfHasRightDual (X : C) [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairingDagger X Xᘁ inferInstance

/-- An object with a left dual has a right dual, namely its left dual, by Lemma 3.45. -/
@[instance_reducible]
def hasRightDualOfHasLeftDual (X : C) [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairingDagger ᘁX X inferInstance

/-- A right rigid monoidal dagger category is left rigid, by Lemma 3.45. Not registered as an
instance, following the precedent of the braided case in Mathlib. -/
@[instance_reducible]
def leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCategory C where
  leftDual X := hasLeftDualOfHasRightDual X

/-- A left rigid monoidal dagger category is right rigid, by Lemma 3.45. Not registered as an
instance, following the precedent of the braided case in Mathlib. -/
@[instance_reducible]
def rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCategory C where
  rightDual X := hasRightDualOfHasLeftDual X

/-- In a monoidal dagger category, right rigidity and left rigidity are equivalent. -/
theorem nonempty_rightRigidCategory_iff_nonempty_leftRigidCategory :
    Nonempty (RightRigidCategory C) ↔ Nonempty (LeftRigidCategory C) :=
  ⟨fun ⟨_⟩ ↦ ⟨leftRigidCategoryOfRightRigidCategory⟩,
    fun ⟨_⟩ ↦ ⟨rightRigidCategoryOfLeftRigidCategory⟩⟩

end MonoidalDaggerCategory

/-- A braided monoidal dagger category has a unitary braiding on the monoidal structure
inherited from its monoidal dagger category, as in Definition 2.37. -/
class BraidedMonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    MonoidalDaggerCategory C, BraidedCategory C where
  /-- Every component of the braiding is unitary. -/
  isUnitary_braiding (X Y : C) : IsUnitary (β_ X Y).hom

attribute [instance] BraidedMonoidalDaggerCategory.isUnitary_braiding

/-- A symmetric monoidal dagger category has a unitary symmetric braiding, as in
Definition 2.37. -/
class SymmetricMonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    BraidedMonoidalDaggerCategory C, SymmetricCategory C

end CategoryTheory
