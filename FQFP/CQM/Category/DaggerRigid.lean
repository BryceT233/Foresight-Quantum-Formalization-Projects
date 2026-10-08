/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.Measurement
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The dagger reverses an exact pairing

Let `C` be a monoidal dagger category and let `ExactPairing X Y` be an exact pairing of `X` with
`Y`, with coevaluation `η : 𝟙_ C ⟶ X ⊗ Y` and evaluation `ε : Y ⊗ X ⟶ 𝟙_ C`. Then
`η† : 𝟙_ C ⟶ Y ⊗ X` and `ε† : X ⊗ Y ⟶ 𝟙_ C` form an exact pairing of `Y` with `X`: this is
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

## Main results

* `exactPairingDagger_coevaluation`, `exactPairingDagger_evaluation`: the reversed coevaluation
  and evaluation are definitionally the daggers of the evaluation and the coevaluation.
* `MonoidalDaggerCategory.hasLeftDualOfHasRightDual`,
  `MonoidalDaggerCategory.hasRightDualOfHasLeftDual`: an object with a right dual has a left
  dual (its right dual) and conversely.
* `MonoidalDaggerCategory.leftRigidCategoryOfRightRigidCategory`,
  `MonoidalDaggerCategory.rightRigidCategoryOfLeftRigidCategory`,
  `MonoidalDaggerCategory.nonempty_rightRigidCategory_iff_nonempty_leftRigidCategory`: a
  monoidal dagger category is right rigid iff it is left rigid.
* `dagger_whiskerLeft`, `dagger_whiskerRight`: the dagger commutes with whiskering.
* `dagger_inv_eq_hom_of_isUnitary`, `dagger_hom_eq_inv_of_isUnitary`: for a unitary
  isomorphism, the dagger of either direction is the other direction.

## Implementation notes

* The essential point is that **the dagger swaps the two triangle identities**: the reversed
  coevaluation/evaluation axiom is the dagger of `ExactPairing.evaluation_coevaluation`, and the
  reversed evaluation/coevaluation axiom is the dagger of `ExactPairing.coevaluation_evaluation`.
  Pairing them the other way round leaves goals that do not match, and no amount of coherence
  rewriting repairs it — this is the one substantive step of the proof.
* The dagger of a structure isomorphism — the associator, the unitors — is *not* given a lemma
  of its own. It is the unitary-isomorphism case of `dagger_hom_eq_inv_of_isUnitary` and
  `dagger_inv_eq_hom_of_isUnitary`, and `MonoidalDaggerCategory` registers the corresponding
  `IsUnitary` instances, so those two lemmas close every such goal by instance search. Naming
  them in the `simp only` sets below is enough, and six one-line restatements are avoided.
* `ExactPairing.coevaluation` and `ExactPairing.evaluation` are *functions* of the two objects,
  and `η_`/`ε_` are function notations. Consequently `(η_ X Y)†` does not parse as the dagger of
  the coevaluation: the dagger is applied to a partially applied function, producing a type
  error that points elsewhere. The proofs below therefore use the explicit forms
  `(ExactPairing.coevaluation X Y)†` and `(ExactPairing.evaluation X Y)†`.
* `Category.assoc` must appear in the `simp only` sets for the two triangle identities, to
  normalize the right-associated compositions that the dagger produces.
* `exactPairingDagger` is registered as an instance, so that instance search finds the reversed
  duality automatically; the object-level duals are instances too. Type class search for an
  `ExactPairing` or `HasLeftDual` goal with no solution still fails cleanly and quickly, because
  instance-search caching cuts the mutual recursion between `exactPairingDagger` and
  `hasLeftDualOfHasRightDual`. The rigid *category* level statements are `def`s rather than
  instances, following the precedent of
  `CategoryTheory.BraidedCategory.leftRigidCategoryOfRightRigidCategory` in Mathlib ("not
  registered as an instance as this is not canonical enough").

## Roadmap

The rest of §3.4.4 needs a braided (in fact symmetric) monoidal dagger category, and that
combination is not yet available in this project:

* `BraidedCategory` and `MonoidalDaggerCategory` both extend `MonoidalCategory`, so passing them
  as two *instance arguments* of one declaration gives two a priori different tensor products,
  and `β_` then elaborates against the wrong one. The braiding and the dagger must come from a
  single combined class.
* Attempting the natural combined class directly runs into the diamond on `MonoidalCategory`:
  `class SymmetricMonoidalDaggerCategory (C) [Category C] extends MonoidalDaggerCategory C,
  SymmetricCategory C` is rejected with `invalid binder annotation, type is not a class
  instance`, because `MonoidalDaggerCategory C` already carries its own `MonoidalCategory C`.
  The fix is to make the tensor product single-sourced — for example by having the combined
  class take the monoidal structure as a *parameter* rather than inheriting it twice, or by
  re-basing `MonoidalDaggerCategory` on `MonoidalCategoryStruct`. This is the prerequisite for
  `IsDaggerDual` (Definition 3.46 / equation (3.33)), which reads

  `(β_ X Y).hom ≫ ε ≫ η† = 𝟙 (𝟙_ C)`,

  where `β` is the braiding that closes the loop of the diagram. In a symmetric category the
  condition is invariant under exchanging `X` and `Y`, which is the notes' remark that a dagger
  dual is equivalently a maximally entangled state; the reversed duality witnessing that
  self-duality is `exactPairingDagger` above, whose structure maps are the daggers of the
  originals.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

open DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalDaggerCategory C]

section DaggerLemmas

/-- The dagger of a left whiskering is the left whiskering of the dagger. -/
lemma dagger_whiskerLeft {X Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : (X ◁ f)† = X ◁ f† := by
  have h : (X ◁ f : X ⊗ Y₁ ⟶ X ⊗ Y₂) = 𝟙 X ⊗ₘ f := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

/-- The dagger of a right whiskering is the right whiskering of the dagger. -/
lemma dagger_whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : (f ▷ Y)† = f† ▷ Y := by
  have h : (f ▷ Y : X₁ ⊗ Y ⟶ X₂ ⊗ Y) = f ⊗ₘ 𝟙 Y := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

/-- For a unitary isomorphism, the dagger of the inverse is the forward map. -/
lemma dagger_inv_eq_hom_of_isUnitary {X Y : C} (e : X ≅ Y) [IsUnitary e.hom] :
    e.inv† = e.hom := by
  rw [← involutive_dagger e.hom]
  congr 1
  calc e.inv = 𝟙 Y ≫ e.inv := (Category.id_comp _).symm
    _ = (e.hom† ≫ e.hom) ≫ e.inv := by rw [IsUnitary.dagger_comp_eq_id]
    _ = e.hom† ≫ e.hom ≫ e.inv := Category.assoc ..
    _ = e.hom† ≫ 𝟙 X := by rw [e.hom_inv_id]
    _ = e.hom† := Category.comp_id _

/-- For a unitary isomorphism, the dagger of the forward map is the inverse. -/
lemma dagger_hom_eq_inv_of_isUnitary {X Y : C} (e : X ≅ Y) [IsUnitary e.hom] :
    e.hom† = e.inv := by
  rw [← dagger_inv_eq_hom_of_isUnitary e, involutive_dagger]

end DaggerLemmas

section ExactPairingDagger

/-- **Lemma 3.45** (Reutter–Vicary, *Categorical Quantum Mechanics*). In a monoidal dagger
category the dagger of an exact pairing is an exact pairing with the roles of the two objects
exchanged: the reversed evaluation is the dagger of the coevaluation, and the reversed
coevaluation is the dagger of the evaluation. -/
instance exactPairingDagger (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := (ExactPairing.evaluation X Y)†
  evaluation' := (ExactPairing.coevaluation X Y)†
  coevaluation_evaluation' := by
    have h := congrArg dagger (ExactPairing.evaluation_coevaluation X Y)
    simpa only [Category.assoc, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight,
      dagger_hom_eq_inv_of_isUnitary, dagger_inv_eq_hom_of_isUnitary] using h
  evaluation_coevaluation' := by
    have h := congrArg dagger (ExactPairing.coevaluation_evaluation X Y)
    simpa only [Category.assoc, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight,
      dagger_hom_eq_inv_of_isUnitary, dagger_inv_eq_hom_of_isUnitary] using h

/-- The reversed coevaluation is the dagger of the evaluation. -/
lemma exactPairingDagger_coevaluation (X Y : C) [ExactPairing X Y] :
    ExactPairing.coevaluation Y X = (ExactPairing.evaluation X Y)† := rfl

/-- The reversed evaluation is the dagger of the coevaluation. -/
lemma exactPairingDagger_evaluation (X Y : C) [ExactPairing X Y] :
    ExactPairing.evaluation Y X = (ExactPairing.coevaluation X Y)† := rfl

end ExactPairingDagger

namespace MonoidalDaggerCategory

/-- An object with a right dual has a left dual, namely its right dual, by Lemma 3.45. -/
instance hasLeftDualOfHasRightDual (X : C) [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairingDagger X Xᘁ

/-- An object with a left dual has a right dual, namely its left dual, by Lemma 3.45. -/
instance hasRightDualOfHasLeftDual (X : C) [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairingDagger ᘁX X

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
  ⟨fun ⟨_⟩ => ⟨leftRigidCategoryOfRightRigidCategory⟩,
    fun ⟨_⟩ => ⟨rightRigidCategoryOfLeftRigidCategory⟩⟩

end MonoidalDaggerCategory

end CategoryTheory

/-
## Dagger duals (statement only — deliberately not compiled; nothing in this file is left
## unfinished, the sketch below lives entirely inside this comment)

A *dagger dual* is a dual whose coevaluation and evaluation are daggers of one another. Since
`coevaluation : 𝟙_ C ⟶ X ⊗ Y` and `evaluation : Y ⊗ X ⟶ 𝟙_ C` live in different hom sets,
relating them requires a braiding `β_ X Y : X ⊗ Y ≅ Y ⊗ X`, and the condition is that the
evaluation is the dagger of the coevaluation, transported across the braiding:

def IsDaggerDual {C : Type u} [Category.{v} C] [BraidedCategory C] [MonoidalDaggerCategory C]
    (X Y : C) [ExactPairing X Y] : Prop :=
  ExactPairing.evaluation X Y = (β_ Y X).hom ≫ (ExactPairing.coevaluation X Y)†

Equivalently `(ExactPairing.coevaluation X Y)† = (β_ X Y).hom ≫ ExactPairing.evaluation X Y`,
using the symmetry axiom `(β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)` of a symmetric monoidal
category. Given `exactPairingDagger X Y`, this condition is self-dual: `IsDaggerDual X Y` holds
for `ExactPairing X Y` if and only if `IsDaggerDual Y X` holds for `ExactPairing Y X`. A
monoidal dagger category in which every object has a dagger dual is *dagger compact closed*,
and in that setting the dagger is automatically compatible with the duality, so the reversal of
Lemma 3.45 is invisible: `η† = ε` up to the braiding.

This is recorded as a statement only. `MonoidalDaggerCategory` (this project) and
`BraidedCategory` (Mathlib) both extend `MonoidalCategory`, so writing both as instance
arguments above would give two a priori different tensor products for `C` — the condition only
makes sense for a single combined class, e.g. a `BraidedCategory C` whose monoidal structure is
definitionally that of `MonoidalDaggerCategory C`. Stating it here would require such a class,
or restating the dagger compatibility of `β_` directly; it is not needed for Lemma 3.45, which
holds in an arbitrary monoidal dagger category.
-/
