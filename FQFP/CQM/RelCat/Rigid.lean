/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.RelCat.Morphism
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Self-duality of the category of relations

Every object of `RelCat` is its own dual. The coevaluation is the diagonal relation
`{(p, (x, x))}` and the evaluation is the codiagonal relation `{((x, x), p)}`, its converse.
The two snake equations are checked directly on underlying relations.

The resulting exact pairing is invariant under the dagger: reversing the pairing as in Lemma 3.45
returns the same coevaluation and evaluation, because the codiagonal relation is the converse of
the diagonal relation. This is the relational instance of the general dagger statement of
`CategoryTheory.exactPairingDagger`.

Consequently the graphical transpose of a relation, taken with respect to this pairing, is its
converse (`rightAdjointMate_eq_dagger`).

## Main definitions

* `RelCat.selfCoevaluation`, `RelCat.selfEvaluation`: the diagonal and codiagonal relations.
* `RelCat.exactPairingSelf`: every object of `RelCat` is self-dual.
* `RelCat.instHasRightDual`, `RelCat.instHasLeftDual`: the dual of an object is itself.

## Main results

* `RelCat.dagger_selfEvaluation`: the codiagonal relation is the dagger of the diagonal relation.
* `RelCat.exactPairingDagger_self`: the reversed self-pairing has the same coevaluation and
  evaluation, so the self-duality is compatible with the dagger.
* `RelCat.rightAdjointMate_eq_dagger`: the transpose of a relation is its converse.

## Implementation notes

The tensor product is the cartesian product of types, so identifying a tensor object with a
product type is definitional but not syntactically visible; in particular the projections out of a
tensor-typed element need that unfolding. The dagger and snake computations therefore run under
`backward.isDefEq.respectTransparency.types false`, as in the monoidal and braided instances.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DaggerCategory

namespace CategoryTheory.RelCat

/-! ### The diagonal and codiagonal relations -/

/-- The diagonal relation, as a coevaluation `𝟙_ ⟶ X ⊗ X`. -/
def selfCoevaluation (X : RelCat.{u}) : 𝟙_ RelCat.{u} ⟶ X ⊗ X :=
  .ofRel {p | p.2.1 = p.2.2}

/-- The codiagonal relation, as an evaluation `X ⊗ X ⟶ 𝟙_`. -/
def selfEvaluation (X : RelCat.{u}) : X ⊗ X ⟶ 𝟙_ RelCat.{u} :=
  .ofRel {p | p.1.1 = p.1.2}

@[simp] lemma mem_selfCoevaluation (X : RelCat.{u}) (p : 𝟙_ RelCat.{u})
    (v : (X ⊗ X : RelCat.{u})) : (p, v) ∈ (selfCoevaluation X).rel ↔ v.1 = v.2 := Iff.rfl

@[simp] lemma mem_selfEvaluation (X : RelCat.{u}) (v : (X ⊗ X : RelCat.{u}))
    (p : 𝟙_ RelCat.{u}) : (v, p) ∈ (selfEvaluation X).rel ↔ v.1 = v.2 := Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The codiagonal relation is the dagger of the diagonal relation: daggering a relation forgets
the unit component of its source. -/
lemma dagger_selfEvaluation (X : RelCat.{u}) : (selfEvaluation X)† = selfCoevaluation X := by
  apply Hom.ext
  ext ⟨p, v⟩
  simp only [rel_dagger, SetRel.mem_inv, mem_selfCoevaluation, mem_selfEvaluation]

/-- The diagonal relation is the dagger of the codiagonal relation. -/
lemma dagger_selfCoevaluation (X : RelCat.{u}) : (selfCoevaluation X)† = selfEvaluation X := by
  rw [← dagger_selfEvaluation, involutive_dagger]

/-! ### Every object is self-dual -/

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object of `RelCat` is self-dual: the diagonal relation is a coevaluation with the
codiagonal relation as evaluation. Both snake equations are checked on underlying relations.

This is *a* witness of `ExactPairing X X`, not the only one: for a composite object,
`ExactPairing.tensor` (applied to two copies of this pairing) and, on the tensor unit,
`exactPairingUnit` are further legitimate witnesses of the same type, with different cups. See
`exactPairingSelf_coevaluation` for the witness that instance search selects. -/
instance exactPairingSelf (X : RelCat.{u}) : ExactPairing X X where
  coevaluation' := selfCoevaluation X
  evaluation' := selfEvaluation X
  coevaluation_evaluation' := by
    apply Hom.ext
    ext ⟨a, b⟩
    simp only [Hom.rel_comp_apply₂, mem_whiskerLeft, mem_whiskerRight, mem_associator_inv,
      mem_selfCoevaluation, mem_selfEvaluation, mem_leftUnitor_inv, mem_rightUnitor_hom,
      Prod.ext_iff]
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, w5, rest⟩
      obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6, h7⟩ := rest
      exact ⟨a.1, rfl, by rw [h1, h3, h6, ← h4, h2, h5, h7]⟩
    · rintro ⟨r, h1, h2⟩
      exact ⟨(r, (r, r)), ⟨h1, rfl⟩, ((r, r), b.2), ⟨⟨rfl, rfl⟩, h2⟩, rfl, rfl⟩
  evaluation_coevaluation' := by
    apply Hom.ext
    ext ⟨a, b⟩
    simp only [Hom.rel_comp_apply₂, mem_whiskerLeft, mem_whiskerRight, mem_associator_hom,
      mem_selfCoevaluation, mem_selfEvaluation, mem_leftUnitor_hom, mem_rightUnitor_inv,
      Prod.ext_iff]
    constructor
    · rintro ⟨w, ⟨h1, h2⟩, w5, rest⟩
      obtain ⟨⟨c1, c2, c3⟩, c4, c5⟩ := rest
      exact ⟨a.2, rfl, by rw [h2, c3, ← c5, ← c2, ← h1, c1, c4]⟩
    · rintro ⟨r, h1, h2⟩
      exact ⟨((r, r), r), ⟨rfl, h1⟩, (r, (r, b.1)), ⟨rfl, rfl, h2⟩, h2, h2⟩

/-- The self-duality is compatible with the dagger: reversing the exact pairing of Lemma 3.45
returns the same coevaluation and evaluation, because the codiagonal relation is the converse of
the diagonal relation. -/
theorem exactPairingDagger_self (X : RelCat.{u}) :
    (exactPairingDagger X X (exactPairingSelf X)).coevaluation' = selfCoevaluation X ∧
      (exactPairingDagger X X (exactPairingSelf X)).evaluation' = selfEvaluation X := by
  refine ⟨?_, ?_⟩
  · rw [exactPairingDagger_coevaluation]
    exact dagger_selfEvaluation X
  · rw [exactPairingDagger_evaluation]
    exact dagger_selfCoevaluation X

/-! ### The witness selected by instance search

`ExactPairing X X` has several legitimate witnesses, so the following two lemmas record *which*
one instance search selects. They are the interface through which a downstream computation can
pin the cup and cap it works with. -/

/-- Instance search selects `exactPairingSelf` as the self-pairing witness: the cup `η_ X X` is
the diagonal relation. Compare `ExactPairing.tensor`, whose cup on a composite object swaps the
two factors. -/
lemma exactPairingSelf_coevaluation (X : RelCat.{u}) : η_ X X = selfCoevaluation X := rfl

/-- Instance search selects `exactPairingSelf` as the self-pairing witness: the cap `ε_ X X` is
the codiagonal relation. -/
lemma exactPairingSelf_evaluation (X : RelCat.{u}) : ε_ X X = selfEvaluation X := rfl

/-! ### Duals -/

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object of `RelCat` has itself as right dual, so the self-dual pairing is available by
instance search. -/
instance instHasRightDual (X : RelCat.{u}) : HasRightDual X where
  rightDual := X
  exact := exactPairingSelf X

set_option backward.isDefEq.respectTransparency.types false in
/-- Every object of `RelCat` has itself as left dual. -/
instance instHasLeftDual (X : RelCat.{u}) : HasLeftDual X where
  leftDual := X
  exact := exactPairingSelf X

/-! ### The transpose is the converse -/

set_option backward.isDefEq.respectTransparency.types false in
/-- **Definition 3.9** for relations: the transpose of a relation with respect to the self-dual
pairing is its converse. This is what makes the correction operators of teleportation available
in `RelCat`, since a correction is a relation and its transpose is again that relation's
converse. -/
theorem rightAdjointMate_eq_dagger {X Y : RelCat.{u}} (f : X ⟶ Y) : fᘁ = f† := by
  rw [rightAdjointMate]
  change (ρ_ Y).inv ≫ (Y ◁ selfCoevaluation X) ≫ (Y ◁ f ▷ X) ≫ (α_ Y Y X).inv
    ≫ (selfEvaluation Y ▷ X) ≫ (λ_ X).hom = f†
  apply Hom.ext
  ext ⟨y, x⟩
  simp only [Hom.rel_comp_apply₂, mem_whiskerLeft, mem_whiskerRight, mem_associator_inv,
    mem_selfCoevaluation, mem_selfEvaluation, mem_leftUnitor_hom, mem_rightUnitor_inv,
    rel_dagger, SetRel.mem_inv, Prod.ext_iff]
  constructor
  · rintro ⟨y1, a1, w, ⟨a2, a3⟩, w2, ⟨a4, a5, a6⟩, w3, ⟨⟨a7, a8⟩, a9⟩, w4, ⟨a10, a11⟩, a12⟩
    rw [show x = w.2.1 from by rw [← a12, ← a11, ← a9, ← a6, ← a3],
      show y = w2.2.1 from by rw [a1, a2, a4, a7, a10, ← a8]]
    exact a5
  · rintro a5
    exact ⟨(y, PUnit.unit), rfl, (y, (x, x)), ⟨rfl, rfl⟩, (y, (y, x)), ⟨rfl, a5, rfl⟩,
      ((y, y), x), ⟨⟨rfl, rfl⟩, rfl⟩, (PUnit.unit, x), ⟨rfl, rfl⟩, rfl⟩

end CategoryTheory.RelCat
