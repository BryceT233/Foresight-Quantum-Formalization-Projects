/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.Teleportation
public import FQFP.CategoryTheory.Category.RelCat.Measurement
public import FQFP.CategoryTheory.Category.RelCat.Rigid
public import Mathlib.Logic.Equiv.Bool
public import Mathlib.Tactic.FinCases

/-!
# Relational teleportation: one-time-pad correctness

`FQFP.CQM.Category.Teleportation` proves that each unitary branch of the teleportation protocol
recovers its input. This file instantiates that theorem in `RelCat`, where the pairing is the
self-dual diagonal pairing `exactPairingSelf` and corrections are unitaries, i.e. bijections.

The instance that matters is the two-element set `RelCat.bit`: the corrections are the identity
and the boolean negation, both branches are the identity relation (the input–output correctness of
the one-time pad), and the corresponding family of Bell effects is complete and disjoint
(`bitBellEffects_complete`, `bitBellEffects_disjoint`). The family is therefore a measurement in
the sense of Definition 2.51, so one of the two outcomes is guaranteed to occur; together with the
branch identities this is Example 3.18 — abstract teleportation in `RelCat` is encrypted
communication whose correction undoes the one-time pad.

Relation semantics expresses *possibility*, not probability: `RelCat` carries no distributions, so
no Shannon-theoretic statement of perfect secrecy is claimed here — only that the two effects form
a complete disjoint family, that both branches are possible for every input, and that each branch
is undone by its correction.

## Main definitions

* `RelCat.bit`: the two-element set as an object of `RelCat`.
* `RelCat.boolNot`: boolean negation, as a unitary endomorphism of `bit`.
* `RelCat.bellEffect`: the Bell effect `U† ▷ X ≫ ε` of a correction `U`.
* `RelCat.bitBellEffects`: the two Bell effects of the one-time-pad corrections.

## Main results

* `RelCat.correctedTeleportation_id`, `RelCat.correctedTeleportation_not`: the two one-time-pad
  branches recover the input.
* `RelCat.bitBellEffects_complete`, `RelCat.bitBellEffects_disjoint`: the two Bell effects form a
  complete, disjoint family.
* `RelCat.mem_bellEffect`: the Bell effect of `U` is the graph of `U`, read as
  `((a, b), ()) ∈ rel ↔ (b, a) ∈ U.rel`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DaggerCategory

namespace CategoryTheory.RelCat

/-- The two-element set, as an object of `RelCat`. -/
def bit : RelCat.{0} := Bool

variable {X : RelCat.{u}}

/-- The Bell effect of a correction `U`: the effect of the branch whose correction is `U`. -/
def bellEffect (U : X ⟶ X) : Effect (X ⊗ X) := (U† ▷ X) ≫ ε_ X X

set_option backward.isDefEq.respectTransparency.types false in
/-- The Bell effect of `U` relates `(a, b)` to the unit exactly when `(b, a)` is in the relation
`U`. -/
lemma mem_bellEffect (U : X ⟶ X) (a b : X) :
    ((a, b), (PUnit.unit : 𝟙_ RelCat.{u})) ∈ (bellEffect U).rel ↔ (b, a) ∈ U.rel := by
  rw [bellEffect, exactPairingSelf_evaluation, Hom.rel_comp_apply₂]
  constructor
  · rintro ⟨m, hm, h2⟩
    rw [mem_whiskerRight] at hm
    obtain ⟨h1, hb⟩ := hm
    rw [mem_selfEvaluation] at h2
    rw [rel_dagger, SetRel.mem_inv] at h1
    rwa [h2, ← hb] at h1
  · intro h
    refine ⟨(b, b), ?_, ?_⟩
    · rw [mem_whiskerRight]
      refine ⟨?_, rfl⟩
      rwa [rel_dagger, SetRel.mem_inv]
    · rw [mem_selfEvaluation]

/-- The effect set of the Bell effect of `U`: it consists of the pairs `(a, b)` with `(b, a)` in
the relation `U`. -/
lemma effectSet_bellEffect (U : X ⟶ X) (a b : X) :
    effectSet (bellEffect U) (a, b) ↔ (b, a) ∈ U.rel :=
  mem_bellEffect U a b

/-- The one-time-pad correction: boolean negation, as a unitary endomorphism of the two-element
set. -/
def boolNot : bit ⟶ bit :=
  (graphFunctor.mapIso (Equiv.boolNot).toIso).hom

/-- Boolean negation is unitary, so it is an admissible correction. -/
instance : IsUnitary boolNot :=
  isUnitary_graphFunctor_mapIso (Equiv.boolNot).toIso

/-- The relation underlying boolean negation is the graph of `not`. -/
lemma mem_boolNot_rel (a b : bit) : (a, b) ∈ boolNot.rel ↔ (!a) = b := by
  simp only [boolNot, Functor.mapIso_hom]
  exact Function.mem_graph_iff (fun x : Bool => (!x)) (a, b)

/-- The identity relation, read on a pair. -/
lemma mem_id_rel (a b : bit) : (a, b) ∈ ((𝟙 bit : bit ⟶ bit)).rel ↔ a = b :=
  SetRel.mem_id

/-- The two Bell effects of the one-time-pad corrections. -/
def bitBellEffects : Fin 2 → Effect (bit ⊗ bit) :=
  Fin.cases (bellEffect (𝟙 bit)) fun _ => bellEffect boolNot

@[simp]
lemma bitBellEffects_zero : bitBellEffects 0 = bellEffect (𝟙 bit) := rfl

@[simp]
lemma bitBellEffects_one : bitBellEffects 1 = bellEffect boolNot := rfl

/-- Every pair of bits lies in at least one of the two effect sets, so one of the two
one-time-pad outcomes always occurs. -/
theorem bitBellEffects_complete : Effect.Complete bitBellEffects := by
  rw [complete_iff_cover]
  rintro ⟨a, b⟩
  by_cases h : a = b
  · refine ⟨0, ?_⟩
    exact (effectSet_bellEffect (𝟙 bit) a b).2 (mem_id_rel b a |>.2 h.symm)
  · refine ⟨1, ?_⟩
    refine (effectSet_bellEffect boolNot a b).2 ?_
    rw [mem_boolNot_rel]
    cases a <;> cases b <;> simp_all

/-- The two one-time-pad Bell effects are normalized and pairwise orthogonal. -/
theorem bitBellEffects_disjoint : Effect.Disjoint bitBellEffects := by
  rw [disjoint_iff_nonempty_pairwise]
  constructor
  · intro i
    fin_cases i
    · refine ⟨(false, false), ?_⟩
      exact (effectSet_bellEffect (𝟙 bit) false false).2 (mem_id_rel false false |>.2 rfl)
    · refine ⟨(false, true), ?_⟩
      exact (effectSet_bellEffect boolNot false true).2 (mem_boolNot_rel true false |>.2 rfl)
  · intro i j hij z hz
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · obtain ⟨a, b⟩ := z
      obtain ⟨h0, h1⟩ := hz
      have h0' : b = a := mem_id_rel b a |>.1 ((effectSet_bellEffect (𝟙 bit) a b).1 h0)
      have h1' : (!b) = a := mem_boolNot_rel b a |>.1 ((effectSet_bellEffect boolNot a b).1 h1)
      cases a <;> cases b <;> simp_all
    · obtain ⟨a, b⟩ := z
      obtain ⟨h1, h0⟩ := hz
      have h0' : b = a := mem_id_rel b a |>.1 ((effectSet_bellEffect (𝟙 bit) a b).1 h0)
      have h1' : (!b) = a := mem_boolNot_rel b a |>.1 ((effectSet_bellEffect boolNot a b).1 h1)
      cases a <;> cases b <;> simp_all
    · exact hij rfl

/-- The first one-time-pad branch (no correction) recovers the input. -/
theorem correctedTeleportation_id :
    correctedTeleportation bit bit (𝟙 bit) = 𝟙 bit :=
  correctedTeleportation_eq_id ..

/-- The second one-time-pad branch (negation correction) recovers the input. -/
theorem correctedTeleportation_not :
    correctedTeleportation bit bit boolNot = 𝟙 bit :=
  correctedTeleportation_eq_id ..

end CategoryTheory.RelCat
