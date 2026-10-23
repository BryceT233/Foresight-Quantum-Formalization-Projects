/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerRigid
public import FQFP.CQM.Category.Measurement

/-!
# Teleportation

This file isolates the single-branch identity underlying quantum teleportation (Example 3.17 of
Reutter–Vicary, *Categorical Quantum Mechanics*). Given an exact pairing `p : ExactPairing R L`
(i.e. `L ⊣ R` in the book's notation), a resource state `η` on `R ⊗ L` and an effect `x`
on `L ⊗ R`, the **branch** of the protocol is

`L --ρ⁻¹--> L ⊗ 𝟙 --L◁η--> L ⊗ (R ⊗ L) --α⁻¹--> (L ⊗ R) ⊗ L --x▷L--> 𝟙 ⊗ L --λ--> L --U--> L`,

which is the protocol restricted to the outcome whose effect is `x`, with `U` the correction
applied to the teleported system. The main theorem is that the branch whose effect is the Bell
effect `U† ▷ R ≫ ε` and whose correction is `U` is the identity: every branch of the protocol,
parameterised by the correction `U`, recovers the input state.

The proof does not unfold the snake equations: it uses Mathlib's `tensorRightHomEquiv`, the
transposition bijection `(L ⊗ R ⟶ 𝟙) ≃ (L ⟶ 𝟙 ⊗ L)` attached to the exact pairing, together with
the sliding identity `tensorRightHomEquiv (V ▷ R ≫ ε) = V ≫ (λ_ L).inv`, proved here for an
explicit pairing as
`tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing`. This is the "effect written on the `L`
side" form of the protocol; translating it to the transpose form of the printed figure is not done
here.

## Single branches are not yet a measurement

The theorems here are per branch: they say what a given outcome does *if it occurs*.
Completeness and disjointness of the branch effects are separate requirements. They are proved
for `RelCat.bitBellEffects`; the corresponding qubit Bell measurement remains to be formalized.

## Normalization boundary

Nothing here normalizes: the resource state `η` and the effect `x` are arbitrary arguments of
`teleportationBranch`, so the unnormalized Bell data of the source — the cup `∑ᵢ |ii⟩` and the
four Bell effects, each of norm `√2` for a qubit — gives an exact identity. The physically
normalized data instead gives the scalar multiple `(1/2) • 𝟙` that `QuditCat.Teleportation`
computes; one cannot normalize the cup and keep the exact-pairing snake equations at the same
time, which is why the two statements are kept apart.

## Main definitions

* `CategoryTheory.teleportationBranch`: one branch of the protocol, for a resource state, an
  effect and a correction. The data are explicit, so this also covers scaled (normalized)
  resource states and effects.
* `CategoryTheory.correctedTeleportation`: the branch of the protocol for a chosen
  `[ExactPairing R L]`, whose effect is `U† ▷ R ≫ ε` and whose correction is `U`.

## Main results

* `CategoryTheory.teleportationBranch_evaluation`: the branch with effect `V ▷ R ≫ ε` and no
  correction is `V`.
* `CategoryTheory.correctedTeleportation_eq_id`: for unitary `U`, the branch with effect
  `U† ▷ R ≫ ε` and correction `U` is the identity.

-/

@[expose] public section

open CategoryTheory MonoidalCategory
open CategoryTheory.DaggerCategory

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The branch of the teleportation protocol with resource state `η : 𝟙_ C ⟶ R ⊗ L`, branch
effect `x : L ⊗ R ⟶ 𝟙_ C` and correction `U : L ⟶ L`.

Reading the composite in order: the input `L` is paired with the unit and the resource state on
`R ⊗ L` is inserted; the associator brings the input next to `R`, the effect `x` contracts that
pair, and the correction `U` is applied to the remaining `L`. -/
def teleportationBranch {L R : C} (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C) (U : L ⟶ L) : L ⟶ L :=
  (ρ_ L).inv ≫ (L ◁ η) ≫ (α_ L R L).inv ≫ (x ▷ L) ≫ (λ_ L).hom ≫ U

/-- Appending a morphism after a branch is the same as extending the correction. -/
lemma teleportationBranch_comp {L R : C} (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C)
    (U V : L ⟶ L) : teleportationBranch η x U ≫ V = teleportationBranch η x (U ≫ V) := by
  simp only [teleportationBranch, Category.assoc]

section Pairing

variable {L R : C} [ExactPairing R L]

/-- Sliding an effect along the pairing: the transposed branch effect `V ▷ R ≫ ε` is the
transpose of `V`. This is the explicit-pairing form of Mathlib's
`tensorRightHomEquiv_whiskerRight_comp_evaluation`. -/
theorem tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing (V : L ⟶ L) :
    (tensorRightHomEquiv L R L (𝟙_ C)) ((V ▷ R) ≫ ε_ R L) = V ≫ (λ_ L).inv := by
  calc
    _ = 𝟙 _ ⊗≫ (L ◁ η_ R L ≫ V ▷ (R ⊗ L)) ⊗≫ ε_ R L ▷ L := by
      dsimp [tensorRightHomEquiv]
      monoidal
    _ = V ⊗≫ (L ◁ η_ R L ⊗≫ ε_ R L ▷ L) := by
      rw [whisker_exchange]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'']
      monoidal

/-- The branch whose effect is `V ▷ R ≫ ε` and whose correction is trivial is `V`: the effect
already carries the whole map, because `ε` together with the resource state transposes `V` back
across the pairing. -/
theorem teleportationBranch_evaluation (V : L ⟶ L) :
    teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) (𝟙 L) = V := by
  have h := tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing (L := L) (R := R) V
  have key : teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) (𝟙 L)
      = (tensorRightHomEquiv L R L (𝟙_ C)) ((V ▷ R) ≫ ε_ R L) ≫ (λ_ L).hom := by
    simp only [teleportationBranch, Category.comp_id, tensorRightHomEquiv, Equiv.coe_fn_mk,
      Category.assoc]
  rw [key, h]
  simp

/-- **Example 3.17**, single branch: for a unitary correction `U`, the branch with Bell effect
`U† ▷ R ≫ ε` and correction `U` is the identity. -/
theorem teleportationBranch_correction [DaggerCategory C] (U : L ⟶ L) [IsUnitary U] :
    teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) U = 𝟙 L := by
  calc teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) U
      = teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) (𝟙 L ≫ U) := by
        rw [Category.id_comp]
    _ = teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) (𝟙 L) ≫ U := by
        rw [teleportationBranch_comp]
    _ = U† ≫ U := by rw [teleportationBranch_evaluation]
    _ = 𝟙 L := IsUnitary.dagger_comp_eq_id U

end Pairing

/-- The branch of the protocol for the chosen exact pairing, whose effect is the Bell effect
`U† ▷ R ≫ ε` and whose correction is `U`. -/
def correctedTeleportation (L R : C) [DaggerCategory C] [ExactPairing R L] (U : L ⟶ L) :
    L ⟶ L :=
  teleportationBranch ExactPairing.coevaluation' ((U† ▷ R) ≫ ExactPairing.evaluation') U

/-- **Example 3.17**, single branch, for an arbitrary exact pairing between `R` and `L`: for a
unitary correction `U`, the branch with Bell effect `U† ▷ R ≫ ε` recovers the input state. -/
theorem correctedTeleportation_eq_id {L R : C} [ExactPairing R L] [DaggerCategory C]
    (U : L ⟶ L) [IsUnitary U] : correctedTeleportation L R U = 𝟙 L :=
  teleportationBranch_correction ..

end CategoryTheory
