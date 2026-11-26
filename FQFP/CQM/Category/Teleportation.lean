/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import FQFP.CategoryTheory.Monoidal.Rigid.Basic
public import FQFP.CategoryTheory.Monoidal.Scalar

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
the sliding identity `tensorRightHomEquiv (V ▷ R ≫ ε) = V ≫ (λ_ L).inv`, provided by
`FQFP.CategoryTheory.Monoidal.Rigid.Basic` for an explicit pairing as
`tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing`. This is the "effect written on the `L`
side" form of the protocol; translating it to the transpose form of the printed figure is not done
here.

## Single branches are not yet a measurement

The theorems here are per branch: they say what a given outcome does *if it occurs*.
Completeness and disjointness of the branch effects are separate requirements, proved in the
models for `RelCat.bitBellEffects` and the normalized `Qudit.qubitBellEffects`.

## Scalar normalization

In a braided category, scaling the resource by `s` and the effect by `t` scales the branch by
`s * t`. For the normalized Bell data of a qubit both factors are `1/√2`, giving amplitude
`1/2` and probability `1/4` for each corrected branch.

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

/-- Attach a bipartite resource to an input and group the input with the resource's
first factor for measurement. The second factor is the receiver's system. -/
def attachTeleportationResource (A : C) {R B : C} (η : 𝟙_ C ⟶ R ⊗ B) :
    A ⟶ (A ⊗ R) ⊗ B :=
  (ρ_ A).inv ≫ (𝟙 A ⊗ₘ η) ≫ (α_ A R B).inv

/-- A normalized resource, expressed as an isometry from the tensor unit, gives an
isometric preparation on every input. -/
instance {D : Type*} [Category D] [MonoidalDaggerCategory D] (A : D) {R B : D}
    (η : 𝟙_ D ⟶ R ⊗ B) [IsIsometry η] : IsIsometry (attachTeleportationResource A η) := by
  unfold attachTeleportationResource
  infer_instance

/-- The branch of the teleportation protocol with resource state `η : 𝟙_ C ⟶ R ⊗ L`, branch
effect `x : L ⊗ R ⟶ 𝟙_ C` and correction `U : L ⟶ L`.

Reading the composite in order: the input `L` is paired with the unit and the resource state on
`R ⊗ L` is inserted; the associator brings the input next to `R`, the effect `x` contracts that
pair, and the correction `U` is applied to the remaining `L`. -/
def teleportationBranch {L R : C} (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C) (U : L ⟶ L) : L ⟶ L :=
  attachTeleportationResource L η ≫ (x ▷ L) ≫ (λ_ L).hom ≫ U

/-- Appending a morphism after a branch is the same as extending the correction. -/
lemma teleportationBranch_comp {L R : C} (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C)
    (U V : L ⟶ L) : teleportationBranch η x U ≫ V = teleportationBranch η x (U ≫ V) := by
  simp only [teleportationBranch, Category.assoc]

/-- Independent scalar factors on the resource and on the effect multiply in a branch. -/
lemma teleportationBranch_smul_smul [BraidedCategory C] {L R : C} (s t : Scalar C)
    (η : 𝟙_ C ⟶ R ⊗ L) (x : L ⊗ R ⟶ 𝟙_ C) (U : L ⟶ L) :
    teleportationBranch (s • η) (t • x) U = (s * t) • teleportationBranch η x U := by
  simp only [teleportationBranch, attachTeleportationResource, id_tensorHom,
    whiskerLeft_scalar_smul, scalar_smul_whiskerRight, scalar_smul_comp, comp_scalar_smul,
    ← mul_smul, mul_comm t s]

section Pairing

variable {L R : C} [ExactPairing R L]

/-- The branch whose effect is `V ▷ R ≫ ε` and whose correction is trivial is `V`: the effect
already carries the whole map, because `ε` together with the resource state transposes `V` back
across the pairing. -/
theorem teleportationBranch_evaluation (V : L ⟶ L) :
    teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) (𝟙 L) = V := by
  have h := tensorRightHomEquiv_whiskerRight_comp_evaluation_pairing (L := L) (R := R) V
  have key : teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) (𝟙 L)
      = (tensorRightHomEquiv L R L (𝟙_ C)) ((V ▷ R) ≫ ε_ R L) ≫ (λ_ L).hom := by
    simp only [teleportationBranch, attachTeleportationResource, id_tensorHom, Category.comp_id,
      tensorRightHomEquiv, Equiv.coe_fn_mk, Category.assoc]
  rw [key, h]
  simp

/-- A branch with the effect induced by `V` followed by any correction `U` realizes `V ≫ U`. -/
lemma teleportationBranch_evaluation_comp (V U : L ⟶ L) :
    teleportationBranch (η_ R L) ((V ▷ R) ≫ ε_ R L) U = V ≫ U := by
  simpa only [teleportationBranch_comp, Category.id_comp] using
    congrArg (· ≫ U) (teleportationBranch_evaluation (R := R) V)

/-- **Example 3.17**, single branch: for a unitary correction `U`, the branch with Bell effect
`U† ▷ R ≫ ε` and correction `U` is the identity. -/
theorem teleportationBranch_correction [DaggerCategory C] (U : L ⟶ L) [IsUnitary U] :
    teleportationBranch (η_ R L) ((U† ▷ R) ≫ ε_ R L) U = 𝟙 L := by
  rw [teleportationBranch_evaluation_comp, IsUnitary.dagger_comp_eq_id]

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
