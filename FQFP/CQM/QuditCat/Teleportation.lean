/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.Teleportation
public import FQFP.CQM.QuditCat.Measurement
public import FQFP.CQM.QuditCat.Rigid

/-!
# Teleportation in the qubit model

`FQFP.CQM.Category.Teleportation` proves the single-branch identity of teleportation for the
unnormalized Bell data of the source. This file instantiates it on the qubit `QuditCat.std 2` with
the four corrections of Example 3.17 — `I`, `Z`, `X` and `J = [[0, 1], [-1, 0]]` — and the exact
pairing `exactPairingOfOrthonormalBasis (ZBasis 2)`: for each correction the branch is the
identity.

The normalization boundary of Example 3.17 is then made explicit. The source's cup `|00⟩ + |11⟩`
and its four Bell effects each have norm `√2`, so with the *unnormalized* data each branch is
exactly the identity. Physically the resource state and the effects each carry a factor
`1/√2`; with those factors the branch map is `(1/2) • 𝟙`:

* `QuditCat.normalizedBranch_apply`: the normalized branch sends a vector `x` to `(1/2) • x`,
  so it is `(1/2) • 𝟙` as a linear map (`normalizedBranch_eq_smul`);
* `QuditCat.branch_probability`: for a unit input the branch state has squared norm `1/4`, the
  probability of that branch.

The last two statements are the *two* normalized factors together; one cannot normalize the cup
alone and still have the exact-pairing snake equation of the source.

## Bell measurement

The four normalized effects `qubitBellEffects` are the bras of the normalized Bell basis
`bellBasis` of Definition 0.58, in the order of the corrections `I, Z, X, J`. Their completeness
and disjointness follow from the existing orthonormal-basis measurement API, as does the Born
rule for any unit two-qubit input. Thus these effects form a measurement in the sense of
Definitions 2.50–2.51. The single-branch probability `1/4` above concerns the teleportation
protocol with its Bell resource; a general two-qubit input has probabilities given by its Bell
basis amplitudes.

## Main definitions

* `QuditCat.bellState`, `QuditCat.bellEffect`: the normalized Bell resource state and the
  scaled Bell effect, normalized when the correction is unitary.
* `QuditCat.corrections`: the four corrections of Example 3.17, in the order of its effect table.
* `QuditCat.jGate`: the gate `J = [[0, 1], [-1, 0]]` of Example 3.17.
* `QuditCat.bellBasis`, `QuditCat.qubitBellEffects`: the normalized Bell basis and measurement.

## Main results

* `CategoryTheory.correctedTeleportation_eq_id` for each of the four corrections
  (`correctedTeleportation_corrections`).
* `QuditCat.isUnitary_corrections`: each correction is unitary, including for a variable index.
* `QuditCat.normalizedBranch_eq_smul`: the normalized branch is `(1/2) • 𝟙`.
* `QuditCat.branch_probability`: its branch probability is `1/4`.
* `QuditCat.qubitBellEffects_complete`, `QuditCat.qubitBellEffects_disjoint`: measurement axioms.
* `QuditCat.sum_probability_qubitBellEffects`: the Bell measurement Born rule.
* `QuditCat.scalarRingEquiv_probability_qubitBellEffects`: squared Bell amplitudes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DaggerCategory QuditCat
open scoped TensorProduct BigOperators

namespace QuditCat

noncomputable section

/-- The normalization factor `1/√2` of the Bell state and of the Bell effects. -/
def bellFactor : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma bellFactor_mul_self : bellFactor * bellFactor = (1 / 2 : ℂ) := by
  rw [bellFactor, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The Bell normalization factor is real. -/
@[simp]
lemma conj_bellFactor : starRingEnd ℂ bellFactor = bellFactor := by
  simp [bellFactor]

/-- The normalized Bell resource state `(1/√2) (|00⟩ + |11⟩)`. -/
def bellState : 𝟙_ QuditCat ⟶ Qubit ⊗ Qubit :=
  ofHom (LinearMap.toSpanSingleton ℂ (Qubit.state ⊗[ℂ] Qubit.state)
    (bellFactor • ∑ i, ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 i))

/-- The scaled Bell effect associated with `U`; it is normalized when `U` is unitary. -/
def bellEffect (U : Qubit ⟶ Qubit) : Qubit ⊗ Qubit ⟶ 𝟙_ QuditCat :=
  ofHom (bellFactor • ((U† ▷ Qubit) ≫ basisEvaluation (ZBasis 2)).hom)

/-- The matrix `[[0, 1], [-1, 0]]` of Example 3.17, as an endomorphism of `Qubit`. -/
def jGate : End Qubit := matrixToEnd !![0, 1; -1, 0]

/-- The gate `J` of Example 3.17 is unitary. -/
instance isUnitary_jGate : IsUnitary jGate.asHom := by
  rw [jGate, isUnitary_matrixToEnd_iff_fin_two]
  simp

/-- The four corrections of Example 3.17, in the order in which that example lists their effects:
`I`, `Z`, `X` and `J`. (The printed Definition 0.74 lists `I`, `X`, `Z`, `J`; the effect table of
Example 3.17 pairs `Z` with the effect `(1 0 0 -1)` and `X` with `(0 1 1 0)`, which is the order
used here. Note that `J = i • pauliY`, so the fourth correction is the Pauli `Y` gate up to the
phase `i`, and the two families differ only by that phase.) -/
def corrections : Fin 4 → (Qubit ⟶ Qubit) :=
  ![𝟙 Qubit, Qubit.pauliZ.asHom, Qubit.pauliX.asHom, jGate.asHom]

/-- Every correction in the qubit teleportation family is unitary. -/
instance isUnitary_corrections (i : Fin 4) : IsUnitary (corrections i) := by
  fin_cases i <;> dsimp [corrections] <;> infer_instance

@[simp]
lemma bellState_apply (c : ℂ) :
    bellState c = c • (bellFactor • ∑ i, ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 i) := rfl

lemma bellEffect_apply (U : Qubit ⟶ Qubit) (a b : Qubit.state) :
    (bellEffect U) (a ⊗ₜ[ℂ] b) = bellFactor * basisForm (ZBasis 2) (U† a) b := by
  have hcomp : ((U† ▷ Qubit) ≫ basisEvaluation (ZBasis 2)) (a ⊗ₜ[ℂ] b)
      = basisForm (ZBasis 2) (U† a) b := by
    rw [comp_apply, whiskerRight_apply, basisEvaluation_apply]
  rw [bellEffect, ofHom_apply, LinearMap.smul_apply, hcomp, smul_eq_mul]

/-! ### The normalized Bell measurement -/

/-- The four normalized Bell vectors of Definition 0.58, in the order `Φ⁺, Φ⁻, Ψ⁺, Ψ⁻`. -/
def bellVector : Fin 4 → Qubit.state ⊗[ℂ] Qubit.state :=
  ![bellFactor • (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 0 + ZBasis 2 1 ⊗ₜ[ℂ] ZBasis 2 1),
    bellFactor • (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 0 - ZBasis 2 1 ⊗ₜ[ℂ] ZBasis 2 1),
    bellFactor • (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 1 + ZBasis 2 1 ⊗ₜ[ℂ] ZBasis 2 0),
    bellFactor • (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 1 - ZBasis 2 1 ⊗ₜ[ℂ] ZBasis 2 0)]

/-- The four Bell vectors are orthonormal for the Hilbert tensor-product inner product. -/
lemma orthonormal_bellVector : Orthonormal ℂ bellVector := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [bellVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Fin.reduceFinMk]
  all_goals
    simp only [inner_smul_left (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_smul_right (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_add_left (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_add_right (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_sub_left (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_sub_right (E := Qubit.state ⊗[ℂ] Qubit.state),
      TensorProduct.inner_tmul, conj_bellFactor]
    norm_num [OrthonormalBasis.inner_eq_ite, ← mul_assoc, bellFactor_mul_self]

/-- The normalized Bell orthonormal basis of a pair of qubits, as in Definition 0.58. -/
def bellBasis : OrthonormalBasis (Fin 4) ℂ (Qubit ⊗ Qubit).state :=
  OrthonormalBasis.mk orthonormal_bellVector
    (orthonormal_bellVector.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa using
        (Module.finrank_eq_card_basis
          ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis).symm)).ge

/-- The Bell basis has the four explicitly given normalized Bell vectors. -/
lemma bellBasis_apply (i : Fin 4) : bellBasis i = bellVector i := by
  simp [bellBasis]

/-- The normalized teleportation resource is the first Bell basis state. -/
lemma bellState_eq_ketArrow : bellState = ketArrow (bellBasis 0) := by
  apply hom_ext
  apply LinearMap.ext
  change ∀ c : ℂ, bellState c = c • bellBasis 0
  intro c
  rw [bellState_apply, bellBasis_apply]
  simp [bellVector, Fin.sum_univ_two]

/-- The Bell resource is a normalized categorical state. -/
instance isIsometry_bellState : IsIsometry bellState := by
  rw [bellState_eq_ketArrow]
  exact (isIsometry_ketArrow_iff _).2 (bellBasis.orthonormal.norm_eq_one 0)

/-- The four normalized Bell effects of the teleportation corrections. -/
def qubitBellEffects : Fin 4 → Effect (Qubit ⊗ Qubit) :=
  fun i ↦ bellEffect (corrections i)

/-- The teleportation effects are exactly the bras of the normalized Bell basis. -/
@[simp]
theorem qubitBellEffects_eq_braArrow : qubitBellEffects = fun i ↦ braArrow (bellBasis i) := by
  funext i
  apply hom_ext
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨a, b⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  change (bellEffect (corrections i)) (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b) =
    inner ℂ (bellBasis i) (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b)
  rw [bellEffect_apply, bellBasis_apply]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [corrections, Qubit.pauliX, Qubit.pauliZ, jGate, dagger_matrixToEnd (n := 2),
      matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two, basisForm_apply,
      bra_apply, bellVector,
      inner_smul_left (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_add_left (E := Qubit.state ⊗[ℂ] Qubit.state),
      inner_sub_left (E := Qubit.state ⊗[ℂ] Qubit.state), TensorProduct.inner_tmul]

/-- The Bell effects detect every nonzero process, as required in Section 3.2.1. -/
theorem qubitBellEffects_complete : Effect.Complete qubitBellEffects := by
  rw [qubitBellEffects_eq_braArrow]
  exact complete_braArrow_orthonormalBasis bellBasis

/-- The Bell effects are normalized and pairwise orthogonal, as in Definition 2.51. -/
theorem qubitBellEffects_disjoint : Effect.Disjoint qubitBellEffects := by
  simpa only [qubitBellEffects_eq_braArrow] using disjoint_braArrow_orthonormalBasis bellBasis

/-- The Bell measurement resolves the identity on the two-qubit state space. -/
theorem sum_qubitBellEffects_comp_dagger :
    ∑ i, qubitBellEffects i ≫ (qubitBellEffects i)† = 𝟙 (Qubit ⊗ Qubit) := by
  simpa only [qubitBellEffects_eq_braArrow, braArrow_dagger] using
    sum_braArrow_comp_ketArrow bellBasis

/-- The existing orthonormal-basis Born rule normalizes Bell measurement probabilities. -/
theorem sum_probability_qubitBellEffects (ψ : (Qubit ⊗ Qubit).state) (hψ : ‖ψ‖ = 1) :
    ∑ i, probability (ketArrow ψ) (qubitBellEffects i) = 1 := by
  simpa only [qubitBellEffects_eq_braArrow] using sum_probability_orthonormalBasis bellBasis ψ hψ

/-- A Bell outcome has probability equal to its squared inner-product amplitude. -/
theorem scalarRingEquiv_probability_qubitBellEffects (ψ : (Qubit ⊗ Qubit).state) (i : Fin 4) :
    scalarRingEquiv (probability (ketArrow ψ) (qubitBellEffects i)) =
      (‖inner ℂ (bellBasis i) ψ‖ ^ 2 : ℂ) := by
  simpa only [qubitBellEffects_eq_braArrow] using
    scalarRingEquiv_probability_ketArrow_braArrow ψ (bellBasis i)

/-- Real Bell outcome probabilities sum to one on any unit input. -/
theorem sum_probability_re_qubitBellEffects (ψ : (Qubit ⊗ Qubit).state) (hψ : ‖ψ‖ = 1) :
    ∑ i, (scalarRingEquiv (probability (ketArrow ψ) (qubitBellEffects i))).re = 1 := by
  simpa only [qubitBellEffects_eq_braArrow] using
    sum_probability_re_orthonormalBasis bellBasis ψ hψ

/-- Measuring a Bell basis state returns its own outcome with probability one. -/
theorem probability_qubitBellEffects_basis_vector (i j : Fin 4) :
    scalarRingEquiv (probability (ketArrow (bellBasis i)) (qubitBellEffects j)) =
      if i = j then 1 else 0 := by
  simpa only [qubitBellEffects_eq_braArrow] using probability_basis_vector bellBasis i j

/-! ### The four unnormalized branches

The source's unnormalized Bell data makes each branch exactly the identity, by the abstract
theorem `CategoryTheory.correctedTeleportation_eq_id`. -/

/-- The branch whose correction is the identity recovers the input. -/
theorem correctedTeleportation_id :
    correctedTeleportation Qubit Qubit (𝟙 Qubit) = 𝟙 Qubit :=
  correctedTeleportation_eq_id ..

/-- The branch whose correction is the Pauli `Z` gate recovers the input. -/
theorem correctedTeleportation_pauliZ :
    correctedTeleportation Qubit Qubit Qubit.pauliZ.asHom = 𝟙 Qubit :=
  correctedTeleportation_eq_id ..

/-- The branch whose correction is the Pauli `X` gate recovers the input. -/
theorem correctedTeleportation_pauliX :
    correctedTeleportation Qubit Qubit Qubit.pauliX.asHom = 𝟙 Qubit :=
  correctedTeleportation_eq_id ..

/-- The branch whose correction is the gate `J` of Example 3.17 recovers the input. -/
theorem correctedTeleportation_jGate :
    correctedTeleportation Qubit Qubit jGate.asHom = 𝟙 Qubit :=
  correctedTeleportation_eq_id ..

/-- All four outcomes of the protocol recover the input. -/
theorem correctedTeleportation_corrections (i : Fin 4) :
    correctedTeleportation Qubit Qubit (corrections i) = 𝟙 Qubit :=
  correctedTeleportation_eq_id _

/-! ### The normalized branch

With a factor `1/√2` on the resource state and on the effect, the branch map is `(1/2) • 𝟙`. -/

/-- The normalized branch, before applying the correction, sends `x` to `(1/2) • U† x`. -/
lemma branch_no_correction (U : Qubit ⟶ Qubit) (x : Qubit.state) :
    (teleportationBranch bellState (bellEffect U) (𝟙 Qubit)) x
      = (1 / 2 : ℂ) • (U† x) := by
  have hterm : ∀ i : Fin 2,
      (λ_ Qubit).hom ((bellEffect U ▷ Qubit) ((α_ Qubit Qubit Qubit).inv
        (x ⊗ₜ[ℂ] (ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 i))))
        = (bellFactor * basisForm (ZBasis 2) (U† x) (ZBasis 2 i)) • ZBasis 2 i := by
    intro i
    rw [associator_inv_apply, whiskerRight_apply, bellEffect_apply, leftUnitor_hom_apply]
  have hsum : ∑ i : Fin 2,
      (bellFactor * basisForm (ZBasis 2) (U† x) (ZBasis 2 i)) • ZBasis 2 i
      = bellFactor • (U† x) := by
    calc ∑ i : Fin 2,
          (bellFactor * basisForm (ZBasis 2) (U† x) (ZBasis 2 i)) • ZBasis 2 i
        = ∑ i : Fin 2,
            bellFactor • (basisForm (ZBasis 2) (U† x) (ZBasis 2 i) • ZBasis 2 i) :=
          Finset.sum_congr rfl fun i _ => mul_smul ..
      _ = bellFactor • ∑ i : Fin 2,
            basisForm (ZBasis 2) (U† x) (ZBasis 2 i) • ZBasis 2 i := (Finset.smul_sum ..).symm
      _ = bellFactor • (U† x) := by
          congr 1
          conv_rhs => rw [← (ZBasis 2).sum_repr' (U† x)]
          exact Finset.sum_congr rfl fun i _ => by rw [basisForm_apply_basis, bra_apply]
  rw [teleportationBranch]
  simp only [comp_apply, Category.comp_id]
  rw [rightUnitor_inv_apply, whiskerLeft_apply, bellState_apply, one_smul,
    tmul_smul_sum_tmul]
  rw [map_smul, map_sum, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm]
  rw [hsum, smul_smul, bellFactor_mul_self]

/-- The normalized branch of a unitary correction sends `x` to `(1/2) • x`. -/
theorem normalizedBranch_apply (U : Qubit ⟶ Qubit) [IsUnitary U] (x : Qubit.state) :
    (teleportationBranch bellState (bellEffect U) U) x = (1 / 2 : ℂ) • x := by
  have hstep : teleportationBranch bellState (bellEffect U) U
      = teleportationBranch bellState (bellEffect U) (𝟙 Qubit) ≫ U := by
    rw [teleportationBranch_comp, Category.id_comp]
  rw [hstep, comp_apply, branch_no_correction, map_smul,
    show U (U† x) = x by
      simpa only [comp_apply, id_apply] using
        congrArg (fun f : Qubit ⟶ Qubit => f x) ‹IsUnitary U›.dagger_comp_eq_id]

/-- The normalized branch of a unitary correction is `(1/2) • 𝟙` as a linear map. -/
theorem normalizedBranch_eq_smul (U : Qubit ⟶ Qubit) [IsUnitary U] :
    (teleportationBranch bellState (bellEffect U) U).hom = (1 / 2 : ℂ) • LinearMap.id :=
  LinearMap.ext fun x => by
    simpa only [LinearMap.smul_apply, LinearMap.id_apply] using normalizedBranch_apply U x

/-- For a unit input state, the normalized state of a unitary branch has squared norm `1/4`. -/
theorem branch_probability (U : Qubit ⟶ Qubit) [IsUnitary U] (ψ : Qubit.state)
    (hψ : ‖ψ‖ = 1) :
    ‖(teleportationBranch bellState (bellEffect U) U) ψ‖ ^ 2 = 1 / 4 := by
  rw [normalizedBranch_apply U ψ, norm_smul, hψ]
  norm_num

end

end QuditCat
