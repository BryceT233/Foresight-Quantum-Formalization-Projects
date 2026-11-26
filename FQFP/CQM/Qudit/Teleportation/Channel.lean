/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.Teleportation.Basic

/-!
# Teleportation as a quantum channel

The Kraus operators are the actual corrected branches of the existing Bell protocol.
Each branch sends an arbitrary operator to one quarter of itself. Branch outputs are
unnormalized positive operators; only the sum of the four branches is trace preserving.
Consequently the protocol transmits every mixed state, including states entangled with
an arbitrary finite-dimensional reference system.

## Main definitions and results

* `Qudit.teleportationChannel`: the channel obtained by summing corrected Bell branches.
* `Qudit.teleportationChannel_eq_id`: corrected teleportation is the identity channel.
* `Qudit.teleportationChannel_tensor_map`: teleportation preserves states entangled with a
  reference.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Qudit

noncomputable section

/-- The linear operator of the existing corrected Bell-protocol branch. -/
def teleportationKraus (i : Fin 4) : Operator Qubit :=
  (teleportationBranch bellState (qubitBellEffects i) (corrections i)).hom

/-- Every corrected branch operator is one half of the identity. -/
lemma teleportationKraus_eq_smul (i : Fin 4) :
    teleportationKraus i = (1 / 2 : ℂ) • LinearMap.id :=
  normalizedBranch_eq_smul (corrections i)

/-- The CP superoperator of a single observed, corrected teleportation branch. -/
def teleportationBranchMap (i : Fin 4) : Superoperator Qubit Qubit :=
  Superoperator.conjugate (teleportationKraus i)

/-- A branch is completely positive without being normalized as a channel. -/
lemma isCompletelyPositive_teleportationBranchMap (i : Fin 4) :
    (teleportationBranchMap i).IsCompletelyPositive :=
  Superoperator.isCompletelyPositive_conjugate _

/-- Every corrected branch sends any input operator to one quarter of itself. -/
lemma teleportationBranchMap_apply (i : Fin 4) (A : Operator Qubit) :
    teleportationBranchMap i A = (1 / 4 : ℂ) • A := by
  rw [teleportationBranchMap, teleportationKraus_eq_smul, Superoperator.conjugate_apply]
  simp only [map_smulₛₗ, map_div₀, map_one, map_ofNat, LinearMap.adjoint_id,
    LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id,
    smul_smul]
  norm_num

/-- Every branch of a density input has probability one quarter. -/
lemma trace_teleportationBranchMap (i : Fin 4) (ρ : Density Qubit) :
    (teleportationBranchMap i ρ.op).trace = 1 / 4 := by
  rw [teleportationBranchMap_apply]
  simp [Operator.trace, ρ.trace_one]

/-- A single branch is not trace preserving and must not be bundled as a channel. -/
lemma not_isTracePreserving_teleportationBranchMap (i : Fin 4) :
    ¬ (teleportationBranchMap i).IsTracePreserving := by
  intro h
  let ρ := Density.pure (UnitState.ofBasis (ZBasis 2) 0)
  have hp := h ρ.op
  rw [trace_teleportationBranchMap, ρ.trace_one] at hp
  norm_num at hp

/-- The four actual branch operators satisfy the Kraus completeness identity. -/
lemma sum_teleportationKraus_adjoint_comp :
    ∑ i, (teleportationKraus i).adjoint ∘ₗ teleportationKraus i = 1 := by
  simp only [teleportationKraus_eq_smul, map_smulₛₗ, map_div₀, map_one, map_ofNat,
    LinearMap.adjoint_id,
    LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, smul_smul]
  rw [Fin.sum_univ_four]
  simp only [← add_smul]
  norm_num
  rfl

/-- Summing the unnormalized branches gives the identity on all operators. -/
lemma sum_teleportationBranchMap :
    ∑ i, teleportationBranchMap i = (LinearMap.id : Superoperator Qubit Qubit) := by
  apply LinearMap.ext
  intro A
  rw [LinearMap.sum_apply]
  simp only [teleportationBranchMap_apply]
  rw [Fin.sum_univ_four]
  simp only [← add_smul, LinearMap.id_apply]
  norm_num

/-- The trace-preserving channel obtained by forgetting the corrected Bell outcome. -/
def teleportationChannel : QuantumChannel Qubit Qubit :=
  QuantumChannel.ofKraus teleportationKraus sum_teleportationKraus_adjoint_comp

/-- Mixed-state teleportation is exactly the identity channel. -/
lemma teleportationChannel_eq_id : teleportationChannel = QuantumChannel.id Qubit := by
  apply QuantumChannel.ext
  exact sum_teleportationBranchMap

/-- Teleportation transmits every density state, without a purity assumption. -/
lemma teleportationChannel_map (ρ : Density Qubit) : teleportationChannel.map ρ = ρ := by
  rw [teleportationChannel_eq_id, QuantumChannel.map_id]

/-- The channel preserves arbitrary entanglement with an untouched reference system. -/
lemma teleportationChannel_tensor_map (R : Qudit) (ρ : Density (Qubit ⊗ R)) :
    (teleportationChannel.tensor (QuantumChannel.id R)).map ρ = ρ := by
  apply Density.ext
  rw [teleportationChannel_eq_id]
  change Superoperator.tensor LinearMap.id LinearMap.id ρ.op = ρ.op
  rw [Superoperator.tensor_id_id]
  rfl

end

end Qudit
