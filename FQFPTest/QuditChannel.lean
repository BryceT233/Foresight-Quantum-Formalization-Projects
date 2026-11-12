/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.QuditCat.TeleportationChannel
import FQFP.CQM.QuditCat.BellDensity

/-!
# Quantum-channel clients

Nonunitary Kraus evolution, discarded entanglement, rectangular systems, arbitrary
reference systems, and the distinction between CP branches and normalized channels.
-/

open CategoryTheory CategoryTheory.MonoidalCategory QuditCat

noncomputable section

local notation "ρ₀" => Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))

private def dephasingKraus (i : Fin 2) : Operator Qubit :=
  Operator.outer (ZBasis 2 i) (ZBasis 2 i)

private lemma dephasing_complete :
    ∑ i, (dephasingKraus i).adjoint ∘ₗ dephasingKraus i = 1 := by
  ext x
  simp only [dephasingKraus, Operator.adjoint_outer, LinearMap.sum_apply,
    LinearMap.comp_apply, Operator.outer_apply, inner_smul_right,
    OrthonormalBasis.inner_eq_one, mul_one, Module.End.one_apply]
  exact (ZBasis 2).sum_repr' x

private def dephasing : QuantumChannel Qubit Qubit :=
  QuantumChannel.ofKraus dephasingKraus dephasing_complete

-- The Kraus constructor handles a nonunitary channel: an off-diagonal operator is erased.
example : dephasing.toSuperoperator (Operator.outer (ZBasis 2 0) (ZBasis 2 1)) = 0 := by
  ext x
  simp [dephasing, QuantumChannel.ofKraus, Superoperator.kraus_apply,
    dephasingKraus, Fin.sum_univ_two, Operator.outer_apply]

-- A computational eigenstate is fixed by dephasing.
example : dephasing.map ρ₀ = ρ₀ := by
  apply Density.ext
  ext x
  simp [QuantumChannel.map, dephasing, QuantumChannel.ofKraus,
    Superoperator.kraus_apply, dephasingKraus, Fin.sum_univ_two,
    Operator.outer_apply]

-- Tensor closure applies to arbitrary positive inputs, not just product inputs.
example {H K L M R : QuditCat} (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (A : Operator ((H ⊗ L) ⊗ R)) (hA : A.IsPositive) :
    (Superoperator.tensor (Φ.tensor Ψ).toSuperoperator
      (LinearMap.id : Superoperator R R) A).IsPositive :=
  (Φ.tensor Ψ).completelyPositive R A hA

-- Existing unitary density evolution is recovered without any Kraus coordinates.
example (ρ : Density Qubit) : (QuantumChannel.ofIsometry Qubit.H.asHom).map ρ =
    ρ.map Qubit.H.asHom := QuantumChannel.map_ofIsometry _ _

-- Discarding a qutrit after a product input returns the qubit state.
example (ρ : Density Qubit) (σ : Density (std 3)) :
    (QuantumChannel.partialTraceRight Qubit (std 3)).map (ρ.tensor σ) = ρ := by
  rw [QuantumChannel.map_partialTraceRight, Density.partialTraceRight_tensor]

-- The partial-trace channel also accepts entangled inputs and returns a mixed state.
example : (QuantumChannel.partialTraceLeft Qubit Qubit).map bellDensity =
    Density.maximallyMixed Qubit (by simp [Qubit]) := by
  rw [QuantumChannel.map_partialTraceLeft, bellDensity_partialTraceLeft]

-- A unitary followed by discarding agrees with the existing density semantics.
example (ρ : Density (Qubit ⊗ Qubit)) :
    ((QuantumChannel.partialTraceRight Qubit Qubit).comp
      ((QuantumChannel.ofIsometry Qubit.H.asHom).tensor (QuantumChannel.id Qubit))).map ρ =
      (((QuantumChannel.ofIsometry Qubit.H.asHom).tensor
        (QuantumChannel.id Qubit)).map ρ).partialTraceRight := by
  rw [QuantumChannel.map_comp, QuantumChannel.map_partialTraceRight]

-- A single teleportation branch stays unnormalized and is not trace preserving.
example (i : Fin 4) (ρ : Density Qubit) :
    (teleportationBranchMap i ρ.op).trace = 1 / 4 := trace_teleportationBranchMap i ρ

example (i : Fin 4) : ¬ (teleportationBranchMap i).IsTracePreserving :=
  not_isTracePreserving_teleportationBranchMap i

-- All four branches together transmit arbitrary mixed inputs.
example (ρ : Density Qubit) : teleportationChannel.map ρ = ρ := teleportationChannel_map ρ

-- Teleporting one half of an entangled pair preserves the entire joint state.
example : (teleportationChannel.tensor (QuantumChannel.id Qubit)).map bellDensity =
    bellDensity := teleportationChannel_tensor_map Qubit bellDensity

-- Reference systems need not be qubits or have matching dimension.
example (ρ : Density (Qubit ⊗ std 3)) :
    (teleportationChannel.tensor (QuantumChannel.id (std 3))).map ρ = ρ :=
  teleportationChannel_tensor_map (std 3) ρ

-- A normalized input cannot be sent to the zero-dimensional space by a channel.
example (Φ : QuantumChannel Qubit (std 0)) : False := isEmptyElim (Φ.map ρ₀)

-- An empty Kraus family on the zero-dimensional domain is legitimately trace preserving.
example : QuantumChannel (std 0) Qubit :=
  QuantumChannel.ofKraus (fun i : Fin 0 => Fin.elim0 i) (Subsingleton.elim _ _)

end
