/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.BellPreparation
public import FQFP.QuantumProgram.FeedForward
public import FQFP.CQM.Qudit.Teleportation.Instrument

/-!
# Teleportation with a classical outcome register

Prepare the two ancillas with the Bell circuit. Group Alice's input and ancilla together
for a measurement in the Bell basis. Write the outcome in the four-dimensional classical
register and read that register to select Bob's correction, in the order I, Z, X, J.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

private theorem preparedBellKet_eq : ketArrow (bellPreparation.denoteHom zeroZero) = bellState := by
  rw [bellPreparation_zeroZero, bellState_eq_ketArrow]
  change ketArrow ((1 : ℂ) • bellBasis 0) = ketArrow (bellBasis 0)
  rw [one_smul]

/-- Attach the circuit's Bell pair to the input and order memory as Bob, then Alice's pair. -/
def teleportationSetup : Qubit ⟶ Qubit ⊗ (Qubit ⊗ Qubit) :=
  attachTeleportationResource Qubit (ketArrow (bellPreparation.denoteHom zeroZero)) ≫
    (β_ (Qubit ⊗ Qubit) Qubit).hom

instance : IsIsometry teleportationSetup := by
  unfold teleportationSetup
  rw [preparedBellKet_eq]
  infer_instance

/-- Prepare the ancillas, measure Alice's pair, write the label and correct Bob's qubit
using the stored label. The output contains both Bob's qubit and the classical register. -/
def teleportationProgram : FeedForwardProgram Qubit (Qubit ⊗ (Qubit ⊗ Qubit)) Qubit 4 where
  prepare := QuantumChannel.ofIsometry teleportationSetup
  measure := Instrument.read Qubit bellBasis
  onResult i := .gateHom .whole (corrections i)

private theorem bellContraction (i : Fin 4) :
    ((TensorProduct.mk ℂ Qubit.state (Qubit ⊗ Qubit).state).flip (bellBasis i)).adjoint ∘ₗ
      (β_ (Qubit ⊗ Qubit) Qubit).hom.hom =
        ((qubitBellEffects i ▷ Qubit) ≫ (λ_ Qubit).hom).hom := by
  apply TensorProduct.ext'
  intro a b
  change ((TensorProduct.mk ℂ Qubit.state (Qubit ⊗ Qubit).state).flip (bellBasis i)).adjoint
    (b ⊗ₜ[ℂ] a) = (λ_ Qubit).hom ((qubitBellEffects i ▷ Qubit) (a ⊗ₜ[ℂ] b))
  rw [Superoperator.adjoint_tensorInsertion_apply, whiskerRight_apply, leftUnitor_hom_apply,
    qubitBellEffects_eq_braArrow]
  rfl

private theorem bellReadout_branch (i : Fin 4) :
    (Instrument.read Qubit bellBasis).branch i ∘ₗ
      (QuantumChannel.ofIsometry teleportationSetup).toSuperoperator =
        teleportationMeasurement.branch i := by
  change Superoperator.conjugate _ ∘ₗ Superoperator.conjugate teleportationSetup.hom =
    Superoperator.conjugate (teleportationMeasurementKraus i)
  rw [← Superoperator.conjugate_comp]
  congr 1
  rw [teleportationSetup, hom_comp, ← LinearMap.comp_assoc, bellContraction, ← hom_comp,
    preparedBellKet_eq]
  simp only [teleportationMeasurementKraus, teleportationBranch, Category.comp_id]

/-- The output with its classical label agrees with the corrected teleportation instrument. -/
theorem teleportationProgram_eq_record :
    teleportationProgram.recordedChannel = teleportationInstrument.record (ZBasis 4) := by
  rw [FeedForwardProgram.recordedChannel, teleportationInstrument_record]
  change (QuantumChannel.controlled (ZBasis 4)
    (fun i => QuantumChannel.ofIsometry (corrections i))).comp _ = _
  congr 1
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change ((Instrument.read Qubit bellBasis).record (ZBasis 4)).toSuperoperator
    ((QuantumChannel.ofIsometry teleportationSetup).toSuperoperator A) = _
  simp only [Instrument.record_apply]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun B => Operator.tensor B (Operator.outer (ZBasis 4 i) (ZBasis 4 i)))
      (LinearMap.congr_fun (bellReadout_branch i) A)

/-- Outcome `i` overwrites the classical register and carries one quarter of the input operator. -/
theorem teleportationProgram_runBranch (s : CQState (Fin 4) Qubit) (i : Fin 4) :
    (teleportationProgram.runBranch s i).store = i ∧
      (teleportationProgram.runBranch s i).op = (1 / 4 : ℂ) • s.op := by
  refine ⟨rfl, ?_⟩
  rw [← FeedForwardProgram.read_recordedChannel, teleportationProgram_eq_record,
    Instrument.read_record, teleportationInstrument_branch, teleportationBranchMap_apply]

/-- Discarding only the classical record gives the teleportation channel on all operators. -/
theorem teleportationProgram_forget_record :
    (QuantumChannel.partialTraceRight Qubit (std 4)).comp teleportationProgram.recordedChannel =
      Qudit.teleportationChannel := by
  rw [teleportationProgram_eq_record, Instrument.partialTraceRight_comp_record,
    teleportationInstrument_toChannel]

end

end QuantumProgram
