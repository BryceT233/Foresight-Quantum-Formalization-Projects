/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Measurement.ClassicalRegister
public import FQFP.CQM.Qudit.Teleportation.Channel

/-!
# Teleportation with an observed Bell result

The measurement instrument uses the actual Bell resource and Bell effects before correction.
Recording its result and applying a classically controlled correction is proved equal to the
corrected instrument. Each result has probability one quarter and conditional output equal
to the input state. Forgetting the result recovers the existing teleportation channel.

## Main definitions and results

* `Qudit.teleportationMeasurement`: the uncorrected Bell measurement instrument.
* `Qudit.teleportationInstrument`: Bell branches with outcome-dependent corrections.
* `Qudit.conditional_teleportationInstrument`: every conditional corrected state is the input.
* `Qudit.teleportationInstrument_record`: recording and controlled correction implement
  teleportation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Qudit

noncomputable section

/-- The actual Bell measurement branch, with the resource attached but no correction yet. -/
def teleportationMeasurementKraus (i : Fin 4) : Operator Qubit :=
  (teleportationBranch bellState (qubitBellEffects i) (𝟙 Qubit)).hom

/-- The corrected branch factors into the observed measurement branch and its correction. -/
lemma teleportationKraus_eq_comp_measurement (i : Fin 4) :
    teleportationKraus i = (corrections i).hom ∘ₗ teleportationMeasurementKraus i := by
  change (teleportationBranch bellState (qubitBellEffects i) (corrections i)).hom =
    ((teleportationBranch bellState (qubitBellEffects i) (𝟙 Qubit)) ≫ corrections i).hom
  rw [teleportationBranch_comp, Category.id_comp]

/-- The branch superoperator factors through an outcome-dependent unitary channel. -/
lemma teleportationBranchMap_eq_comp_measurement (i : Fin 4) :
    teleportationBranchMap i = (QuantumChannel.ofIsometry (corrections i)).toSuperoperator ∘ₗ
      Superoperator.conjugate (teleportationMeasurementKraus i) := by
  rw [teleportationBranchMap, teleportationKraus_eq_comp_measurement,
    Superoperator.conjugate_comp]
  rfl

/-- Removing the unitary correction leaves every branch trace unchanged. -/
lemma trace_teleportationMeasurementKraus (i : Fin 4) (A : Operator Qubit) :
    (Superoperator.conjugate (teleportationMeasurementKraus i) A).trace =
      (teleportationBranchMap i A).trace := by
  rw [teleportationBranchMap_eq_comp_measurement, LinearMap.comp_apply,
    (QuantumChannel.ofIsometry (corrections i)).tracePreserving]

/-- The four uncorrected Bell measurement branches form an instrument. -/
def teleportationMeasurement : Instrument Qubit Qubit (Fin 4) where
  branch i := Superoperator.conjugate (teleportationMeasurementKraus i)
  completelyPositive i := Superoperator.isCompletelyPositive_conjugate
    (teleportationMeasurementKraus i)
  tracePreserving A := by
    rw [LinearMap.sum_apply, Operator.trace, map_sum]
    change ∑ i, (Superoperator.conjugate (teleportationMeasurementKraus i) A).trace = A.trace
    simp only [trace_teleportationMeasurementKraus]
    have h := congrArg (fun f : Superoperator Qubit Qubit => (f A).trace)
      sum_teleportationBranchMap
    simpa only [LinearMap.sum_apply, map_sum, LinearMap.id_apply] using h

/-- Teleportation as an instrument, including the outcome-dependent correction. -/
def teleportationInstrument : Instrument Qubit Qubit (Fin 4) :=
  teleportationMeasurement.postprocess (fun i => QuantumChannel.ofIsometry (corrections i))

/-- The corrected instrument recovers the existing CP branch maps. -/
lemma teleportationInstrument_branch (i : Fin 4) :
    teleportationInstrument.branch i = teleportationBranchMap i :=
  (teleportationBranchMap_eq_comp_measurement i).symm

/-- Every corrected outcome has probability one quarter, for arbitrary mixed input. -/
lemma probability_teleportationInstrument (ρ : Density Qubit) (i : Fin 4) :
    teleportationInstrument.probability ρ i = 1 / 4 := by
  rw [Instrument.probability, teleportationInstrument_branch, trace_teleportationBranchMap]
  norm_num

/-- The uncorrected measurement already has the same four equiprobable results. -/
lemma probability_teleportationMeasurement (ρ : Density Qubit) (i : Fin 4) :
    teleportationMeasurement.probability ρ i = 1 / 4 := by
  rw [← Instrument.probability_postprocess teleportationMeasurement
    (fun j => QuantumChannel.ofIsometry (corrections j))]
  exact probability_teleportationInstrument ρ i

/-- Conditioning any corrected Bell result recovers the entire input density state. -/
lemma conditional_teleportationInstrument (ρ : Density Qubit) (i : Fin 4)
    (hp : 0 < teleportationInstrument.probability ρ i) :
    teleportationInstrument.conditional ρ i hp = ρ := by
  apply teleportationInstrument.conditional_eq_of_branch_eq_smul ρ i hp
  rw [teleportationInstrument_branch, teleportationBranchMap_apply]

/-- Forgetting the observed Bell result gives the existing teleportation channel. -/
lemma teleportationInstrument_toChannel :
    teleportationInstrument.toChannel = teleportationChannel := by
  apply QuantumChannel.ext
  change ∑ i, teleportationInstrument.branch i = _
  simp only [teleportationInstrument_branch]
  rfl

/-- Explicit measurement, classical recording, and controlled correction implement teleportation. -/
lemma teleportationInstrument_record :
    teleportationInstrument.record (ZBasis 4) =
      (QuantumChannel.controlled (ZBasis 4)
        (fun i => QuantumChannel.ofIsometry (corrections i))).comp
          (teleportationMeasurement.record (ZBasis 4)) :=
  teleportationMeasurement.record_postprocess _ _

/-- Discarding the classical result after the explicit controlled protocol returns the input. -/
lemma partialTraceRight_teleportationInstrument_record (ρ : Density Qubit) :
    ((teleportationInstrument.record (ZBasis 4)).map ρ).partialTraceRight = ρ := by
  rw [Instrument.partialTraceRight_record, teleportationInstrument_toChannel,
    teleportationChannel_map]

end

end Qudit
