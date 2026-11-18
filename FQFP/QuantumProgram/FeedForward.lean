/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Measurement
public import FQFP.QuantumProgram.Unitary
public import FQFP.CQM.Qudit.Measurement.ClassicalRegister

/-!
# Measurement followed by classical feed-forward

A program prepares its memory, measures a finite outcome into a classical register,
and executes the unitary program selected by that register. The channel semantics
represents the classical register in the computational basis.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram

/-- A preparation, a measurement with write-back, and a unitary continuation for each label. -/
structure FeedForwardProgram (H M K : Qudit) (m : ℕ) where
  /-- Prepare the memory on which the instrument acts. -/
  prepare : QuantumChannel H M
  /-- Measure the memory, leaving the quantum output on the retained subsystem. -/
  measure : Instrument M K (Fin m)
  /-- Choose the next unitary program from the stored measurement result. -/
  onResult : Fin m → UnitaryProgram K

namespace FeedForwardProgram

variable {H M K : Qudit} {m : ℕ} (p : FeedForwardProgram H M K m)

/-- Run one outcome, overwriting the old label before executing the conditional gate. -/
noncomputable def runBranch (s : CQState (Fin m) H) (i : Fin m) : CQState (Fin m) K :=
  let measured := measurementBranch p.measure (fun label _ => label) (s.map p.prepare) i
  measured.map (p.onResult measured.store).toChannel

/-- Execute the program as a channel with an explicit classical output register. -/
noncomputable def recordedChannel : QuantumChannel H (K ⊗ std m) :=
  (QuantumChannel.controlled (ZBasis m) (fun i => (p.onResult i).toChannel)).comp
    ((p.measure.record (ZBasis m)).comp p.prepare)

/-- Reading a block of the output recovers the same operator as executing that branch. -/
theorem read_recordedChannel (s : CQState (Fin m) H) (i : Fin m) :
    (Instrument.read K (ZBasis m)).branch i (p.recordedChannel.toSuperoperator s.op) =
      (p.runBranch s i).op := by
  rw [recordedChannel, ← QuantumChannel.comp_assoc, ← Instrument.record_postprocess]
  exact (p.measure.postprocess (fun j => (p.onResult j).toChannel)).read_record
    (ZBasis m) (p.prepare.toSuperoperator s.op) i

end FeedForwardProgram

end QuantumProgram
