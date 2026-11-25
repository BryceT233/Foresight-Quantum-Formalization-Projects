/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the finite-list parallel Hadamard triple.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/ParallelHadamardForTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.CQM.Qudit.Measurement.Basic
public import FQFP.QuantumProgram.Logic.Iteration.ForUnitary

/-!
# Parallel Hadamard as a finite list of commands

The program applies a Hadamard to each qubit in increasing site order. Its classical store
is arbitrary. For zero qubits it executes skip on the tensor unit.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {Store : Type*}

/-- Visit all `n` sites in order, using one Hadamard at each. -/
noncomputable def hadamardFor (n : ℕ) :
    Command Store (Fin n) (tensorMemory fun _ : Fin n => Qubit) :=
  .forList (List.finRange n) fun i => .unitaryAt (D := fun _ => Qubit) i Qubit.H

/-- The finite list of Hadamards derives the all-plus projector from the all-zero projector. -/
theorem derivTot_hadamardFor (n : ℕ) :
    let zero := UnitState.ofBasis (ZBasis 2) 0
    let prod := registerProductState (fun _ : Fin n => Qubit)
    DerivTot (Store := Store) (Assertion.pure (prod fun _ => zero)) (hadamardFor n)
      (Assertion.pure (prod fun _ => UnitState.map Qubit.H.asHom zero)) := by
  intro zero prod
  have h := DerivTot.forList_unitaryAt (D := fun _ : Fin n => Qubit) (Store := Store)
    (fun _ => Qubit.H) (List.finRange n) (List.nodup_finRange n) (fun _ => zero)
  rw [applyAtSites_finRange] at h
  exact h

/-- Total correctness of finite parallel Hadamard for every width, including zero. -/
theorem validTot_hadamardFor (n : ℕ) :
    let zero := UnitState.ofBasis (ZBasis 2) 0
    let prod := registerProductState (fun _ : Fin n => Qubit)
    validTot (Store := Store) (Assertion.pure (prod fun _ => zero)) (hadamardFor n)
      (Assertion.pure (prod fun _ => UnitState.map Qubit.H.asHom zero)) :=
  (derivTot_hadamardFor n).sound

end QuantumProgram
