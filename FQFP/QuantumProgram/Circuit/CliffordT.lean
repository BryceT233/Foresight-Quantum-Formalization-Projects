/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/Circuits/Gates.lean (gate vocabulary and control/target order)
QuantumComputation/Circuits/Basic.lean (a primitive on an ordered register)
QuantumComputation/Circuits/DynamicCircuit.lean (one-wire readout and classical control)
QuantumComputation/Circuits/ResourceCounting.lean (worst-branch primitive counts)
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Circuit.Dynamic
public import FQFP.QuantumProgram.Register.Permutation
public import FQFP.QuantumProgram.Register.TensorPower
public import FQFP.CQM.Qudit.State.Pure.Qubit
public import FQFP.CQM.Qudit.Measurement.Luders

/-!
# Clifford + T circuits with measurement

The instruction set also admits a primitive Toffoli so that specifications can require its
count to be zero after decomposition. A Z readout overwrites the circuit's classical integer
cell with the observed bit. Compilation and resource counts use the same ordered instructions.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram.CliffordT

/-- Named primitives with their arities. Control wires precede targets. -/
inductive Gate : ℕ → Type where
  | x : Gate 1
  | y : Gate 1
  | z : Gate 1
  | h : Gate 1
  | s : Gate 1
  | t : Gate 1
  | cnot : Gate 2
  | swap : Gate 2
  | toffoli : Gate 3
  deriving DecidableEq

/-- The name and ordered, pairwise distinct operands of a primitive. -/
structure Instruction (n : ℕ) where
  /-- Number of local wires. -/
  {arity : ℕ}
  /-- Named primitive to apply. -/
  gate : Gate arity
  /-- Local wires in operand order. -/
  wires : Fin arity ↪ Fin n

/-- Operand descriptor consumed by the FQFP compiler and support query. -/
def Instruction.operands {n : ℕ} (g : Instruction n) : (k : ℕ) × (Fin k ↪ Fin n) :=
  ⟨g.arity, g.wires⟩

/-- FQFP interpretations of the native instructions on their local tensor memories. -/
noncomputable def Gate.program {k : ℕ} : Gate k → UnitaryProgram (qubitMemory k)
  | .x => .gate (.left .whole) Qubit.pauliX
  | .y => .gate (.left .whole) Qubit.pauliY
  | .z => .gate (.left .whole) Qubit.pauliZ
  | .h => .gate (.left .whole) Qubit.H
  | .s => .gate (.left .whole) Qubit.S
  | .t => .gate (.left .whole) Qubit.T
  | .cnot => .liftGateHom (S := Qubit ⊗ Qubit) (tensorPowerMemoryEquiv Qubit 1).toStarAlgHom
      Qubit.CNOT
  | .swap => .permuteSites (ZBasis 2) (Equiv.swap 0 1)
  | .toffoli => .liftGateHom (S := Qubit ⊗ (Qubit ⊗ Qubit))
      (tensorPowerMemoryEquiv Qubit 2).toStarAlgHom (Qubit.controlled Qubit.CNOT)

/-- The only readout measures one wire in the Z basis and overwrites the single integer cell. -/
inductive Readout {n : ℕ} : {k : ℕ} → (Fin k ↪ Fin n) → ℕ → Type where
  | measure (r : Fin 1 ↪ Fin n) : Readout r 2

/-- Native gates, single-qubit measurements and branches on the classical cell. -/
abbrev Circuit (n : ℕ) := DynamicCircuit ℤ (@Readout n) (@Instruction.operands n)

/-- Interpret the measurement label with the computational-basis Lüders instrument. -/
noncomputable def Readout.interpret {n k m : ℕ} {r : Fin k ↪ Fin n} :
    Readout r m → RegisterReadout ℤ (fun _ => Qubit) r m
  | .measure _ =>
    let B := (registerBasis (ZBasis 2) 1).reindex (Equiv.funUnique (Fin 1) (Fin 2))
    ⟨(POVM.ofBasis B).luders, fun i _ => (i.val : ℤ)⟩

/-- Compile precisely the circuit used for resource counting. -/
noncomputable def Circuit.compile {n : ℕ} (c : Circuit n) : Command ℤ (Fin n) (qubitMemory n) :=
  DynamicCircuit.compile (fun g => g.gate.program) (fun _ label => label.interpret) c

/-- Worst-branch count of a named gate. Measurements are free, sequences add and branches take
the maximum. -/
def Circuit.count {n k : ℕ} (c : Circuit n) (gate : Gate k) : ℕ :=
  c.gateCountBound fun g => decide ((⟨g.arity, g.gate⟩ : Σ a, Gate a) = ⟨k, gate⟩)

end QuantumProgram.CliffordT
