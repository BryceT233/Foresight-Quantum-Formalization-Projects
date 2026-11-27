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
QuantumComputation/Maths/Basis.lean (little-endian integer basis indices)
QuantumComputation/Registers/Assertions.lean (projector onto selected computational outcomes)
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Register.Permutation
public import FQFP.QuantumProgram.Register.Ordered
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Integer coordinates on a qubit register

Site zero is the least significant bit. Matrices and sets of encoded inputs use this same basis.
-/

@[expose] public noncomputable section

open Qudit

namespace QuantumProgram

/-- Computational basis of an ordered qubit register indexed by its little-endian word. -/
def qubitWordBasis (k : ℕ) : OrthonormalBasis (Fin (2 ^ k)) ℂ (qubitMemory k).state :=
  (registerBasis (ZBasis 2) k).reindex finFunctionFinEquiv

/-- Interpret a matrix of computational-basis amplitudes as an operator on ordered qubits. -/
def qubitOperatorOfMatrix {k : ℕ} (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    Operator (qubitMemory k) :=
  (LinearMap.toMatrixOrthonormal (qubitWordBasis k)).symm M

/-- Orthogonal projector onto the joint span of the specified basis words. -/
def basisOutcomesProjector {k : ℕ} (outcomes : Finset (Fin (2 ^ k))) : Operator (qubitMemory k) :=
  qubitOperatorOfMatrix (Matrix.diagonal fun x => if x ∈ outcomes then 1 else 0)

/-- Lift a system input projector and restrict the workspace to the all-zero word. -/
def withZeroWorkspace {k m n : ℕ} (sys : Fin k ↪ Fin n) (anc : Fin m ↪ Fin n)
    (P : Operator (qubitMemory k)) : Operator (qubitMemory n) :=
  orderedLift (fun _ => Qubit) sys P * orderedLift (fun _ => Qubit) anc (basisOutcomesProjector {0})

end QuantumProgram
