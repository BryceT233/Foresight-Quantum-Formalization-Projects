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
QuantumComputationSpecs/Algorithms/StoppingPower.lean (ApproximatesTimeEvolution)
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Register.ComputationalBasis
public import FQFP.CQM.Qudit.State.OperatorNorm
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Time evolution on a subspace with clean workspace

The logical register is ordered with the system first and the workspace second.
The operator norm tests all superpositions in the promised input subspace.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- On system inputs selected by `P` with zero workspace, `W` approximates the ideal
Hamiltonian evolution tensored with identity, up to a single global phase. -/
def ApproximatesTimeEvolution {k m : ℕ} (H : Operator (qubitMemory k)) (t ε : ℝ)
    (P : Operator (qubitMemory k)) (W : UnitaryProgram (qubitMemory (k + m))) : Prop :=
  let sys : Fin k ↪ Fin (k + m) := Fin.castAddEmb m
  let anc : Fin m ↪ Fin (k + m) := Fin.natAddEmb k
  let target := orderedLift (fun _ => Qubit) sys (NormedSpace.exp ((-Complex.I * t) • H))
  ∃ φ : ℝ, ‖(W.toOperator - Complex.exp (φ * Complex.I) • target) *
    withZeroWorkspace sys anc P‖ ≤ ε

end QuantumProgram
