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
QuantumComputation/QuantumHoareLogic/CleanAncilla.lean (clean and promised-input subroutines)
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Assertion.Kraus
public import FQFP.QuantumProgram.Logic.PrimitiveRules
public import FQFP.QuantumProgram.Register.ComputationalBasis
public import FQFP.QuantumProgram.Semantics.Precondition.Weakest
public import Mathlib.Data.Fin.Tuple.Embedding
public import FQFP.QuantumProgram.Register.Ordered
public import FQFP.QuantumProgram.Register.Permutation
import FQFP.CQM.Qudit.State.OperatorNorm

/-!
# Exact subroutines with clean ancillas

The caller supplies disjoint data and workspace registers. Testing every whole-memory effect
after projection onto the all-zero workspace specifies the channel on coherent data inputs.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {Store : Type*}

/-- Compress a whole-memory effect to the subspace where the ancilla register is all zero. -/
noncomputable def Assertion.restrictToZeroAncilla {n m : ℕ} (A : Assertion Store (qubitMemory n))
    (r : Fin m ↪ Fin n) : Assertion Store (qubitMemory n) := by
  let v := UnitState.ofBasis (registerBasis (ZBasis 2) m) (fun _ => 0)
  let ρ := Density.pure v
  let F := orderedLift (fun _ => Qubit) r
  have h : star ρ.op * ρ.op ≤ 1 := by
    change ρ.op.adjoint * ρ.op ≤ 1
    rw [ρ.adjoint_op, Density.pure_mul_self]
    exact (Assertion.pure v ()).2.2
  exact Assertion.kraus (fun _ (_ : Unit) => F ρ.op) (fun _ => by
    rw [Fintype.sum_unique]
    change star (F ρ.op) * F ρ.op ≤ 1
    simpa only [map_mul, map_star, map_one] using OrderHomClass.mono F h) (fun _ => A)

/-- Total Hoare specification for clean workspace and arbitrary whole-memory observables. -/
def RealizesCleanSubroutine {n d m : ℕ} (data : Fin d ↪ Fin n) (anc : Fin m ↪ Fin n)
    (U : UnitaryProgram (qubitMemory d)) (c : Command Store (Fin n) (qubitMemory n)) : Prop :=
  ∀ E : Set.Icc (0 : Operator (qubitMemory n)) 1,
    let post : Assertion Store (qubitMemory n) := Assertion.restrictToZeroAncilla (fun _ => E) anc
    let ideal := UnitaryProgram.liftGate (orderedLift (fun _ => Qubit) data) U.denoteEnd
    validTot ((post.channelPre fun _ => ideal.toChannel).restrictToZeroAncilla anc) c post

/-- Exact implementation of a joint unitary on the span of the allowed system words with zero
workspace. Compress both effect pullbacks to that input subspace. The postcondition can observe
the entire memory, including the output workspace. -/
def RealizesUnitaryFromBasisOutcomesAndZeroWorkspace {n k m : ℕ} (sys : Fin k ↪ Fin n)
    (outcomes : Finset (Fin (2 ^ k))) (anc : Fin m ↪ Fin n)
    (hd : Disjoint (Set.range sys) (Set.range anc)) (W : UnitaryProgram (qubitMemory (k + m)))
    (c : Command Store (Fin n) (qubitMemory n)) : Prop :=
  let Q := withZeroWorkspace sys anc (basisOutcomesProjector outcomes)
  let U := UnitaryProgram.liftGate (orderedLift (fun _ => Qubit) (Fin.Embedding.append hd))
    W.denoteEnd
  ∀ (E : Set.Icc (0 : Operator (qubitMemory n)) 1) (σ : Store),
    let post : Assertion Store (qubitMemory n) := fun _ => E
    Q.adjoint * (U.toChannel.pullbackEffect E).val * Q ≤ Q.adjoint * (wp c post σ).val * Q

end QuantumProgram
