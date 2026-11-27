/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Circuit.Dynamic
public import FQFP.QuantumProgram.IsingChain.Circuit
public import FQFP.QuantumProgram.Register.TensorPower

/-!
# Ising instructions as dynamic circuits

The existing instruction lists supply both the native CNOT count and the ordered operands.
Compilation acts by the original Ising gates in ordered-memory coordinates.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram.IsingChain

variable {e : ℕ} {Store : Type*}

/-- Read the native instruction list as a straight-line dynamic circuit. -/
def dynamicCircuit (gs : List (Gate e)) :
    DynamicCircuit Store (RegisterReadout Store (fun _ : Fin (e + 1) => Qubit)) Gate.operands :=
  .ofList gs

/-- The native semantics of each gate on its one- or two-qubit operand register. -/
noncomputable def Gate.localProgram (g : Gate e) :
    UnitaryProgram (tensorMemory (fun _ : Fin g.operands.1 => Qubit)) :=
  match g with
  | .rx _ θ => .liftGate (S := Qubit) (tensorPowerMemoryEquiv Qubit 0).toStarAlgHom
      (QuantumProgram.rx θ)
  | .rz _ θ => .liftGate (S := Qubit) (tensorPowerMemoryEquiv Qubit 0).toStarAlgHom
      (QuantumProgram.rz θ)
  | .cnot _ => .liftGateHom (S := Qubit ⊗ Qubit) (tensorPowerMemoryEquiv Qubit 1).toStarAlgHom
      Qubit.CNOT

/-- The local implementation acts by the original whole-chain gate in the new coordinates. -/
theorem Gate.orderedLift_localProgram (g : Gate e) :
    orderedLift (fun _ => Qubit) g.operands.2 g.localProgram.toOperator =
      tensorPowerMemoryEquiv Qubit e g.program.toOperator := by
  cases g with
  | rx i θ =>
    exact orderedLift_tensorPowerMemoryEquiv_single (Gate.rx i θ).operands.2
      (endAlgEquiv Qubit (QuantumProgram.rx θ))
  | rz i θ =>
    exact orderedLift_tensorPowerMemoryEquiv_single (Gate.rz i θ).operands.2
      (endAlgEquiv Qubit (QuantumProgram.rz θ))
  | cnot j =>
    exact orderedLift_tensorPowerMemoryEquiv_pair (Gate.cnot j).operands.2 j
      (Fin.ext (Nat.add_zero _)) rfl Qubit.CNOT.hom

/-- The compiled list executes the original Ising instructions in ordered-memory coordinates. -/
theorem compile_dynamicCircuit (gs : List (Gate e)) :
    (dynamicCircuit (Store := Store) gs).compile Gate.localProgram (fun _ I => I) =
      .forList gs (fun g => .unitary (fun _ => g.operands.2) (fun _ _ =>
        .liftGate (tensorPowerMemoryEquiv Qubit e).toStarAlgHom g.program.denoteEnd)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change Command.seq _ _ = Command.seq _ _
    apply congrArg₂ Command.seq _ ih
    rw [DynamicCircuit.compile, Command.unitaryOnRegister, Command.unitaryOn]
    congr 1
    funext σ hi
    exact UnitaryProgram.liftGate_eq_of_operator_eq _ _ _ _ g.orderedLift_localProgram

/-- Counting CNOTs through the circuit API agrees with the native count on every list. -/
theorem gateCountBound_dynamicCircuit (gs : List (Gate e)) :
    (dynamicCircuit (Store := Store) gs).gateCountBound Gate.isCNOT = cnotCount gs :=
  DynamicCircuit.gateCountBound_ofList gs _

/-- The Lie–Trotter circuit executes two CNOTs per edge and time step. -/
theorem gateCountBound_circuit (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) :
    (dynamicCircuit (Store := Store) (circuit h J t r)).gateCountBound Gate.isCNOT =
      2 * r * e := (gateCountBound_dynamicCircuit _).trans (cnotCount_circuit h J t r)

end QuantumProgram.IsingChain
