/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the two-gate preparation and its Bell output state.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/BellStateTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.CQM.Qudit.State.Pure.Qubit
public import FQFP.QuantumProgram.Unitary
public import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Bell preparation on two qubits

Starting in the computational basis state `|00⟩`, apply Hadamard on the left register,
then controlled NOT with the left qubit as control. The output of the program's channel
is the Bell resource already used by the teleportation protocol.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

noncomputable section

/-- Controlled NOT on the two-qubit program memory. -/
def controlledNot : Qubit ⊗ Qubit ⟶ Qubit ⊗ Qubit := Qubit.CNOT

instance : IsUnitary controlledNot := inferInstanceAs (IsUnitary Qubit.CNOT)

/-- Action of the program's controlled NOT in the computational basis. -/
theorem controlledNot_basis (a b : Fin 2) :
    controlledNot.hom (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b) =
      ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 (a + b) :=
  Qubit.CNOT_basis a b

/-- Hadamard on the first qubit, followed by controlled NOT on the ordered pair. -/
def bellPreparation : UnitaryProgram (Qubit ⊗ Qubit) :=
  .seq (.gate (.left .whole) Qubit.H) (.gateHom .whole controlledNot)

/-- The initial unit vector in the two-qubit computational basis. -/
def zeroZero : UnitState (Qubit ⊗ Qubit) :=
  UnitState.ofBasis ((ZBasis 2).tensorProduct (ZBasis 2)) (0, 0)

private theorem hadamard_zero :
    Qubit.H.asHom (ZBasis 2 0) = bellFactor • (ZBasis 2 0 + ZBasis 2 1) := by
  rw [Qubit.H, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  simp [bellFactor, smul_add]

/-- The program prepares the normalized Bell vector, including its phase. -/
theorem bellPreparation_zeroZero : bellPreparation.denoteHom zeroZero = bellState (1 : ℂ) := by
  rw [show (zeroZero : (Qubit ⊗ Qubit).state) = ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 0 from
    OrthonormalBasis.tensorProduct_apply _ _ _ _]
  change controlledNot.hom (Qubit.H.asHom (ZBasis 2 0) ⊗ₜ[ℂ] ZBasis 2 0) = _
  rw [hadamard_zero, ← TensorProduct.smul_tmul', TensorProduct.add_tmul, map_smul, map_add,
    controlledNot_basis, controlledNot_basis, bellState_apply, one_smul, Fin.sum_univ_two]
  simp

/-- The final density operator of the two-gate program is the existing Bell density operator. -/
theorem bellPreparation_op :
    (bellPreparation.toChannel.map (Density.pure zeroZero)).op = Qudit.bellDensity.op := by
  rw [UnitaryProgram.op_map_pure, bellPreparation_zeroZero, bellDensity_op_eq_outer_bellState]

end

end QuantumProgram
