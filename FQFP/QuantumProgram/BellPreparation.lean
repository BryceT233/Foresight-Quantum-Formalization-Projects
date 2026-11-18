/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

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

/-- Controlled NOT permutes the computational basis by adding the control to the target mod two. -/
def controlledNot : Qubit ⊗ Qubit ⟶ Qubit ⊗ Qubit :=
  let b := (ZBasis 2).tensorProduct (ZBasis 2)
  (isoMk (b.equiv b (Equiv.prodCongrRight fun a => Equiv.addLeft a)).toLinearEquiv).hom

instance : IsUnitary controlledNot :=
  isUnitary_isoMk_coe_LIEquiv (H₁ := Qubit ⊗ Qubit) (H₂ := Qubit ⊗ Qubit) _

/-- Action of controlled NOT on every computational basis input, with the left qubit as control. -/
theorem controlledNot_basis (a b : Fin 2) :
    controlledNot.hom (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b) =
      ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 (a + b) := by
  let e := (ZBasis 2).tensorProduct (ZBasis 2)
  have h : controlledNot.hom (e (a, b)) = e (a, a + b) :=
    e.equiv_apply_basis e (Equiv.prodCongrRight fun i => Equiv.addLeft i) (a, b)
  simpa only [e, OrthonormalBasis.tensorProduct_apply] using h

/-- Hadamard on the first qubit, followed by controlled NOT on the ordered pair. -/
def bellPreparation : UnitaryProgram (Qubit ⊗ Qubit) :=
  .seq (.gateHom (.left .whole) Qubit.H.asHom) (.gateHom .whole controlledNot)

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
