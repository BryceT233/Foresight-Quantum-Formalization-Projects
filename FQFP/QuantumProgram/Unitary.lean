/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Composite
public import FQFP.QuantumProgram.Circuit

/-!
# Qudit semantics of unitary programs

A program's unitary denotation acts on amplitudes by its underlying linear map
and on density operators by conjugation.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram.Register

variable {H S : Qudit}

/-- Extending a register into the left tensor factor tensors its operator with the identity. -/
theorem toContinuousLinearMap_liftEnd_left (r : Register H S) (K : Qudit) (A : CQM.Operator S) :
    LinearMap.toContinuousLinearMap (endAlgEquiv (H ⊗ K) (r.left.liftEnd A)) =
      (LinearMap.toContinuousLinearMap (endAlgEquiv H (r.liftEnd A))).rTensor K.state := rfl

/-- Extending a register into the right tensor factor tensors the identity with its operator. -/
theorem toContinuousLinearMap_liftEnd_right (r : Register H S) (K : Qudit) (A : CQM.Operator S) :
    LinearMap.toContinuousLinearMap (endAlgEquiv (K ⊗ H) (r.right.liftEnd A)) =
      (LinearMap.toContinuousLinearMap (endAlgEquiv H (r.liftEnd A))).lTensor K.state := by
  apply ContinuousLinearMap.coe_injective
  exact (ContinuousLinearMap.toLinearMap_lTensor K.state
    (LinearMap.toContinuousLinearMap (endAlgEquiv H (r.liftEnd A)))).symm

end QuantumProgram.Register

namespace QuantumProgram.UnitaryProgram

variable {H : Qudit}

/-- A program acts on density operators by its unitary channel. -/
noncomputable def toChannel (p : UnitaryProgram H) : QuantumChannel H H :=
  QuantumChannel.ofIsometry p.denoteHom

/-- The qudit operator acting on amplitudes of the whole memory. -/
noncomputable def toOperator (p : UnitaryProgram H) : Qudit.Operator H :=
  endAlgEquiv H p.denoteEnd

/-- Interpret a gate on a register as a linear operator on memory. -/
theorem toOperator_gateHom {S : Qudit} (r : Register H S) (U : S ⟶ S)
    [DaggerCategory.IsUnitary U] :
    (gateHom r U).toOperator = endAlgEquiv H (r.liftEnd (.of U)) :=
  congrArg (endAlgEquiv H) (denoteEnd_gateHom r U)

/-- The first gate executed is the rightmost factor in the operator product. -/
theorem toOperator_sequence (ps : List (UnitaryProgram H)) :
    (sequence ps).toOperator = (ps.reverse.map toOperator).prod := by
  change endAlgEquiv H (sequence ps).denoteEnd = _
  rw [denoteEnd_sequence, map_list_prod, List.map_map]
  rfl

/-- Continuous operator form of the ordered product, for use with exponentials and norms. -/
theorem toContinuousLinearMap_toOperator_sequence (ps : List (UnitaryProgram H)) :
    LinearMap.toContinuousLinearMap (sequence ps).toOperator =
      (ps.reverse.map fun p => LinearMap.toContinuousLinearMap p.toOperator).prod := by
  change Module.End.toContinuousLinearMap H.state (sequence ps).toOperator = _
  rw [toOperator_sequence, map_list_prod, List.map_map]
  rfl

/-- Sequential execution composes the two channels in execution order. -/
theorem toChannel_seq (p q : UnitaryProgram H) :
    (p.seq q).toChannel = q.toChannel.comp p.toChannel :=
  QuantumChannel.ofIsometry_comp p.denoteHom q.denoteHom

/-- The channel acts on every operator by conjugation with the program's denotation. -/
theorem toSuperoperator_toChannel_apply (p : UnitaryProgram H) (A : CQM.Operator H) :
    p.toChannel.toSuperoperator (endAlgEquiv H A) =
      endAlgEquiv H (p.denoteEnd * A * star p.denoteEnd) := rfl

/-- On a pure input the output operator is the projector onto the evolved vector. -/
theorem op_map_pure (p : UnitaryProgram H) (v : UnitState H) :
    (p.toChannel.map (Density.pure v)).op = Operator.outer (p.denoteHom v) (p.denoteHom v) := by
  rw [toChannel, QuantumChannel.map_ofIsometry, Density.map_pure, Density.op_pure]
  rfl

end QuantumProgram.UnitaryProgram
