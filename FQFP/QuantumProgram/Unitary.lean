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
theorem endAlgEquiv_liftEnd_left (r : Register H S) (K : Qudit) (A : End S) :
    endAlgEquiv (H ⊗ K) (r.left.liftEnd A) =
      Operator.tensorOneHom H K (endAlgEquiv H (r.liftEnd A)) := rfl

/-- Extending a register into the right tensor factor tensors the identity with its operator. -/
theorem endAlgEquiv_liftEnd_right (r : Register H S) (K : Qudit) (A : End S) :
    endAlgEquiv (K ⊗ H) (r.right.liftEnd A) =
      Operator.oneTensorHom K H (endAlgEquiv H (r.liftEnd A)) := rfl

end QuantumProgram.Register

namespace QuantumProgram.UnitaryProgram

variable {H : Qudit}

/-- A program acts on density operators by its unitary channel. -/
noncomputable def toChannel (p : UnitaryProgram H) : QuantumChannel H H :=
  QuantumChannel.ofIsometry p.denoteHom

/-- The qudit operator acting on amplitudes of the whole memory. -/
noncomputable def toOperator (p : UnitaryProgram H) : Qudit.Operator H :=
  endAlgEquiv H p.denoteEnd

/-- Lift a local unitary endomorphism through a unital star-algebra homomorphism. -/
noncomputable def liftGate {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (U : End S) [DaggerCategory.IsUnitary U.asHom] : UnitaryProgram H :=
  let e (K : Qudit) : End K ≃⋆ₐ[ℂ] Operator K :=
    .ofAlgEquiv (endAlgEquiv K) endAlgEquiv_star
  let lift := ((e S).arrowCongr (e H)).symm F
  haveI : DaggerCategory.IsUnitary (lift U).asHom :=
    (End.mem_unitary_iff _).mp (Unitary.map_mem lift ((End.mem_unitary_iff U).mpr inferInstance))
  .gate .whole (lift U)

/-- Lift a local gate supplied as a unitary morphism. -/
noncomputable abbrev liftGateHom {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (U : S ⟶ S) [DaggerCategory.IsUnitary U] : UnitaryProgram H :=
  liftGate F (.of U)

/-- A lifted gate acts by its specified operator embedding. -/
theorem toOperator_liftGate {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (U : End S) [DaggerCategory.IsUnitary U.asHom] :
    (liftGate F U).toOperator = F (endAlgEquiv S U) := rfl

/-- Linear operator semantics of a lifted unitary morphism. -/
theorem toOperator_liftGateHom {S H : Qudit} (F : Operator S →⋆ₐ[ℂ] Operator H)
    (U : S ⟶ S) [DaggerCategory.IsUnitary U] : (liftGateHom F U).toOperator = F U.hom :=
  toOperator_liftGate F (.of U)

/-- Interpret a gate on a register as a linear operator on memory. -/
theorem toOperator_gate {S : Qudit} (r : Register H S) (U : End S)
    [DaggerCategory.IsUnitary U.asHom] :
    (gate r U).toOperator = endAlgEquiv H (r.liftEnd U) := rfl

/-- Linear operator semantics of a gate supplied as a morphism. -/
theorem toOperator_gateHom {S : Qudit} (r : Register H S) (U : S ⟶ S)
    [DaggerCategory.IsUnitary U] :
    (gateHom r U).toOperator = endAlgEquiv H (r.liftEnd (.of U)) :=
  toOperator_gate r (.of U)

/-- The first gate executed is the rightmost factor in the operator product. -/
theorem toOperator_sequence (ps : List (UnitaryProgram H)) :
    (sequence ps).toOperator = (ps.reverse.map toOperator).prod := by
  change endAlgEquiv H (sequence ps).denoteEnd = _
  rw [denoteEnd_sequence, map_list_prod, List.map_map]
  rfl

/-- Execute the gates with indices from zero up to the given bound, in increasing order. -/
noncomputable def gatePrefix (gate : ℕ → UnitaryProgram H) (m : ℕ) : UnitaryProgram H :=
  sequence ((List.range m).map gate)

/-- The empty prefix acts as the identity. -/
theorem toOperator_gatePrefix_zero (gate : ℕ → UnitaryProgram H) :
    (gatePrefix gate 0).toOperator = 1 := rfl

/-- The next gate acts on the output of the preceding prefix. -/
theorem toOperator_gatePrefix_succ (gate : ℕ → UnitaryProgram H) (m : ℕ) :
    (gatePrefix gate (m + 1)).toOperator =
      (gate m).toOperator * (gatePrefix gate m).toOperator := by
  simp [gatePrefix, toOperator_sequence, List.range_succ]

/-- A gate sequence transports a vector family from its first to its last member. -/
theorem toOperator_gatePrefix_apply (gate : ℕ → UnitaryProgram H) (m : ℕ) (v : ℕ → H.state)
    (step : ∀ k < m, (gate k).toOperator (v k) = v (k + 1)) :
    (gatePrefix gate m).toOperator (v 0) = v m := by
  induction m with
  | zero => rw [toOperator_gatePrefix_zero, one_apply_eq_self]
  | succ m ih =>
    rw [toOperator_gatePrefix_succ, mul_apply_eq_comp, ih (fun k hk => step k (by lia))]
    exact step m (by lia)

/-- Sequential execution composes the two channels in execution order. -/
theorem toChannel_seq (p q : UnitaryProgram H) :
    (p.seq q).toChannel = q.toChannel.comp p.toChannel :=
  QuantumChannel.ofIsometry_comp p.denoteHom q.denoteHom

/-- The channel acts on every operator by conjugation with the program's denotation. -/
theorem toSuperoperator_toChannel_apply (p : UnitaryProgram H) (A : End H) :
    p.toChannel.toSuperoperator (endAlgEquiv H A) =
      endAlgEquiv H (p.denoteEnd * A * star p.denoteEnd) := rfl

/-- On a pure input the output operator is the projector onto the evolved vector. -/
theorem op_map_pure (p : UnitaryProgram H) (v : UnitState H) :
    (p.toChannel.map (Density.pure v)).op = Operator.outer (p.denoteHom v) (p.denoteHom v) := by
  rw [toChannel, QuantumChannel.map_ofIsometry, Density.map_pure, Density.op_pure]
  rfl

end QuantumProgram.UnitaryProgram
