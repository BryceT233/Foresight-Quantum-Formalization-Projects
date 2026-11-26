/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the transverse-field Ising slice and its ordered product specification.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/TFIM.lean
Qhl/Examples/TrotterTFIMTriple.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.IsingChain.Instruction

/-!
# Two-qubit transverse-field Ising simulation

For the signed Hamiltonian `a X⊗I + b I⊗X + J Z⊗Z`, one slice executes two local
X rotations followed by a parity computation, a local Z rotation and parity uncomputation.
The two-site native circuit and its Hoare command use the same instructions. Their
specification uses the ordered Trotter product with the half-angle convention for rotations.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit NormedSpace

namespace QuantumProgram

noncomputable section

/-- A Hermitian two-by-two matrix induces a self-adjoint qubit operator. -/
theorem isSelfAdjoint_of_hermitian_qubit_matrix (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.conjTranspose = M) :
    _root_.IsSelfAdjoint (matrixToEnd M).asHom.hom :=
  isSelfAdjoint_hom ((isSelfAdjoint_matrixToEnd_iff M).2 hM)

namespace TransverseFieldIsing

/-- Transverse field on the left qubit. -/
def xLeft : selfAdjoint (Operator (Qubit ⊗ Qubit)) :=
  ⟨_, pauliXHamiltonian.prop.map (Operator.tensorOneHom Qubit Qubit)⟩

/-- Transverse field on the right qubit. -/
def xRight : selfAdjoint (Operator (Qubit ⊗ Qubit)) :=
  ⟨_, pauliXHamiltonian.prop.map (Operator.oneTensorHom Qubit Qubit)⟩

/-- The longitudinal interaction is the tensor product of the two Pauli Z operators. -/
def zz : selfAdjoint (Operator (Qubit ⊗ Qubit)) :=
  ⟨Operator.tensor pauliZHamiltonian.val pauliZHamiltonian.val, by
    change (TensorProduct.map pauliZHamiltonian.val pauliZHamiltonian.val).adjoint = _
    rw [TensorProduct.adjoint_map]
    rw [← LinearMap.star_eq_adjoint, pauliZHamiltonian.prop.star_eq]
    rfl⟩

/-- The three terms in gate execution order, with independent real field strengths. -/
def terms (a b J : ℝ) : Fin 3 → selfAdjoint (Operator (Qubit ⊗ Qubit)) :=
  ![a • xLeft, b • xRight, J • zz]

/-- One physical slice, with the left qubit controlling both CNOT gates. -/
def step (a b J δ : ℝ) : UnitaryProgram (Qubit ⊗ Qubit) :=
  .sequence [.gate (.left .whole) (rx (2 * a * δ)), .gate (.right .whole) (rx (2 * b * δ)),
    .gateHom .whole Qubit.CNOT, .gate (.right .whole) (rz (2 * J * δ)), .gateHom .whole Qubit.CNOT]

private abbrev cnotOp : Operator (Qubit ⊗ Qubit) := Qubit.CNOT.hom

open scoped TensorProduct in
private theorem cnot_sq : cnotOp * cnotOp = 1 := by
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨i, j⟩
  change Qubit.CNOT.hom (Qubit.CNOT.hom _) = _
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  rw [Qubit.CNOT_basis, Qubit.CNOT_basis]
  have h : i + (i + j) = j := by lia
  rw [h]
  rfl

private theorem pauliZ_zero : pauliZHamiltonian.val (ZBasis 2 0) = ZBasis 2 0 := by
  change (matrixToEnd _).asHom (ZBasis 2 0) = _
  rw [matrixToEnd_apply_basis, Fin.sum_univ_two]
  simp

private theorem pauliZ_one : pauliZHamiltonian.val (ZBasis 2 1) = -ZBasis 2 1 := by
  change (matrixToEnd _).asHom (ZBasis 2 1) = _
  rw [matrixToEnd_apply_basis, Fin.sum_univ_two]
  simp

open scoped TensorProduct in
private theorem cnot_z :
    SemiconjBy cnotOp (Operator.oneTensorHom Qubit Qubit pauliZHamiltonian.val) zz.val := by
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨i, j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    mul_apply_eq_comp, Operator.oneTensorHom_apply]
  change Qubit.CNOT.hom _ = Operator.tensor pauliZHamiltonian.val pauliZHamiltonian.val
    (Qubit.CNOT.hom _)
  rw [Qubit.CNOT_basis, Operator.tensor_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ_zero, pauliZ_one, TensorProduct.tmul_neg, TensorProduct.neg_tmul,
      Qubit.CNOT_basis]

private theorem lift_evolution (L : Operator Qubit →⋆ₐ[ℂ] Operator (Qubit ⊗ Qubit))
    (P : selfAdjoint (Operator Qubit)) (c δ : ℝ) :
    L (hamiltonianGate (S := Qubit) P (2 * c * δ / 2)).toOperator =
      exp (((-Complex.I) * (δ : ℂ) * (c : ℂ)) • L P.val) := by
  let : NormedAlgebra ℚ (Operator Qubit) := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ (Operator (Qubit ⊗ Qubit)) := .restrictScalars ℚ ℂ _
  change L (exp ((2 * c * δ / 2) • ((-Complex.I) • P.val))) = _
  rw [map_exp L L.toAlgHom.toLinearMap.continuous_of_finiteDimensional, ← Complex.coe_smul,
    smul_smul, map_smul]
  congr 2
  push_cast
  ring

private theorem term_evolution (P : selfAdjoint (Operator (Qubit ⊗ Qubit))) (c δ : ℝ) :
    (hamiltonianGate (S := Qubit ⊗ Qubit) (c • P) δ).toOperator =
      exp (((-Complex.I) * (δ : ℂ) * (c : ℂ)) • P.val) := by
  change exp (δ • ((-Complex.I) • (c • P.val))) = _
  simp only [← Complex.coe_smul, smul_smul]
  rw [mul_left_comm, mul_assoc]

/-- Computing parity, rotating its target, and uncomputing implements the ZZ exponential. -/
theorem controlledNot_rz_controlledNot (c δ : ℝ) :
    Qubit.CNOT.hom * Operator.oneTensorHom Qubit Qubit (endAlgEquiv Qubit (rz (2 * c * δ))) *
        Qubit.CNOT.hom =
      exp (((-Complex.I) * (δ : ℂ) * (c : ℂ)) • zz.val) := by
  let k := (-Complex.I) * (δ : ℂ) * (c : ℂ)
  let : NormedAlgebra ℚ (Operator (Qubit ⊗ Qubit)) := .restrictScalars ℚ ℂ _
  change cnotOp * Operator.oneTensorHom Qubit Qubit
    ((hamiltonianGate (S := Qubit) pauliZHamiltonian (2 * c * δ / 2)).toOperator) * cnotOp = _
  rw [lift_evolution (Operator.oneTensorHom Qubit Qubit) pauliZHamiltonian c δ,
    ((cnot_z.smul_right k).exp_right).eq, mul_assoc, cnot_sq, mul_one]

/-- The five gates implement one ordered Trotter step exactly as an amplitude operator. -/
theorem toOperator_step (a b J δ : ℝ) :
    (step a b J δ).toOperator =
      (trotterStep (S := Qubit ⊗ Qubit) (terms a b J) δ).toOperator := by
  have hleft := lift_evolution (Operator.tensorOneHom Qubit Qubit) pauliXHamiltonian a δ
  have hright := lift_evolution (Operator.oneTensorHom Qubit Qubit) pauliXHamiltonian b δ
  have hzz := controlledNot_rz_controlledNot J δ
  simp only [rz, endAlgEquiv_apply] at hzz
  simp only [UnitaryProgram.toOperator] at hleft hright
  have hlist : List.finRange 3 = [0, 1, 2] := by decide
  simp only [step, trotterStep, hlist, List.map_cons, List.map_nil,
    UnitaryProgram.toOperator_sequence, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, rx, rz,
    UnitaryProgram.toOperator_gate,
    Register.endAlgEquiv_liftEnd_left, Register.endAlgEquiv_liftEnd_right, Register.liftEnd_whole]
  rw [hleft, hright]
  simp only [endAlgEquiv_apply, terms, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [term_evolution zz J δ, term_evolution xRight b δ, term_evolution xLeft a δ,
    ← mul_assoc, ← mul_assoc, hzz]
  rfl

end TransverseFieldIsing

namespace IsingChain

/-- Two sites and one edge give the existing five-gate Ising slice. -/
theorem toOperator_slice_pair (a b J δ : ℝ) :
    (program (slice ![a, b] ![J] δ)).toOperator =
      (TransverseFieldIsing.step a b J δ).toOperator := by
  simp only [slice, fieldGates, interactionGates, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, edgeGates, program,
    TransverseFieldIsing.step, List.map_cons, List.map_nil, UnitaryProgram.toOperator_sequence]
  rfl

end IsingChain

namespace TransverseFieldIsing

/-- Repeat the physical slice at time `t/n` for `n` steps. -/
def circuit (a b J t : ℝ) (n : ℕ) : UnitaryProgram (Qubit ⊗ Qubit) :=
  IsingChain.program (IsingChain.circuit ![a, b] ![J] t n)

/-- The repeated circuit has the same operator as the generic product formula. -/
theorem toOperator_circuit (a b J t : ℝ) (n : ℕ) :
    (circuit a b J t n).toOperator =
      (trotterProgram (S := Qubit ⊗ Qubit) (terms a b J) t n).toOperator := by
  let δ := t / n
  have hs := (IsingChain.toOperator_slice_pair a b J δ).trans (toOperator_step a b J δ)
  refine (IsingChain.toOperator_replicate n _).trans
    ((congrArg (fun U : Operator (Qubit ⊗ Qubit) => U ^ n) hs).trans ?_)
  simp [trotterProgram, UnitaryProgram.toOperator_sequence, δ]

/-- Execute the two-site circuit as a sequence of native Hoare commands. -/
def circuitCommand {Store : Type*} (a b J t : ℝ) (n : ℕ) : Command Store (Fin 2) (Qubit ⊗ Qubit) :=
  IsingChain.command (IsingChain.circuit ![a, b] ![J] t n)

/-- For any postcondition, the Trotter channel gives the precondition of the native commands. -/
theorem derivTot_circuit {Store : Type*} (a b J t : ℝ) (n : ℕ)
    (A : Assertion Store (Qubit ⊗ Qubit)) :
    DerivTot (A.channelPre fun _ => (trotterProgram (terms a b J) t n).toChannel)
      (circuitCommand a b J t n) A := by
  have he : (circuit a b J t n).toChannel = (trotterProgram (terms a b J) t n).toChannel :=
    QuantumChannel.ext (congrArg (Superoperator.conjugate (H := Qubit ⊗ Qubit) (K := Qubit ⊗ Qubit))
      (toOperator_circuit a b J t n))
  rw [← he]
  exact IsingChain.derivTot_command (e := 1) _ A

/-- Compile the transverse-field Ising evolution to a circuit at the requested tolerance. -/
def simulation (a b J t ε : ℝ) : UnitaryProgram (Qubit ⊗ Qubit) :=
  circuit a b J t (trotterSteps (S := Qubit ⊗ Qubit) (terms a b J) t ε)

/-- The compiled circuit approximates the full Ising exponential in operator norm. -/
theorem simulation_error_le (a b J t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(simulation a b J t ε).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • (a • xLeft.val + b • xRight.val + J • zz.val))‖ ≤ ε := by
  rw [simulation, toOperator_circuit]
  have hsum : ∑ i, (terms a b J i).val = a • xLeft.val + b • xRight.val + J • zz.val := by
    rw [Fin.sum_univ_three]
    rfl
  simpa only [trotterSimulation, hsum] using
    trotterSimulation_error_le (S := Qubit ⊗ Qubit) (terms a b J) t hε

end TransverseFieldIsing

end

end QuantumProgram
