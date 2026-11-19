/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Examples.BellPreparation
public import FQFP.QuantumProgram.Trotter

/-!
# Two-qubit transverse-field Ising simulation

For the signed Hamiltonian `a X⊗I + b I⊗X + J Z⊗Z`, one slice executes two local
X rotations followed by a parity computation, a local Z rotation and parity uncomputation.
The semantics is equality on amplitudes with the half-angle convention for rotations.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit NormedSpace

namespace QuantumProgram

noncomputable section

/-- A Hermitian two-by-two matrix induces a self-adjoint qubit operator. -/
theorem isSelfAdjoint_of_hermitian_qubit_matrix (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.conjTranspose = M) :
    _root_.IsSelfAdjoint (matrixToEnd M).asHom.hom :=
  (isSelfAdjoint_iff_hom _).1 ((isSelfAdjoint_matrixToEnd_iff M).2 hM)

/-- Pauli X as a self-adjoint single-qubit Hamiltonian. -/
def pauliXHamiltonian : selfAdjoint (Operator Qubit) :=
  ⟨_, (isSelfAdjoint_iff_hom Qubit.pauliX.asHom).1 inferInstance⟩

/-- Pauli Z as a self-adjoint single-qubit Hamiltonian. -/
def pauliZHamiltonian : selfAdjoint (Operator Qubit) :=
  ⟨_, (isSelfAdjoint_iff_hom Qubit.pauliZ.asHom).1 inferInstance⟩

/-- The rotation `exp(-i θ X/2)` on one qubit. -/
def rx (θ : ℝ) : Qubit ⟶ Qubit :=
  (hamiltonianGate (S := Qubit) pauliXHamiltonian (θ / 2)).denoteHom

instance (θ : ℝ) : IsUnitary (rx θ) := by unfold rx; infer_instance

/-- The rotation `exp(-i θ Z/2)` on one qubit. -/
def rz (θ : ℝ) : Qubit ⟶ Qubit :=
  (hamiltonianGate (S := Qubit) pauliZHamiltonian (θ / 2)).denoteHom

instance (θ : ℝ) : IsUnitary (rz θ) := by unfold rz; infer_instance

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
  .sequence [.gateHom (.left .whole) (rx (2 * a * δ)), .gateHom (.right .whole) (rx (2 * b * δ)),
    .gateHom .whole controlledNot, .gateHom (.right .whole) (rz (2 * J * δ)),
    .gateHom .whole controlledNot]

private abbrev cnotOp : Operator (Qubit ⊗ Qubit) := controlledNot.hom

open scoped TensorProduct in
private theorem cnot_sq : cnotOp * cnotOp = 1 := by
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨i, j⟩
  change controlledNot.hom (controlledNot.hom _) = _
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  rw [controlledNot_basis, controlledNot_basis]
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
    Module.End.mul_apply, Operator.oneTensorHom_apply]
  change controlledNot.hom _ = Operator.tensor pauliZHamiltonian.val pauliZHamiltonian.val
    (controlledNot.hom _)
  rw [controlledNot_basis, Operator.tensor_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ_zero, pauliZ_one, TensorProduct.tmul_neg, TensorProduct.neg_tmul,
      controlledNot_basis]

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
    controlledNot.hom * Operator.oneTensorHom Qubit Qubit (rz (2 * c * δ)).hom * controlledNot.hom =
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
  simp only [rz] at hzz
  simp only [UnitaryProgram.toOperator, UnitaryProgram.denoteEnd] at hleft hright
  have hlist : List.finRange 3 = [0, 1, 2] := by decide
  simp only [step, trotterStep, hlist, List.map_cons, List.map_nil,
    UnitaryProgram.toOperator_sequence, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, rx, rz,
    UnitaryProgram.toOperator_gateHom, Register.endAlgEquiv_liftEnd_left,
    Register.endAlgEquiv_liftEnd_right, Register.liftEnd_whole]
  rw [hleft, hright]
  simp only [endAlgEquiv_apply, terms, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [term_evolution zz J δ, term_evolution xRight b δ, term_evolution xLeft a δ,
    ← mul_assoc, ← mul_assoc, hzz]
  rfl

/-- Repeat the physical slice at time `t/n` for `n` steps. -/
def circuit (a b J t : ℝ) (n : ℕ) : UnitaryProgram (Qubit ⊗ Qubit) :=
  .sequence (List.replicate n (step a b J (t / n)))

/-- The repeated circuit has the same operator as the generic product formula. -/
theorem toOperator_circuit (a b J t : ℝ) (n : ℕ) :
    (circuit a b J t n).toOperator =
      (trotterProgram (S := Qubit ⊗ Qubit) (terms a b J) t n).toOperator := by
  simp only [circuit, trotterProgram, UnitaryProgram.toOperator_sequence, List.reverse_replicate,
    List.map_replicate, List.prod_replicate, toOperator_step]

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
