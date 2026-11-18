/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.BellPreparation
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

local notation "SingleOp" => Qubit.state →L[ℂ] Qubit.state
local notation "PairOp" => Qudit.state (Qubit ⊗ Qubit) →L[ℂ] Qudit.state (Qubit ⊗ Qubit)

/-- A Hermitian two-by-two matrix induces a self-adjoint qubit operator. -/
theorem isSelfAdjoint_of_hermitian_qubit_matrix (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M.conjTranspose = M) :
    IsSelfAdjoint (matrixToEnd M).asHom.hom.toContinuousLinearMap := by
  change (matrixToEnd M).asHom.hom.adjoint.toContinuousLinearMap = _
  rw [← Qudit.hom_dagger, dagger_matrixToEnd, hM]

/-- Pauli X as a self-adjoint single-qubit Hamiltonian. -/
def pauliXHamiltonian : selfAdjoint SingleOp :=
  ⟨Qubit.pauliX.asHom.hom.toContinuousLinearMap, isSelfAdjoint_of_hermitian_qubit_matrix _ (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply])⟩

/-- Pauli Z as a self-adjoint single-qubit Hamiltonian. -/
def pauliZHamiltonian : selfAdjoint SingleOp :=
  ⟨Qubit.pauliZ.asHom.hom.toContinuousLinearMap, isSelfAdjoint_of_hermitian_qubit_matrix _ (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply])⟩

/-- The rotation `exp(-i θ X/2)` on one qubit. -/
def rx (θ : ℝ) : Qubit ⟶ Qubit :=
  (hamiltonianGate (S := Qubit) pauliXHamiltonian (θ / 2)).denoteHom

instance (θ : ℝ) : IsUnitary (rx θ) := by unfold rx; infer_instance

/-- The rotation `exp(-i θ Z/2)` on one qubit. -/
def rz (θ : ℝ) : Qubit ⟶ Qubit :=
  (hamiltonianGate (S := Qubit) pauliZHamiltonian (θ / 2)).denoteHom

instance (θ : ℝ) : IsUnitary (rz θ) := by unfold rz; infer_instance

namespace TransverseFieldIsing

open scoped TensorProduct in
local instance : CompleteSpace (Qubit.state ⊗[ℂ] Qubit.state) := FiniteDimensional.complete ℂ _

/-- Transverse field on the left qubit. -/
def xLeft : selfAdjoint PairOp :=
  ⟨pauliXHamiltonian.val.rTensor Qubit.state, by
    exact (ContinuousLinearMap.adjoint_rTensor Qubit.state pauliXHamiltonian.val).trans
      (congrArg (fun A : SingleOp => A.rTensor Qubit.state) pauliXHamiltonian.prop)⟩

/-- Transverse field on the right qubit. -/
def xRight : selfAdjoint PairOp :=
  ⟨pauliXHamiltonian.val.lTensor Qubit.state, by
    exact (ContinuousLinearMap.adjoint_lTensor Qubit.state pauliXHamiltonian.val).trans
      (congrArg (fun A : SingleOp => A.lTensor Qubit.state) pauliXHamiltonian.prop)⟩

/-- The longitudinal interaction is the tensor product of the two Pauli Z operators. -/
def zz : selfAdjoint PairOp :=
  ⟨TensorProduct.mapL pauliZHamiltonian.val pauliZHamiltonian.val, by
    exact (TensorProduct.adjoint_mapL pauliZHamiltonian.val pauliZHamiltonian.val).trans
      (congrArg₂ TensorProduct.mapL pauliZHamiltonian.prop pauliZHamiltonian.prop)⟩

/-- The three terms in gate execution order, with independent real field strengths. -/
def terms (a b J : ℝ) : Fin 3 → selfAdjoint PairOp :=
  ![a • xLeft, b • xRight, J • zz]

/-- One physical slice, with the left qubit controlling both CNOT gates. -/
def step (a b J δ : ℝ) : UnitaryProgram (Qubit ⊗ Qubit) :=
  .sequence [.gateHom (.left .whole) (rx (2 * a * δ)), .gateHom (.right .whole) (rx (2 * b * δ)),
    .gateHom .whole controlledNot, .gateHom (.right .whole) (rz (2 * J * δ)),
    .gateHom .whole controlledNot]

private def liftLeft : SingleOp →ₐ[ℂ] PairOp :=
  AlgHom.ofLinearMap
    { toFun := fun A => A.rTensor Qubit.state
      map_add' := ContinuousLinearMap.rTensor_add _
      map_smul' := fun c A => ContinuousLinearMap.rTensor_smul _ c A }
    (ContinuousLinearMap.rTensor_one _) (ContinuousLinearMap.rTensor_mul _)

private def liftRight : SingleOp →ₐ[ℂ] PairOp :=
  AlgHom.ofLinearMap
    { toFun := fun A => A.lTensor Qubit.state
      map_add' := ContinuousLinearMap.lTensor_add _
      map_smul' := fun c A => ContinuousLinearMap.lTensor_smul _ c A }
    (ContinuousLinearMap.lTensor_one _) (ContinuousLinearMap.lTensor_mul _)

private theorem liftLeft_apply (A : SingleOp) : liftLeft A = A.rTensor Qubit.state := rfl

private theorem liftRight_apply (A : SingleOp) : liftRight A = A.lTensor Qubit.state := rfl

private abbrev cnotOp : PairOp := controlledNot.hom.toContinuousLinearMap

open scoped TensorProduct in
private theorem cnot_sq : cnotOp * cnotOp = 1 := by
  apply ContinuousLinearMap.coe_injective
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨i, j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    ContinuousLinearMap.coe_coe, mul_apply_eq_comp, one_apply_eq_self]
  simp only [cnotOp, LinearMap.coe_toContinuousLinearMap']
  rw [controlledNot_basis, controlledNot_basis]
  have h : i + (i + j) = j := by lia
  rw [h]

private theorem pauliZ_zero : pauliZHamiltonian.val (ZBasis 2 0) = ZBasis 2 0 := by
  change (matrixToEnd _).asHom (ZBasis 2 0) = _
  rw [matrixToEnd_apply_basis, Fin.sum_univ_two]
  simp

private theorem pauliZ_one : pauliZHamiltonian.val (ZBasis 2 1) = -ZBasis 2 1 := by
  change (matrixToEnd _).asHom (ZBasis 2 1) = _
  rw [matrixToEnd_apply_basis, Fin.sum_univ_two]
  simp

open scoped TensorProduct in
private theorem cnot_z : SemiconjBy cnotOp (liftRight pauliZHamiltonian.val) zz.val := by
  apply ContinuousLinearMap.coe_injective
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨i, j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    ContinuousLinearMap.coe_coe, mul_apply_eq_comp]
  change controlledNot.hom (ZBasis 2 i ⊗ₜ[ℂ] pauliZHamiltonian.val (ZBasis 2 j)) =
    TensorProduct.mapL pauliZHamiltonian.val pauliZHamiltonian.val
      (controlledNot.hom (ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 j))
  rw [controlledNot_basis, TensorProduct.mapL_tmul]
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ_zero, pauliZ_one, TensorProduct.tmul_neg, TensorProduct.neg_tmul,
      controlledNot_basis]

private theorem lift_evolution (L : SingleOp →ₐ[ℂ] PairOp) (P : selfAdjoint SingleOp)
    (c δ : ℝ) :
    L (LinearMap.toContinuousLinearMap
      (hamiltonianGate (S := Qubit) P (2 * c * δ / 2)).toOperator) =
      exp (((-Complex.I) * (δ : ℂ) * (c : ℂ)) • L P.val) := by
  let : NormedAlgebra ℚ SingleOp := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℚ PairOp := .restrictScalars ℚ ℂ _
  change L (exp ((2 * c * δ / 2) • ((-Complex.I) • P.val))) = _
  rw [map_exp L L.toLinearMap.continuous_of_finiteDimensional, ← Complex.coe_smul, smul_smul,
    map_smul]
  congr 2
  push_cast
  ring

private theorem term_evolution (P : selfAdjoint PairOp) (c δ : ℝ) :
    LinearMap.toContinuousLinearMap (hamiltonianGate (S := Qubit ⊗ Qubit) (c • P) δ).toOperator =
      exp (((-Complex.I) * (δ : ℂ) * (c : ℂ)) • P.val) := by
  change exp (δ • ((-Complex.I) • (c • P.val))) = _
  simp only [← Complex.coe_smul, smul_smul]
  rw [mul_left_comm, mul_assoc]

/-- The five gates implement one ordered Trotter step exactly as an amplitude operator. -/
theorem toOperator_step (a b J δ : ℝ) :
    (step a b J δ).toOperator =
      (trotterStep (S := Qubit ⊗ Qubit) (terms a b J) δ).toOperator := by
  apply LinearMap.toContinuousLinearMap.injective
  let k (c : ℝ) := (-Complex.I) * (δ : ℂ) * (c : ℂ)
  have hleft := lift_evolution liftLeft pauliXHamiltonian a δ
  have hright := lift_evolution liftRight pauliXHamiltonian b δ
  have hz := lift_evolution liftRight pauliZHamiltonian J δ
  let : NormedAlgebra ℚ PairOp := .restrictScalars ℚ ℂ _
  have hzz : cnotOp * exp (k J • liftRight pauliZHamiltonian.val) * cnotOp =
      exp (k J • zz.val) := by
    rw [((cnot_z.smul_right (k J)).exp_right).eq, mul_assoc, cnot_sq, mul_one]
  simp only [liftLeft_apply, liftRight_apply, UnitaryProgram.toOperator,
    UnitaryProgram.denoteEnd] at hleft hright hz hzz
  have hlist : List.finRange 3 = [0, 1, 2] := by decide
  simp only [step, trotterStep, hlist, List.map_cons, List.map_nil,
    UnitaryProgram.toContinuousLinearMap_toOperator_sequence, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one, rx, rz,
    UnitaryProgram.toOperator_gateHom, Register.toContinuousLinearMap_liftEnd_left,
    Register.toContinuousLinearMap_liftEnd_right, Register.liftEnd_whole]
  rw [hleft, hright, hz]
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
    ‖LinearMap.toContinuousLinearMap (simulation a b J t ε).toOperator -
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
