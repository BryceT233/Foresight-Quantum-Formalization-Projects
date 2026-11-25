/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Pure/Qubit.lean: S and T, single-qubit identities, controlled gates
and their block matrices, CNOT and conjugation on the control.

qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Gate/Phase.lean and Qhl/Gate/ControlledU.lean: phase shifts and coherent control.
Qhl/Examples/BellStateTriple.lean: CNOT as a computational basis permutation.
Copyright 2026 Qedia contributors.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite.Basic

/-!
# Qubit gate identities and coherent control

Products of endomorphisms act on the rightmost input first. In a controlled gate the
left tensor factor is the control. The target can be any finite-dimensional qudit.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory Complex
open scoped TensorProduct

namespace Qudit

/-- Computational-basis matrix of an endomorphism of a standard qudit. -/
def endToMatrix (n : ℕ) : End (std n) ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (endAlgEquiv _).trans (LinearMap.toMatrixAlgEquiv (ZBasis n).toBasis)

lemma endToMatrix_matrixToEnd {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    endToMatrix n (matrixToEnd M) = M :=
  (LinearMap.toMatrixAlgEquiv (ZBasis n).toBasis).apply_symm_apply M

namespace Qubit

/-- The Hadamard is its own adjoint. -/
theorem isSelfAdjoint_H : IsSelfAdjoint Qubit.H := by
  rw [Qubit.H, isSelfAdjoint_matrixToEnd_iff]
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

/-- Negating the phase angle gives the adjoint gate. -/
theorem phaseShift_neg (θ : ℝ) : (phaseShift (-θ)).asHom = (phaseShift θ).asHom† := by
  rw [phaseShift, phaseShift, dagger_matrixToEnd]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, ← Complex.exp_conj]

/-- The adjoint phase shift negates its angle. -/
theorem star_phaseShift (θ : ℝ) : star (phaseShift θ) = phaseShift (-θ) :=
  End.ext (phaseShift_neg θ).symm

instance (θ : ℝ) : IsUnitary (phaseShift θ).asHom := by
  rw [phaseShift, isUnitary_matrixToEnd_iff_fin_two]
  simp [norm_exp_ofReal_mul_I]

/-- The computational basis diagonalizes the phase shift. -/
theorem phaseShift_basis (θ : ℝ) (i : Fin 2) :
    (phaseShift θ).asHom (ZBasis 2 i) =
      (if i = 0 then 1 else exp (θ * I)) • ZBasis 2 i := by
  rw [phaseShift, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  fin_cases i <;> simp

/-- The quarter-turn phase gate, with diagonal entries one and `I`. -/
abbrev S : End Qubit := phaseShift (Real.pi / 2)

/-- The eighth-turn phase gate, with diagonal entries one and `(1 + I) / √2`. -/
abbrev T : End Qubit := phaseShift (Real.pi / 4)

theorem endToMatrix_S : endToMatrix 2 S = !![1, 0; 0, I] := by
  simp [S, phaseShift, endToMatrix_matrixToEnd, exp_pi_div_two_mul_I]

/-- The eighth root of unity acting on the excited state of the T gate. -/
theorem exp_pi_div_four_mul_I :
    exp (((Real.pi / 4 : ℝ) : ℂ) * I) = (1 + I) / (Real.sqrt 2 : ℂ) := by
  rw [exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  field_simp
  have h : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; norm_num
  linear_combination (1 + I) * h

theorem endToMatrix_T : endToMatrix 2 T = !![1, 0; 0, (1 + I) / (Real.sqrt 2 : ℂ)] := by
  rw [T, phaseShift, endToMatrix_matrixToEnd, exp_pi_div_four_mul_I]

/-- Multiplication of phase gates adds their phase angles. -/
theorem phaseShift_mul (a b : ℝ) : phaseShift a * phaseShift b = phaseShift (a + b) := by
  apply (endToMatrix 2).injective
  simp [phaseShift, endToMatrix_matrixToEnd, add_mul, exp_add]

theorem phaseShift_pi : phaseShift Real.pi = pauliZ := by
  simp [phaseShift, pauliZ]

private theorem mul_self_of_selfAdjoint_unitary {J : Qudit} {U : End J}
    (hU : IsSelfAdjoint U) [IsUnitary U.asHom] : U * U = 1 := by
  simpa only [hU.star_eq] using
    Unitary.star_mul_self_of_mem ((End.mem_unitary_iff U).2 inferInstance)

theorem pauliX_mul_self : pauliX * pauliX = 1 :=
  mul_self_of_selfAdjoint_unitary isSelfAdjoint_pauliX

theorem pauliY_mul_self : pauliY * pauliY = 1 :=
  mul_self_of_selfAdjoint_unitary isSelfAdjoint_pauliY

theorem pauliZ_mul_self : pauliZ * pauliZ = 1 :=
  mul_self_of_selfAdjoint_unitary isSelfAdjoint_pauliZ

theorem H_mul_self : H * H = 1 := mul_self_of_selfAdjoint_unitary isSelfAdjoint_H

theorem S_mul_self : S * S = pauliZ := by
  rw [S, phaseShift_mul, add_halves, phaseShift_pi]

theorem T_mul_self : T * T = S := by
  rw [T, phaseShift_mul, S]
  congr 1
  ring

theorem pauliX_mul_pauliY : pauliX * pauliY = -(pauliY * pauliX) := by
  apply (endToMatrix 2).injective
  simp [pauliX, pauliY, endToMatrix_matrixToEnd]

theorem pauliZ_mul_pauliY : pauliZ * pauliY = -(pauliY * pauliZ) := by
  apply (endToMatrix 2).injective
  simp [pauliZ, pauliY, endToMatrix_matrixToEnd]

theorem pauliZ_mul_pauliX : pauliZ * pauliX = -(pauliX * pauliZ) := by
  apply (endToMatrix 2).injective
  simp [pauliZ, pauliX, endToMatrix_matrixToEnd]

theorem H_mul_pauliX : H * pauliX = pauliZ * H := by
  apply (endToMatrix 2).injective
  simp [H, pauliX, pauliZ, endToMatrix_matrixToEnd]

theorem H_mul_pauliZ : H * pauliZ = pauliX * H := by
  apply (endToMatrix 2).injective
  simp [H, pauliZ, pauliX, endToMatrix_matrixToEnd]

theorem phaseShift_commute (a b : ℝ) : Commute (phaseShift a) (phaseShift b) := by
  rw [Commute, SemiconjBy, phaseShift_mul, phaseShift_mul, add_comm]

theorem pauliZ_commute_S : Commute pauliZ S :=
  phaseShift_pi ▸ phaseShift_commute Real.pi (Real.pi / 2)

theorem pauliZ_commute_T : Commute pauliZ T :=
  phaseShift_pi ▸ phaseShift_commute Real.pi (Real.pi / 4)

theorem S_commute_T : Commute S T := phaseShift_commute _ _

variable {H : Qudit}

/-- Coherent control of a linear operator on an arbitrary target. -/
def controlledOp (T : Operator H) : Operator (Qubit ⊗ H) :=
  Operator.tensor (Operator.outer (ZBasis 2 0) (ZBasis 2 0)) 1 +
    Operator.tensor (Operator.outer (ZBasis 2 1) (ZBasis 2 1)) T

/-- A basis control selects the identity or the target operator. -/
theorem controlledOp_basis (T : Operator H) (i : Fin 2) (w : H.state) :
    controlledOp T (ZBasis 2 i ⊗ₜ[ℂ] w) = ZBasis 2 i ⊗ₜ[ℂ] (if i = 0 then w else T w) := by
  fin_cases i <;> simp [controlledOp, Operator.outer_apply]

/-- Taking the adjoint commutes with coherent control. -/
theorem controlledOp_adjoint (T : Operator H) :
    (controlledOp T).adjoint = controlledOp T.adjoint := by
  unfold controlledOp Operator.tensor
  rw [map_add, TensorProduct.adjoint_map, TensorProduct.adjoint_map, LinearMap.adjoint_one,
    Operator.adjoint_outer, Operator.adjoint_outer]

/-- Gate on the joint memory controlled by the first qubit. -/
def controlled (V : H ⟶ H) : Qubit ⊗ H ⟶ Qubit ⊗ H := ofHom (controlledOp V.hom)

/-- Taking the adjoint commutes with coherent control of the target gate. -/
theorem controlled_dagger (V : H ⟶ H) : controlled V† = (controlled V)† :=
  hom_ext (controlledOp_adjoint V.hom).symm

/-- Action of a controlled gate on a computational basis control and any target vector. -/
theorem controlled_basis (V : H ⟶ H) (i : Fin 2) (w : H.state) :
    controlled V (ZBasis 2 i ⊗ₜ[ℂ] w) = ZBasis 2 i ⊗ₜ[ℂ] (if i = 0 then w else V w) :=
  controlledOp_basis V.hom i w

private lemma control_basis_ext {f g : Qubit ⊗ H ⟶ Qubit ⊗ H}
    (h : ∀ (i : Fin 2) (w : H.state), f (ZBasis 2 i ⊗ₜ[ℂ] w) = g (ZBasis 2 i ⊗ₜ[ℂ] w)) :
    f = g := by
  let b := stdOrthonormalBasis ℂ H.state
  apply hom_ext
  apply ((ZBasis 2).tensorProduct b).toBasis.ext
  rintro ⟨i, j⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  exact h i (b j)

theorem controlled_id : controlled (𝟙 H) = 𝟙 (Qubit ⊗ H) := by
  apply control_basis_ext
  intro i w
  simp [controlled_basis]

theorem controlled_comp (U V : H ⟶ H) : controlled U ≫ controlled V = controlled (U ≫ V) := by
  apply control_basis_ext
  intro i w
  simp only [comp_apply, controlled_basis]
  split <;> rfl

/-- Controlling a unitary and its adjoint in sequence gives the identity. -/
theorem controlled_comp_dagger (V : H ⟶ H) [IsUnitary V] :
    controlled V ≫ controlled V† = 𝟙 _ := by
  rw [controlled_comp, IsIsometry.comp_dagger_eq_id, controlled_id]

/-- Controlling the inverse followed by the gate also gives the identity. -/
theorem controlled_dagger_comp (V : H ⟶ H) [IsUnitary V] :
    controlled V† ≫ controlled V = 𝟙 _ := by
  rw [controlled_comp, IsUnitary.dagger_comp_eq_id, controlled_id]

instance (V : H ⟶ H) [IsUnitary V] : IsUnitary (controlled V) := by
  rw [isUnitary_iff, ← controlled_dagger]
  exact ⟨controlled_comp_dagger V, controlled_dagger_comp V⟩

/-- In any orthonormal target basis the controlled matrix has diagonal blocks `1` and `V`. -/
theorem toMatrix_controlled_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (V : H ⟶ H) (a c : Fin 2) (i j : ι) :
    LinearMap.toMatrixOrthonormal ((ZBasis 2).tensorProduct b) (controlled V).hom (a, i) (c, j) =
      if a = c then
        (if c = 0 then (1 : Matrix ι ι ℂ) i j else LinearMap.toMatrixOrthonormal b V.hom i j)
      else 0 := by
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, OrthonormalBasis.tensorProduct_apply]
  change inner ℂ _ (controlled V (ZBasis 2 c ⊗ₜ[ℂ] b j)) = _
  rw [controlled_basis, TensorProduct.inner_tmul]
  fin_cases a <;> fin_cases c <;> simp [(ZBasis 2).inner_eq_ite, b.inner_eq_ite, Matrix.one_apply]

theorem pauliX_basis (i : Fin 2) : pauliX.asHom (ZBasis 2 i) = ZBasis 2 (1 + i) := by
  rw [pauliX, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  fin_cases i <;> simp

/-- Conjugating by X on the control selects the opposite block. -/
theorem pauliX_controlled_pauliX (V : H ⟶ H) [IsUnitary V] :
    (pauliX.asHom ▷ H) ≫ controlled V ≫ (pauliX.asHom ▷ H) =
      controlled V† ≫ (Qubit ◁ V) := by
  apply control_basis_ext
  intro i w
  have hv : V (V.hom.adjoint w) = w :=
    LinearMap.congr_fun (congrArg Hom.hom (IsUnitary.dagger_comp_eq_id V)) w
  fin_cases i <;> simp [controlled_basis, pauliX_basis, hv]

/-- Controlled NOT permutes the computational basis by adding the control to the target mod two. -/
def CNOT : Qubit ⊗ Qubit ⟶ Qubit ⊗ Qubit :=
  let b := (ZBasis 2).tensorProduct (ZBasis 2)
  (isoMk (b.equiv b (Equiv.prodCongrRight fun a => Equiv.addLeft a)).toLinearEquiv).hom

instance : IsUnitary CNOT :=
  isUnitary_isoMk_coe_LIEquiv (H₁ := Qubit ⊗ Qubit) (H₂ := Qubit ⊗ Qubit) _

/-- Action of controlled NOT on every computational basis input, with the left qubit as control. -/
theorem CNOT_basis (a b : Fin 2) :
    CNOT.hom (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b) =
      ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 (a + b) := by
  let e := (ZBasis 2).tensorProduct (ZBasis 2)
  have h : CNOT.hom (e (a, b)) = e (a, a + b) :=
    e.equiv_apply_basis e (Equiv.prodCongrRight fun i => Equiv.addLeft i) (a, b)
  simpa only [e, OrthonormalBasis.tensorProduct_apply] using h

/-- CNOT is precisely coherent control of the Pauli X gate. -/
theorem CNOT_eq_controlled_pauliX : CNOT = controlled pauliX.asHom := by
  apply hom_ext
  apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
  rintro ⟨a, b⟩
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  change CNOT.hom (ZBasis 2 a ⊗ₜ[ℂ] ZBasis 2 b) = controlled pauliX.asHom _
  rw [CNOT_basis, controlled_basis]
  fin_cases a <;> simp [pauliX_basis]

/-- Matrix in computational basis order 00, 01, 10, 11, with the first qubit controlling. -/
theorem CNOT_matrix :
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrixOrthonormal ((ZBasis 2).tensorProduct (ZBasis 2)) CNOT.hom) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  let b := (ZBasis 2).tensorProduct (ZBasis 2)
  have entry (i j : Fin 2 × Fin 2) :
      LinearMap.toMatrixOrthonormal b CNOT.hom i j = if i = (j.1, j.1 + j.2) then 1 else 0 := by
    obtain ⟨a, c⟩ := j
    have act : CNOT.hom (b (a, c)) = b (a, a + c) := by
      simpa only [b, OrthonormalBasis.tensorProduct_apply] using CNOT_basis a c
    rw [LinearMap.toMatrixOrthonormal_apply_apply, act, b.inner_eq_ite]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [entry]
  fin_cases i <;> fin_cases j <;> rfl

end Qubit

end Qudit
