/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.PureComposite
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Schmidt decomposition

Schmidt vectors are obtained by contracting a bipartite vector against an eigenbasis of
its left marginal. Only positive eigenvalues are retained, so both Schmidt families are
orthonormal even for singular states and systems of different dimensions.

The nonzero spectra of the two marginals agree as multisets. The rectangular-matrix
proof adapts the characteristic-polynomial argument in physlib's
`QuantumInfo/Entropy/VonNeumann.lean`, revision `76e1b4f0171d27a0d35334a633263a40ecf24fd5`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Qudit.UnitState

noncomputable section

variable {H K : Qudit}

/-- Contract the left leg of a bipartite vector against a specified vector. -/
def contractLeft (ψ : UnitState (H ⊗ K)) (x : H.state) : K.state :=
  (TensorProduct.mk ℂ H.state K.state x).adjoint ψ.val

/-- Contraction is characterized by its inner products on the remaining subsystem. -/
lemma inner_contractLeft (ψ : UnitState (H ⊗ K)) (x : H.state) (y : K.state) :
    inner ℂ y (ψ.contractLeft x) = inner ℂ (x ⊗ₜ[ℂ] y) ψ.val :=
  LinearMap.adjoint_inner_right _ _ _

/-- Expansion of a bipartite vector along any left orthonormal basis. -/
lemma sum_tmul_contractLeft (ψ : UnitState (H ⊗ K)) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    ∑ i, b i ⊗ₜ[ℂ] ψ.contractLeft (b i) = ψ.val := by
  classical
  apply InnerProductSpace.ext_inner_left_basis
    (b.tensorProduct (stdOrthonormalBasis ℂ K.state)).toBasis
  rintro ⟨i, j⟩
  simp [inner_sum,
    TensorProduct.inner_tmul (𝕜 := ℂ) (E := H.state) (F := K.state),
    b.inner_eq_ite, inner_contractLeft]

/-- Inner products of contractions are matrix coefficients of the left marginal. -/
lemma inner_contractLeft_contractLeft (ψ : UnitState (H ⊗ K)) (x y : H.state) :
    inner ℂ (ψ.contractLeft x) (ψ.contractLeft y) =
      inner ℂ y ((Density.pure ψ).partialTraceRight.op x) := by
  let b := stdOrthonormalBasis ℂ K.state
  rw [Density.op_partialTraceRight, Operator.inner_partialTraceRight b,
    ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_contractLeft, ← inner_conj_symm (ψ.contractLeft x) (b i),
    inner_contractLeft, inner_conj_symm ψ.val (x ⊗ₜ[ℂ] b i)]
  simp [inner_smul_right]

/-- Contractions against marginal eigenvectors are orthogonal, with squared norm the eigenvalue. -/
lemma inner_contractLeft_eigenbasis (ψ : UnitState (H ⊗ K))
    (i j : Fin (Module.finrank ℂ H.state)) :
    inner ℂ (ψ.contractLeft ((Density.pure ψ).partialTraceRight.eigenbasis i))
      (ψ.contractLeft ((Density.pure ψ).partialTraceRight.eigenbasis j)) =
      if i = j then ((Density.pure ψ).partialTraceRight.eigenvalue i : ℂ) else 0 := by
  classical
  rw [inner_contractLeft_contractLeft, Density.apply_eigenbasis, inner_smul_right,
    OrthonormalBasis.inner_eq_ite]
  split_ifs with h h <;> simp_all

/-- The labels with strictly positive Schmidt coefficients. -/
abbrev SchmidtIndex (ψ : UnitState (H ⊗ K)) :=
  {i : Fin (Module.finrank ℂ H.state) // 0 < (Density.pure ψ).partialTraceRight.eigenvalue i}

/-- A strictly positive Schmidt coefficient, the square root of a marginal eigenvalue. -/
def schmidtCoefficient (ψ : UnitState (H ⊗ K)) (i : ψ.SchmidtIndex) : ℝ :=
  Real.sqrt ((Density.pure ψ).partialTraceRight.eigenvalue i.val)

/-- A left Schmidt vector, taken from the left marginal's eigenbasis. -/
def schmidtLeft (ψ : UnitState (H ⊗ K)) (i : ψ.SchmidtIndex) : H.state :=
  (Density.pure ψ).partialTraceRight.eigenbasis i.val

/-- The normalized contraction giving the corresponding right Schmidt vector. -/
def schmidtRight (ψ : UnitState (H ⊗ K)) (i : ψ.SchmidtIndex) : K.state :=
  (ψ.schmidtCoefficient i : ℂ)⁻¹ • ψ.contractLeft (ψ.schmidtLeft i)

/-- All retained Schmidt coefficients are strictly positive. -/
lemma schmidtCoefficient_pos (ψ : UnitState (H ⊗ K)) (i : ψ.SchmidtIndex) :
    0 < ψ.schmidtCoefficient i := Real.sqrt_pos.mpr i.property

/-- Squared Schmidt coefficients are the positive eigenvalues of the left marginal. -/
lemma sq_schmidtCoefficient (ψ : UnitState (H ⊗ K)) (i : ψ.SchmidtIndex) :
    ψ.schmidtCoefficient i ^ 2 = (Density.pure ψ).partialTraceRight.eigenvalue i.val :=
  Real.sq_sqrt (le_of_lt i.property)

/-- The left Schmidt family is orthonormal. -/
lemma orthonormal_schmidtLeft (ψ : UnitState (H ⊗ K)) :
    Orthonormal ℂ ψ.schmidtLeft :=
  (Density.pure ψ).partialTraceRight.eigenbasis.orthonormal.comp _ Subtype.val_injective

/-- The right Schmidt family is orthonormal. -/
lemma orthonormal_schmidtRight (ψ : UnitState (H ⊗ K)) :
    Orthonormal ℂ ψ.schmidtRight := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [schmidtRight, schmidtLeft, inner_smul_left, inner_smul_right,
    inner_contractLeft_eigenbasis, map_inv₀, Complex.conj_ofReal]
  by_cases h : i = j
  · subst j
    have hc : (ψ.schmidtCoefficient i : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (ψ.schmidtCoefficient_pos i))
    have hs : ((Density.pure ψ).partialTraceRight.eigenvalue i.val : ℂ) =
        (ψ.schmidtCoefficient i : ℂ) ^ 2 := by
      exact_mod_cast (ψ.sq_schmidtCoefficient i).symm
    simp only [ite_true, hs]
    field_simp
  · have hv : i.val ≠ j.val := fun hij => h (Subtype.ext hij)
    simp [h, hv]

/-- A zero marginal eigenvalue contributes no contraction vector. -/
lemma contractLeft_eigenbasis_eq_zero (ψ : UnitState (H ⊗ K))
    (i : Fin (Module.finrank ℂ H.state))
    (hi : (Density.pure ψ).partialTraceRight.eigenvalue i = 0) :
    ψ.contractLeft ((Density.pure ψ).partialTraceRight.eigenbasis i) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_contractLeft_eigenbasis, ite_eq_left rfl, hi, Complex.ofReal_zero]

/-- Multiplying a right Schmidt vector by its coefficient recovers the contraction. -/
lemma schmidtCoefficient_smul_schmidtRight (ψ : UnitState (H ⊗ K))
    (i : ψ.SchmidtIndex) :
    (ψ.schmidtCoefficient i : ℂ) • ψ.schmidtRight i =
      ψ.contractLeft (ψ.schmidtLeft i) := by
  have hc : (ψ.schmidtCoefficient i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (ψ.schmidtCoefficient_pos i))
  simp [schmidtRight, smul_smul, hc]

/-- Schmidt decomposition of a bipartite unit vector, with no zero coefficients. -/
lemma schmidt_decomposition (ψ : UnitState (H ⊗ K)) :
    ψ.val = ∑ i : ψ.SchmidtIndex,
      (ψ.schmidtCoefficient i : ℂ) • (ψ.schmidtLeft i ⊗ₜ[ℂ] ψ.schmidtRight i) := by
  classical
  simp_rw [← TensorProduct.tmul_smul, schmidtCoefficient_smul_schmidtRight]
  simp only [schmidtLeft]
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun i => 0 < (Density.pure ψ).partialTraceRight.eigenvalue i)) (by simp)
    (fun i => (Density.pure ψ).partialTraceRight.eigenbasis i ⊗ₜ[ℂ]
      ψ.contractLeft ((Density.pure ψ).partialTraceRight.eigenbasis i)), Finset.sum_filter]
  rw [← ψ.sum_tmul_contractLeft (Density.pure ψ).partialTraceRight.eigenbasis]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · have hz : (Density.pure ψ).partialTraceRight.eigenvalue i = 0 :=
      le_antisymm (le_of_not_gt hi) ((Density.pure ψ).partialTraceRight.eigenvalue_nonneg i)
    rw [ψ.contractLeft_eigenbasis_eq_zero i hz, TensorProduct.tmul_zero]

/-- The squared Schmidt coefficients form a probability distribution. -/
lemma sum_sq_schmidtCoefficient (ψ : UnitState (H ⊗ K)) :
    ∑ i : ψ.SchmidtIndex, ψ.schmidtCoefficient i ^ 2 = 1 := by
  classical
  simp_rw [sq_schmidtCoefficient]
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun i => 0 < (Density.pure ψ).partialTraceRight.eigenvalue i)) (by simp), Finset.sum_filter]
  convert (Density.pure ψ).partialTraceRight.sum_eigenvalue using 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · exact (le_antisymm (le_of_not_gt hi)
      ((Density.pure ψ).partialTraceRight.eigenvalue_nonneg i)).symm

/-- A Schmidt decomposition indexed by `Fin r`, with positive coefficients and orthonormal
families on both sides. The coefficients have squared sum one. -/
theorem exists_schmidt_decomposition (ψ : UnitState (H ⊗ K)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → H.state) (v : Fin r → K.state),
      (∀ i, 0 < s i) ∧ Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      (∑ i, s i ^ 2 = 1) ∧ ψ.val = ∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i) := by
  classical
  let e := (Fintype.equivFin ψ.SchmidtIndex).symm
  refine ⟨_, ψ.schmidtCoefficient ∘ e, ψ.schmidtLeft ∘ e, ψ.schmidtRight ∘ e,
    fun i => ψ.schmidtCoefficient_pos (e i),
    ψ.orthonormal_schmidtLeft.comp e e.injective,
    ψ.orthonormal_schmidtRight.comp e e.injective, ?_, ?_⟩
  · dsimp only [Function.comp_apply]
    rw [e.sum_comp (fun i => ψ.schmidtCoefficient i ^ 2)]
    exact ψ.sum_sq_schmidtCoefficient
  · dsimp only [Function.comp_apply]
    rw [e.sum_comp (fun i => (ψ.schmidtCoefficient i : ℂ) •
      (ψ.schmidtLeft i ⊗ₜ[ℂ] ψ.schmidtRight i))]
    exact ψ.schmidt_decomposition

end

end Qudit.UnitState

namespace Qudit

noncomputable section

variable {H K : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The rectangular coefficient matrix of a bipartite pure state in local orthonormal bases. -/
def UnitState.coefficientMatrix (ψ : UnitState (H ⊗ K))
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ K.state) : Matrix ι κ ℂ :=
  fun i j => inner ℂ (b i ⊗ₜ[ℂ] c j) ψ.val

/-- The left marginal is the coefficient matrix times its conjugate transpose. -/
lemma Density.toMatrix_partialTraceRight_pure [DecidableEq ι] (ψ : UnitState (H ⊗ K))
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ K.state) :
    (pure ψ).partialTraceRight.toMatrix b =
      ψ.coefficientMatrix b c * (ψ.coefficientMatrix b c).conjTranspose := by
  classical
  ext i j
  rw [Density.toMatrix, LinearMap.toMatrixOrthonormal_apply_apply,
    op_partialTraceRight, Operator.inner_partialTraceRight c]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, UnitState.coefficientMatrix,
    pure_apply, inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [← starRingEnd_apply, inner_conj_symm ψ.val (b j ⊗ₜ[ℂ] c k)]
  exact mul_comm _ _

/-- The right marginal is the transpose of the reverse coefficient Gram matrix. -/
lemma Density.toMatrix_partialTraceLeft_pure [DecidableEq κ] (ψ : UnitState (H ⊗ K))
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ K.state) :
    (pure ψ).partialTraceLeft.toMatrix c =
      ((ψ.coefficientMatrix b c).conjTranspose * ψ.coefficientMatrix b c).transpose := by
  classical
  ext i j
  rw [Density.toMatrix, LinearMap.toMatrixOrthonormal_apply_apply,
    op_partialTraceLeft, Operator.inner_partialTraceLeft b]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    UnitState.coefficientMatrix, pure_apply, inner_smul_right]
  apply Finset.sum_congr rfl
  intro k _
  rw [← starRingEnd_apply, inner_conj_symm ψ.val (b k ⊗ₜ[ℂ] c j)]

private lemma nonzero_roots_mul_comm [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    (A * B).charpoly.roots.filter (· ≠ 0) = (B * A).charpoly.roots.filter (· ≠ 0) := by
  have h := congrArg (fun p : Polynomial ℂ => p.roots.filter (· ≠ 0))
    (A.charpoly_mul_comm' B)
  simpa [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero,
    Multiset.filter_nsmul, Multiset.filter_singleton] using h

/-- The two marginals of a pure state have identical nonzero spectra, including multiplicities.
Their zero eigenvalues can have different multiplicities when the subsystem dimensions differ. -/
lemma Density.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft
    (ψ : UnitState (H ⊗ K)) :
    (pure ψ).partialTraceRight.nonzeroEigenvalues =
      (pure ψ).partialTraceLeft.nonzeroEigenvalues := by
  classical
  apply Multiset.map_injective Complex.ofReal_injective
  rw [← roots_charpoly_filter_ne_zero, ← roots_charpoly_filter_ne_zero]
  let b := stdOrthonormalBasis ℂ H.state
  let c := stdOrthonormalBasis ℂ K.state
  have hr : ((pure ψ).partialTraceRight.toMatrix b).charpoly =
      (pure ψ).partialTraceRight.op.charpoly :=
    LinearMap.charpoly_toMatrix _ b.toBasis
  have hl : ((pure ψ).partialTraceLeft.toMatrix c).charpoly =
      (pure ψ).partialTraceLeft.op.charpoly :=
    LinearMap.charpoly_toMatrix _ c.toBasis
  rw [← hr, ← hl, toMatrix_partialTraceRight_pure ψ b c,
    toMatrix_partialTraceLeft_pure ψ b c, Matrix.charpoly_transpose]
  exact nonzero_roots_mul_comm _ _

/-- The marginal nonzero spectra agree for any density operator known to be pure. -/
lemma Density.IsPure.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft
    {ρ : Density (H ⊗ K)} (hρ : ρ.IsPure) :
    ρ.partialTraceRight.nonzeroEigenvalues = ρ.partialTraceLeft.nonzeroEigenvalues := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact Density.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft ψ

end

end Qudit
