/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.Schmidt
import FQFP.CQM.Qudit.State.Purification
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Schmidt decomposition and marginal spectra regressions

These clients check unequal dimensions, repeated eigenvalues, the complex conjugation
convention of the right marginal, and compatibility with purification.
-/

open CategoryTheory MonoidalCategory Qudit
open scoped TensorProduct

noncomputable section

-- No equality between subsystem dimensions is needed, and the vectors are normalized.
example (ψ : UnitState (std 3 ⊗ Qubit)) :
    ∃ (r : ℕ) (s : Fin r → ℝ) (u : Fin r → (std 3).state) (v : Fin r → Qubit.state),
      (∀ i, 0 < s i) ∧ Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      (∑ i, s i ^ 2 = 1) ∧ ψ.val = ∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i) :=
  ψ.exists_schmidt_decomposition

-- The common nonzero spectrum preserves multiplicities after swapping the systems.
example (ψ : UnitState (Qubit ⊗ std 3)) :
    (Density.pure ψ.swap).partialTraceRight.nonzeroEigenvalues =
      (Density.pure ψ).partialTraceRight.nonzeroEigenvalues := by
  rw [Density.partialTraceRight_pure_swap]
  exact (Density.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft ψ).symm

-- A purification's environment has exactly the original state's nonzero eigenvalues.
example {H : Qudit} (ρ : Density H) :
    (Density.pure ρ.purify).partialTraceLeft.nonzeroEigenvalues = ρ.nonzeroEigenvalues := by
  rw [← Density.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft,
    ρ.partialTraceRight_pure_purify]

-- Repeated positive eigenvalues survive: the Bell marginal has two copies of 1/2.
example : bellDensity.partialTraceRight.nonzeroEigenvalues = {1 / 2, 1 / 2} := by
  classical
  have he (i : Fin (Module.finrank ℂ Qubit.state)) :
      bellDensity.partialTraceRight.eigenvalue i = 1 / 2 := by
    have h := bellDensity.partialTraceRight.apply_eigenbasis i
    rw [bellDensity_partialTraceRight_op] at h
    have hi := congrArg
      (inner ℂ (bellDensity.partialTraceRight.eigenbasis i)) h
    simp only [LinearMap.smul_apply, Module.End.one_apply, inner_smul_right,
      OrthonormalBasis.inner_eq_ite, ite_true, mul_one] at hi
    have hre := congrArg Complex.re hi
    norm_num at hre
    exact hre.symm
  simp [Density.nonzeroEigenvalues, he, Qubit, Multiset.filter_singleton]

private def phaseQubit : UnitState Qubit :=
  ⟨bellFactor • (ZBasis 2 0 + Complex.I • ZBasis 2 1), by
    change inner ℂ _ _ = 1
    simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      (ZBasis 2).inner_eq_ite, conj_bellFactor, Complex.conj_I]
    norm_num
    linear_combination (norm := ring_nf) 2 * bellFactor_mul_self
    simp [Complex.I_sq]⟩

private def rectangularState : UnitState (std 3 ⊗ Qubit) :=
  (UnitState.ofBasis (ZBasis 3) 0).tensor phaseQubit

-- The transpose in the right Gram-matrix formula is essential for this imaginary entry.
example : (Density.pure rectangularState).partialTraceLeft.toMatrix (ZBasis 2) 0 1 =
    -Complex.I / 2 := by
  rw [Density.toMatrix_partialTraceLeft_pure rectangularState (ZBasis 3) (ZBasis 2)]
  simp only [Matrix.transpose_apply]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, UnitState.coefficientMatrix,
    rectangularState, phaseQubit, TensorProduct.inner_tmul, inner_smul_right,
    inner_add_right, Fin.sum_univ_succ, ← starRingEnd_apply, conj_bellFactor,
    ← mul_assoc]
  linear_combination -Complex.I * bellFactor_mul_self

-- In a rectangular product state the two full spectra have different lengths.
example :
    (Finset.univ.val.map (Density.pure rectangularState).partialTraceRight.eigenvalue).card ≠
      (Finset.univ.val.map (Density.pure rectangularState).partialTraceLeft.eigenvalue).card := by
  simp [Qubit]

-- Nevertheless their nonzero spectra agree, also through the density-level purity API.
example : (Density.pure rectangularState).partialTraceRight.nonzeroEigenvalues =
    (Density.pure rectangularState).partialTraceLeft.nonzeroEigenvalues :=
  (Density.isPure_pure rectangularState).nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft

end
