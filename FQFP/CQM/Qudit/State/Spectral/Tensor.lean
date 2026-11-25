/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean: product spectra with multiplicities, the least spectral
value of a product, and invariance of the spectrum under relabeling and swap.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Spectral.Basic
import FQFP.Data.Fintype.Fibers
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Spectra under tensor products and unitary transport

The eigenvalues of a product state are the pairwise products of the local eigenvalues,
with multiplicities. A bijection matches these products to the ordered spectral labels.
-/

public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped Pointwise

namespace Qudit.Density

variable {H K : Qudit}

/-- The real spectrum of a density operator is the range of its eigenvalue list. -/
theorem realSpectrum_eq_range_eigenvalue (ρ : Density H) :
    _root_.spectrum ℝ ρ.op = Set.range ρ.eigenvalue := by
  ext x
  rw [← spectrum.algebraMap_mem_iff ℂ, Module.End.mem_spectrum_iff_isRoot_charpoly,
    ← Polynomial.mem_roots (LinearMap.charpoly_monic ρ.op).ne_zero,
    ρ.positive.isSymmetric.roots_charpoly_eq_eigenvalues rfl]
  simp [eigenvalue, Set.mem_range]

/-- Pairwise products and the ordered tensor-product eigenvalues agree with multiplicities. -/
theorem exists_equiv_eigenvalue_tensor (ρ : Density H) (σ : Density K) :
    ∃ e : (Fin (Module.finrank ℂ H.state) × Fin (Module.finrank ℂ K.state)) ≃
      Fin (Module.finrank ℂ (H ⊗ K).state), ∀ p,
        (ρ.tensor σ).eigenvalue (e p) = ρ.eigenvalue p.1 * σ.eigenvalue p.2 :=
  Fintype.exists_equiv_of_multiset_eq _ _ ((ρ.tensor σ).eigenvalues_eq_of_eigenbasis
    (ρ.eigenbasis.tensorProduct σ.eigenbasis) _ (ρ.tensor_apply_eigenbasis σ)).symm

/-- The real spectrum of a product state is the pointwise product of the two spectra. -/
theorem realSpectrum_tensor (ρ : Density H) (σ : Density K) :
    _root_.spectrum ℝ (ρ.tensor σ).op = _root_.spectrum ℝ ρ.op * _root_.spectrum ℝ σ.op := by
  obtain ⟨e, he⟩ := ρ.exists_equiv_eigenvalue_tensor σ
  simp only [realSpectrum_eq_range_eigenvalue]
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨p, rfl⟩ := e.surjective k
    exact ⟨_, ⟨p.1, rfl⟩, _, ⟨p.2, rfl⟩, (he p).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact ⟨e (i, j), he (i, j)⟩

/-- The least value of a density operator's spectrum is attained by an eigenvalue. -/
theorem exists_isLeast_eigenvalue (ρ : Density H) :
    ∃ i, IsLeast (_root_.spectrum ℝ ρ.op) (ρ.eigenvalue i) := by
  have := ρ.spectrum.nonempty
  obtain ⟨i, hi⟩ := Finite.exists_min ρ.eigenvalue
  exact ⟨i, ρ.realSpectrum_eq_range_eigenvalue ▸ ⟨⟨i, rfl⟩, Set.forall_mem_range.mpr hi⟩⟩

/-- The least spectral value is multiplicative, including for singular states. -/
theorem sInf_realSpectrum_tensor (ρ : Density H) (σ : Density K) :
    sInf (_root_.spectrum ℝ (ρ.tensor σ).op) =
      sInf (_root_.spectrum ℝ ρ.op) * sInf (_root_.spectrum ℝ σ.op) := by
  obtain ⟨i, hi⟩ := ρ.exists_isLeast_eigenvalue
  obtain ⟨j, hj⟩ := σ.exists_isLeast_eigenvalue
  rw [ρ.realSpectrum_tensor σ, hi.csInf_eq, hj.csInf_eq]
  apply IsLeast.csInf_eq
  refine ⟨Set.mul_mem_mul hi.1 hj.1, ?_⟩
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_le_mul (hi.2 ha) (hj.2 hb) (σ.eigenvalue_nonneg j)
    ((ρ.eigenvalue_nonneg i).trans (hi.2 ha))

/-- Unitary transport preserves the eigenvalue multiset, including the multiplicity of zero. -/
theorem eigenvalues_map_unitary (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    Finset.univ.val.map (ρ.map U).eigenvalue = Finset.univ.val.map ρ.eigenvalue := by
  apply (ρ.map U).eigenvalues_eq_of_eigenbasis (ρ.eigenbasis.map (LIEquivOfIsUnitary U))
  intro i
  change (ρ.map U).op (U.hom (ρ.eigenbasis i)) = (ρ.eigenvalue i : ℂ) • U.hom (ρ.eigenbasis i)
  rw [op_map_apply, ρ.apply_eigenbasis, map_smul]

/-- A unitary, in particular a swap, gives a value-preserving bijection of spectral labels. -/
theorem exists_equiv_eigenvalue_map_unitary (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    ∃ e : Fin (Module.finrank ℂ H.state) ≃ Fin (Module.finrank ℂ K.state),
      ∀ i, (ρ.map U).eigenvalue (e i) = ρ.eigenvalue i :=
  Fintype.exists_equiv_of_multiset_eq _ _ (ρ.eigenvalues_map_unitary U).symm

/-- The real operator spectrum is invariant under unitary transport. -/
theorem realSpectrum_map_unitary (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    _root_.spectrum ℝ (ρ.map U).op = _root_.spectrum ℝ ρ.op := by
  obtain ⟨e, he⟩ := ρ.exists_equiv_eigenvalue_map_unitary U
  rw [realSpectrum_eq_range_eigenvalue, realSpectrum_eq_range_eigenvalue,
    ← e.surjective.range_comp (ρ.map U).eigenvalue]
  exact congrArg Set.range (funext he)

end Qudit.Density
