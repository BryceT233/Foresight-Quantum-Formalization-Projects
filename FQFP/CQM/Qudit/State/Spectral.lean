/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Ensemble

/-!
# Spectral ensembles

The eigenvalues of a density operator form a probability distribution on an orthonormal
eigenbasis. Its pure-state ensemble mixes back to the original density operator, including
singular states and zero eigenvalues. This is the coordinate-free counterpart of physlib's
`Ensemble.spectral_ensemble` and `Ensemble.spectral_ensemble_mix`.

## Main definitions and results

* `Qudit.Density.eigenvalue`: ordered eigenvalues with multiplicities.
* `Qudit.Density.spectralEnsemble`: the pure eigenstates weighted by their eigenvalues.
* `Qudit.Density.mix_spectralEnsemble`: the spectral ensemble recovers the density.
* `Qudit.Density.card_positiveEigenIndex`: positive spectral labels count the operator rank.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory MonoidalCategory

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- The eigenvalues of a density operator, in decreasing order and with multiplicities. -/
def eigenvalue (ρ : Density H) : Fin (Module.finrank ℂ H.state) → ℝ :=
  ρ.positive.isSymmetric.eigenvalues rfl

/-- An orthonormal eigenbasis of a density operator. -/
def eigenbasis (ρ : Density H) :
    OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ H.state :=
  ρ.positive.isSymmetric.eigenvectorBasis rfl

/-- A density operator acts diagonally on its eigenbasis. -/
lemma apply_eigenbasis (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    ρ.op (ρ.eigenbasis i) = (ρ.eigenvalue i : ℂ) • ρ.eigenbasis i :=
  ρ.positive.isSymmetric.apply_eigenvectorBasis rfl i

/-- Product eigenbases diagonalize tensor products of density operators. -/
lemma tensor_apply_eigenbasis {K : Qudit} (ρ : Density H) (σ : Density K)
    (i : Fin (Module.finrank ℂ H.state) × Fin (Module.finrank ℂ K.state)) :
    (ρ.tensor σ).op ((ρ.eigenbasis.tensorProduct σ.eigenbasis) i) =
      (↑(ρ.eigenvalue i.1 * σ.eigenvalue i.2) : ℂ) •
        (ρ.eigenbasis.tensorProduct σ.eigenbasis) i := by
  rcases i with ⟨i, j⟩
  rw [OrthonormalBasis.tensorProduct_apply ρ.eigenbasis σ.eigenbasis i j]
  simp only [op_tensor, Operator.tensor_apply, apply_eigenbasis,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Complex.ofReal_mul, mul_comm]

/-- All eigenvalues of a density operator are nonnegative. -/
lemma eigenvalue_nonneg (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    0 ≤ ρ.eigenvalue i := ρ.positive.nonneg_eigenvalues rfl i

/-- The spectral decomposition as a sum of weighted orthogonal rank-one projections. -/
lemma op_eq_sum_eigenvalue_smul_outer (ρ : Density H) :
    ρ.op = ∑ i, (ρ.eigenvalue i : ℂ) •
      Operator.outer (ρ.eigenbasis i) (ρ.eigenbasis i) := by
  rw [← Operator.sum_outer_basis ρ.eigenbasis ρ.op]
  simp only [apply_eigenbasis, Operator.outer_smul_left]

/-- The eigenvalues of a density operator sum to one. -/
lemma sum_eigenvalue (ρ : Density H) : ∑ i, ρ.eigenvalue i = 1 := by
  have h := ρ.trace_one
  rw [ρ.op_eq_sum_eigenvalue_smul_outer] at h
  have hb (i) : inner ℂ (ρ.eigenbasis i) (ρ.eigenbasis i) = 1 :=
    inner_self_eq_one_of_norm_eq_one (ρ.eigenbasis.norm_eq_one i)
  simp only [map_sum, map_smul, Operator.trace_outer, hb, smul_eq_mul, mul_one,
    ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Every eigenvalue of a density operator is at most one. -/
lemma eigenvalue_le_one (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    ρ.eigenvalue i ≤ 1 := by
  rw [← ρ.sum_eigenvalue]
  exact Finset.single_le_sum (fun j _ => ρ.eigenvalue_nonneg j) (Finset.mem_univ i)

/-- Any orthonormal diagonalization gives the same eigenvalues with multiplicities. -/
lemma _root_.Qudit.Operator.eigenvalues_eq_of_eigenbasis {ι : Type*} [Fintype ι]
    {A : Operator H} (hA : A.IsSymmetric)
    (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, A (b i) = (w i : ℂ) • b i) :
    Finset.univ.val.map (hA.eigenvalues rfl) = Finset.univ.val.map w := by
  classical
  apply Multiset.map_injective Complex.ofReal_injective
  have hm : LinearMap.toMatrix b.toBasis b.toBasis A =
      Matrix.diagonal (fun i => (w i : ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr (A (b j)) i = _
    rw [b.repr_apply_apply, hw, inner_smul_right, b.inner_eq_ite]
    by_cases hij : i = j <;> simp [hij]
  have hr := hA.roots_charpoly_eq_eigenvalues rfl
  change A.charpoly.roots = Finset.univ.val.map (Complex.ofReal ∘ (hA.eigenvalues rfl)) at hr
  simp only [Multiset.map_map]
  rw [← hr, ← LinearMap.charpoly_toMatrix A b.toBasis, hm, Matrix.charpoly_diagonal,
    Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp

/-- Any orthonormal diagonalization gives the same eigenvalues with multiplicities. -/
lemma eigenvalues_eq_of_eigenbasis {ι : Type*} [Fintype ι] (ρ : Density H)
    (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    Finset.univ.val.map ρ.eigenvalue = Finset.univ.val.map w :=
  Operator.eigenvalues_eq_of_eigenbasis ρ.positive.isSymmetric b w hw

/-- Spectral sums can be evaluated using any orthonormal diagonalization. -/
lemma sum_eigenvalue_eq_of_eigenbasis {ι : Type*} [Fintype ι] (ρ : Density H)
    (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) (f : ℝ → ℝ) :
    ∑ i, f (ρ.eigenvalue i) = ∑ i, f (w i) := by
  have h := congrArg (fun s : Multiset ℝ => (s.map f).sum)
    (ρ.eigenvalues_eq_of_eigenbasis b w hw)
  simpa only [Finset.sum, Multiset.map_map, Function.comp_def] using h

/-- The nonzero eigenvalues of a density operator, retaining their multiplicities. -/
def nonzeroEigenvalues (ρ : Density H) : Multiset ℝ :=
  (Finset.univ.val.map ρ.eigenvalue).filter (· ≠ 0)

/-- A spectral sum of a function vanishing at zero uses only the nonzero spectrum. -/
lemma sum_eigenvalue_eq_sum_nonzeroEigenvalues (ρ : Density H) (f : ℝ → ℝ)
    (hf : f 0 = 0) : ∑ i, f (ρ.eigenvalue i) = (ρ.nonzeroEigenvalues.map f).sum := by
  classical
  simp only [nonzeroEigenvalues, Multiset.filter_map, Multiset.map_map]
  change (∑ i, f (ρ.eigenvalue i)) =
    ∑ i ∈ Finset.univ.filter (fun i => ρ.eigenvalue i ≠ 0), f (ρ.eigenvalue i)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ρ.eigenvalue i = 0 <;> simp [hi, hf]

/-- The eigenbasis labels with strictly positive eigenvalues. -/
abbrev PositiveEigenIndex (ρ : Density H) :=
  {i : Fin (Module.finrank ℂ H.state) // 0 < ρ.eigenvalue i}

/-- Positive eigenbasis labels count the nonzero eigenvalues with multiplicity. -/
lemma card_positiveEigenIndex_eq_card_nonzeroEigenvalues (ρ : Density H) :
    Fintype.card ρ.PositiveEigenIndex = ρ.nonzeroEigenvalues.card := by
  classical
  simp only [PositiveEigenIndex, Fintype.card_subtype, nonzeroEigenvalues,
    Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => 0 < ρ.eigenvalue i)).card =
    (Finset.univ.filter (fun i => ρ.eigenvalue i ≠ 0)).card
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (lt_iff_le_and_ne).trans (by simp [ρ.eigenvalue_nonneg i, ne_comm])

/-- The number of nonzero eigenvalues, with multiplicity, is the operator's rank. -/
lemma card_nonzeroEigenvalues (ρ : Density H) :
    ρ.nonzeroEigenvalues.card = Module.finrank ℂ (LinearMap.range ρ.op) := by
  classical
  have hz := ρ.positive.isSymmetric.card_filter_eigenvalues_eq rfl (0 : ℂ)
  change (Finset.univ.filter (fun i => (ρ.eigenvalue i : ℂ) = 0)).card =
    Module.finrank ℂ (Module.End.eigenspace ρ.op 0) at hz
  simp only [Complex.ofReal_eq_zero] at hz
  rw [Module.End.eigenspace_zero] at hz
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i => ρ.eigenvalue i = 0)
  have hr := ρ.op.finrank_range_add_finrank_ker
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  simp only [nonzeroEigenvalues, Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => ρ.eigenvalue i ≠ 0)).card = _
  lia

/-- The positive spectral subspace has as many eigenbasis labels as the operator's rank. -/
lemma card_positiveEigenIndex (ρ : Density H) :
    Fintype.card ρ.PositiveEigenIndex = Module.finrank ℂ (LinearMap.range ρ.op) := by
  rw [card_positiveEigenIndex_eq_card_nonzeroEigenvalues, card_nonzeroEigenvalues]

/-- The spectral decomposition restricted to positive eigenvalues discards only zero terms. -/
lemma op_eq_sum_positiveEigenvalue_smul_outer (ρ : Density H) :
    ρ.op = ∑ i : ρ.PositiveEigenIndex, (ρ.eigenvalue i.val : ℂ) •
      Operator.outer (ρ.eigenbasis i.val) (ρ.eigenbasis i.val) := by
  classical
  rw [ρ.op_eq_sum_eigenvalue_smul_outer]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => 0 < ρ.eigenvalue i)) (by simp)
    (fun i => (ρ.eigenvalue i : ℂ) • Operator.outer (ρ.eigenbasis i) (ρ.eigenbasis i)),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · have hz : ρ.eigenvalue i = 0 := le_antisymm (le_of_not_gt hi) (ρ.eigenvalue_nonneg i)
    simp only [hz, Complex.ofReal_zero, zero_smul]

/-- The nonzero characteristic roots are the complex images of the nonzero eigenvalues. -/
lemma roots_charpoly_filter_ne_zero (ρ : Density H) :
    ρ.op.charpoly.roots.filter (· ≠ 0) = ρ.nonzeroEigenvalues.map Complex.ofReal := by
  classical
  rw [ρ.positive.isSymmetric.roots_charpoly_eq_eigenvalues rfl]
  change (Finset.univ.val.map (Complex.ofReal ∘ ρ.eigenvalue)).filter (· ≠ 0) = _
  rw [← Multiset.map_map]
  simp only [Multiset.filter_map, nonzeroEigenvalues, Function.comp_def, Complex.ofReal_ne_zero]

/-- The spectral probability distribution; zero eigenvalues are retained. -/
def spectrum (ρ : Density H) : Convexity.StdSimplex ℝ (Fin (Module.finrank ℂ H.state)) :=
  (Ensemble.ofWeights ρ.eigenvalue ρ.eigenvalue_nonneg ρ.sum_eigenvalue
    (fun i => pure (UnitState.ofBasis ρ.eigenbasis i))).distribution

/-- The spectral ensemble consists of the pure eigenstates with their eigenvalue weights. -/
def spectralEnsemble (ρ : Density H) : Ensemble H (Fin (Module.finrank ℂ H.state)) :=
  Ensemble.ofPure ρ.spectrum (UnitState.ofBasis ρ.eigenbasis)

/-- The weight of a spectral label is its eigenvalue. -/
lemma weight_spectralEnsemble (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    ρ.spectralEnsemble.weight i = ρ.eigenvalue i := by
  simp [spectralEnsemble, spectrum, Ensemble.ofPure, Ensemble.weight, Ensemble.ofWeights]

/-- Every state of the spectral ensemble is the corresponding pure eigenstate. -/
lemma state_spectralEnsemble (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    ρ.spectralEnsemble.state i = pure (UnitState.ofBasis ρ.eigenbasis i) := rfl

/-- Forgetting the spectral label recovers the original density operator. -/
lemma mix_spectralEnsemble (ρ : Density H) : ρ.spectralEnsemble.mix = ρ := by
  apply Density.ext
  simpa only [Ensemble.op_mix, weight_spectralEnsemble, state_spectralEnsemble,
    op_pure, UnitState.coe_ofBasis] using ρ.op_eq_sum_eigenvalue_smul_outer.symm

end

end Qudit.Density
