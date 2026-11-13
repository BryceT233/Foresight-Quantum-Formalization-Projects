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
-/

@[expose] public section

open scoped BigOperators

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

/-- The nonzero eigenvalues of a density operator, retaining their multiplicities. -/
def nonzeroEigenvalues (ρ : Density H) : Multiset ℝ :=
  (Finset.univ.val.map ρ.eigenvalue).filter (· ≠ 0)

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
