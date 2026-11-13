/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Schmidt
public import FQFP.CQM.Qudit.State.Separable

/-!
# Schmidt rank and pure-state separability

The Schmidt rank counts the positive coefficients in the existing Schmidt decomposition.
It equals the rank of either marginal, in coordinate-free or matrix form. A pure state is
separable exactly when this rank is one. Swapping subsystems or changing global phase
does not change the Schmidt rank.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped ComplexOrder

namespace Qudit

noncomputable section

variable {H K : Qudit}

namespace UnitState

/-- The number of nonzero coefficients in the Schmidt decomposition. -/
def schmidtRank (ψ : UnitState (H ⊗ K)) : ℕ := Fintype.card ψ.SchmidtIndex

/-- The Schmidt rank counts the nonzero eigenvalues of the left marginal, with multiplicity. -/
lemma schmidtRank_eq_card_nonzeroEigenvalues (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtRank = (Density.pure ψ).partialTraceRight.nonzeroEigenvalues.card := by
  classical
  simp only [schmidtRank, Fintype.card_subtype, Density.nonzeroEigenvalues,
    Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => 0 < (Density.pure ψ).partialTraceRight.eigenvalue i)).card =
    (Finset.univ.filter (fun i => (Density.pure ψ).partialTraceRight.eigenvalue i ≠ 0)).card
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (lt_iff_le_and_ne).trans (by
    simp [(Density.pure ψ).partialTraceRight.eigenvalue_nonneg i, ne_comm])

/-- The Schmidt rank equals the dimension of the range of the left marginal. -/
lemma schmidtRank_eq_finrank_range_partialTraceRight (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtRank = Module.finrank ℂ (LinearMap.range (Density.pure ψ).partialTraceRight.op) := by
  rw [schmidtRank_eq_card_nonzeroEigenvalues, Density.card_nonzeroEigenvalues]

/-- The Schmidt rank equals the dimension of the range of the right marginal. -/
lemma schmidtRank_eq_finrank_range_partialTraceLeft (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtRank = Module.finrank ℂ (LinearMap.range (Density.pure ψ).partialTraceLeft.op) := by
  rw [schmidtRank_eq_card_nonzeroEigenvalues,
    Density.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft,
    Density.card_nonzeroEigenvalues]

/-- In any orthonormal basis, the left marginal's matrix rank is the Schmidt rank. -/
lemma schmidtRank_eq_rank_toMatrix_partialTraceRight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : UnitState (H ⊗ K)) (b : OrthonormalBasis ι ℂ H.state) :
    ψ.schmidtRank = ((Density.pure ψ).partialTraceRight.toMatrix b).rank := by
  rw [Density.rank_toMatrix, schmidtRank_eq_finrank_range_partialTraceRight]

/-- In any orthonormal basis, the right marginal's matrix rank is the Schmidt rank. -/
lemma schmidtRank_eq_rank_toMatrix_partialTraceLeft {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : UnitState (H ⊗ K)) (b : OrthonormalBasis ι ℂ K.state) :
    ψ.schmidtRank = ((Density.pure ψ).partialTraceLeft.toMatrix b).rank := by
  rw [Density.rank_toMatrix, schmidtRank_eq_finrank_range_partialTraceLeft]

/-- The rectangular coefficient matrix has the Schmidt rank in any pair of local bases. -/
lemma schmidtRank_eq_rank_coefficientMatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : UnitState (H ⊗ K)) (b : OrthonormalBasis ι ℂ H.state)
    (c : OrthonormalBasis κ ℂ K.state) :
    ψ.schmidtRank = (ψ.coefficientMatrix b c).rank := by
  classical
  rw [schmidtRank_eq_rank_toMatrix_partialTraceLeft ψ c,
    Density.toMatrix_partialTraceLeft_pure ψ b c, Matrix.rank_transpose,
    Matrix.rank_conjTranspose_mul_self]

/-- Exchanging the two systems preserves Schmidt rank. -/
lemma schmidtRank_swap (ψ : UnitState (H ⊗ K)) : ψ.swap.schmidtRank = ψ.schmidtRank := by
  rw [schmidtRank_eq_finrank_range_partialTraceRight, Density.partialTraceRight_pure_swap,
    ← schmidtRank_eq_finrank_range_partialTraceLeft]

/-- A global phase does not affect Schmidt rank. -/
lemma schmidtRank_phase (ψ : UnitState (H ⊗ K)) (c : ℂ) (hc : ‖c‖ = 1) :
    (ψ.phase c hc).schmidtRank = ψ.schmidtRank := by
  rw [schmidtRank_eq_finrank_range_partialTraceRight, Density.pure_phase,
    ← schmidtRank_eq_finrank_range_partialTraceRight]

/-- A bipartite unit vector is a product vector exactly when its Schmidt rank is one. -/
lemma isProduct_iff_schmidtRank_eq_one (ψ : UnitState (H ⊗ K)) :
    ψ.IsProduct ↔ ψ.schmidtRank = 1 := by
  rw [isProduct_iff_isPure_partialTraceRight, Density.isPure_iff_finrank_range_eq_one,
    ← schmidtRank_eq_finrank_range_partialTraceRight]

/-- Product unit vectors have Schmidt rank one, including in unequal dimensions. -/
lemma schmidtRank_tensor (v : UnitState H) (w : UnitState K) :
    (v.tensor w).schmidtRank = 1 :=
  (isProduct_iff_schmidtRank_eq_one _).mp (isProduct_tensor v w)

end UnitState

namespace Density

/-- A pure density operator is separable exactly when its vector has Schmidt rank one. -/
lemma isSeparable_pure_iff_schmidtRank_eq_one (ψ : UnitState (H ⊗ K)) :
    (pure ψ).IsSeparable ↔ ψ.schmidtRank = 1 := by
  rw [isSeparable_pure_iff, ψ.isProduct_iff_schmidtRank_eq_one]

/-- Both marginals of a pure density operator have the same operator rank. -/
lemma IsPure.finrank_range_partialTraceRight_eq_partialTraceLeft
    {ρ : Density (H ⊗ K)} (hρ : ρ.IsPure) :
    Module.finrank ℂ (LinearMap.range ρ.partialTraceRight.op) =
      Module.finrank ℂ (LinearMap.range ρ.partialTraceLeft.op) := by
  rw [← card_nonzeroEigenvalues, ← card_nonzeroEigenvalues,
    hρ.nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft]

end Density

end

end Qudit
