/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Purification.Basic
public import FQFP.CQM.Qudit.State.Composite.SchmidtRank
import FQFP.CQM.Qudit.State.Purification.Mixture

/-!
# Minimal purification

The least possible auxiliary dimension of a purification is the rank of the density
operator. The lower bound follows from Schmidt rank. The construction retains exactly
the positive spectral labels and pairs their weighted eigenvectors with an auxiliary
orthonormal basis. In particular, zero eigenvalues do not use auxiliary dimensions.

`Density.purifyMinimal` uses the standard space of dimension equal to the operator's rank.
Every other purification is its image under an auxiliary isometry, with exact vector
equality. The existing `Density.purify` continues to use a full-dimensional auxiliary copy.

## Main definitions and results

* `Qudit.Density.purifyMinimal`: a purification with auxiliary dimension equal to the operator rank.
* `Qudit.Density.finrank_range_le_of_purification`: the lower bound on auxiliary dimension.
* `Qudit.Density.exists_purification_iff_finrank_le`: the exact dimension criterion for
  purification.
* `Qudit.Density.exists_eq_map_purifyMinimal`: every purification extends the minimal one
  isometrically.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- Any auxiliary system purifying a density operator has dimension at least its rank. -/
theorem finrank_range_le_of_purification (ρ : Density H) (ψ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ) :
    Module.finrank ℂ (LinearMap.range ρ.op) ≤ Module.finrank ℂ K.state := by
  have h := ψ.schmidtRank_le_finrank_right
  rwa [ψ.schmidtRank_eq_finrank_range_partialTraceRight, hψ] at h

/-- The positive spectral purification sum has the original density as its marginal. -/
lemma partialTraceRight_outer_positive_spectral_sum (ρ : Density H)
    (b : OrthonormalBasis ρ.PositiveEigenIndex ℂ K.state) :
    Operator.partialTraceRight
      (Operator.outer
        (∑ i, ((Real.sqrt (ρ.eigenvalue i.val) : ℂ) • ρ.eigenbasis i.val) ⊗ₜ[ℂ] b i)
        (∑ i, ((Real.sqrt (ρ.eigenvalue i.val) : ℂ) • ρ.eigenbasis i.val) ⊗ₜ[ℂ] b i)) =
      ρ.op := by
  rw [Operator.partialTraceRight_outer_sum_sqrt_smul b (fun i => ρ.eigenvalue i.val)
    (fun i => ρ.eigenvalue_nonneg i.val), ← ρ.op_eq_sum_positiveEigenvalue_smul_outer]

/-- Purify using an auxiliary basis indexed by exactly the positive eigenvalues. -/
def purifyMinimalWith (ρ : Density H)
    (b : OrthonormalBasis ρ.PositiveEigenIndex ℂ K.state) : UnitState (H ⊗ K) :=
  ⟨∑ i, ((Real.sqrt (ρ.eigenvalue i.val) : ℂ) • ρ.eigenbasis i.val) ⊗ₜ[ℂ] b i, by
    rw [state.Normalized, ← Operator.trace_partialTraceRight_outer,
      ρ.partialTraceRight_outer_positive_spectral_sum b, ρ.trace_one]⟩

/-- The vector of a minimal explicit-basis purification is its positive spectral sum. -/
lemma coe_purifyMinimalWith (ρ : Density H)
    (b : OrthonormalBasis ρ.PositiveEigenIndex ℂ K.state) :
    (ρ.purifyMinimalWith b).val =
      ∑ i, ((Real.sqrt (ρ.eigenvalue i.val) : ℂ) • ρ.eigenbasis i.val) ⊗ₜ[ℂ] b i := rfl

/-- Discarding the auxiliary basis of a minimal purification recovers the density. -/
lemma partialTraceRight_pure_purifyMinimalWith (ρ : Density H)
    (b : OrthonormalBasis ρ.PositiveEigenIndex ℂ K.state) :
    (pure (ρ.purifyMinimalWith b)).partialTraceRight = ρ := by
  apply Density.ext
  exact ρ.partialTraceRight_outer_positive_spectral_sum b

/-- The auxiliary dimension of a positive-eigenbasis purification is exactly the rank. -/
lemma finrank_eq_of_positiveEigenIndex_basis (ρ : Density H)
    (b : OrthonormalBasis ρ.PositiveEigenIndex ℂ K.state) :
    Module.finrank ℂ K.state = Module.finrank ℂ (LinearMap.range ρ.op) :=
  (Module.finrank_eq_card_basis b.toBasis).trans ρ.card_positiveEigenIndex

/-- A purification on a standard auxiliary system whose dimension is the density's rank. -/
def purifyMinimal (ρ : Density H) :
    UnitState (H ⊗ std (Module.finrank ℂ (LinearMap.range ρ.op))) :=
  ρ.purifyMinimalWith ((ZBasis _).reindex (Fintype.equivFinOfCardEq ρ.card_positiveEigenIndex).symm)

/-- The minimal purification pairs positive eigenvectors with distinct standard basis vectors. -/
lemma coe_purifyMinimal (ρ : Density H) :
    ρ.purifyMinimal.val = ∑ i : ρ.PositiveEigenIndex,
      ((Real.sqrt (ρ.eigenvalue i.val) : ℂ) • ρ.eigenbasis i.val) ⊗ₜ[ℂ]
        ZBasis _ (Fintype.equivFinOfCardEq ρ.card_positiveEigenIndex i) := by
  simp only [purifyMinimal, coe_purifyMinimalWith, OrthonormalBasis.reindex_apply,
    Equiv.symm_symm]

/-- The right partial trace of the minimal purification recovers the original density. -/
lemma partialTraceRight_pure_purifyMinimal (ρ : Density H) :
    (pure ρ.purifyMinimal).partialTraceRight = ρ :=
  ρ.partialTraceRight_pure_purifyMinimalWith _

/-- The minimal purification has Schmidt rank equal to its auxiliary dimension. -/
lemma schmidtRank_purifyMinimal (ρ : Density H) :
    ρ.purifyMinimal.schmidtRank = Module.finrank ℂ (LinearMap.range ρ.op) := by
  rw [UnitState.schmidtRank_eq_finrank_range_partialTraceRight,
    partialTraceRight_pure_purifyMinimal]

/-- Every density admits a purification attaining the lower bound on auxiliary dimension. -/
theorem exists_purification_finrank_eq (ρ : Density H) :
    ∃ (K : Qudit) (ψ : UnitState (H ⊗ K)), (pure ψ).partialTraceRight = ρ ∧
      Module.finrank ℂ K.state = Module.finrank ℂ (LinearMap.range ρ.op) :=
  ⟨_, ρ.purifyMinimal, ρ.partialTraceRight_pure_purifyMinimal, by simp⟩

/-- An auxiliary space admits a purification exactly when its dimension is at least the rank. -/
theorem exists_purification_iff_finrank_le (ρ : Density H) :
    (∃ ψ : UnitState (H ⊗ K), (pure ψ).partialTraceRight = ρ) ↔
      Module.finrank ℂ (LinearMap.range ρ.op) ≤ Module.finrank ℂ K.state := by
  constructor
  · rintro ⟨ψ, hψ⟩
    exact ρ.finrank_range_le_of_purification ψ hψ
  · intro hdim
    let V : std (Module.finrank ℂ (LinearMap.range ρ.op)) ⟶ K :=
      ofLinearIsometry (LinearIsometry.ofFinrankLE (by simpa using hdim))
    refine ⟨ρ.purifyMinimal.map (𝟙 H ⊗ₘ V), ?_⟩
    rw [UnitState.partialTraceRight_pure_map_isometry, partialTraceRight_pure_purifyMinimal]

/-- Every purification is an auxiliary-isometric image of the minimal purification. -/
theorem exists_eq_map_purifyMinimal (ρ : Density H) (ψ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ) :
    ∃ (V : std (Module.finrank ℂ (LinearMap.range ρ.op)) ⟶ K) (_ : IsIsometry V),
      ψ = ρ.purifyMinimal.map (𝟙 H ⊗ₘ V) :=
  ρ.exists_isometry_of_purifications ρ.purifyMinimal ψ
    (by simpa using ρ.finrank_range_le_of_purification ψ hψ)
    ρ.partialTraceRight_pure_purifyMinimal hψ

end

end Qudit.Density
