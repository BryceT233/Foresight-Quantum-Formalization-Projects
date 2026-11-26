/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
Physlib reference for separability and decomposition into pure product states.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean

QuantumInfo/States/Ensemble.lean
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Composite.Pure
public import FQFP.CQM.Qudit.State.Spectral.Basic
public import Mathlib.Analysis.Convex.Combination

/-!
# Separable mixed states

A bipartite density operator is separable when it is a finite convex combination of
product density operators, as in physlib's `MState.IsSeparable`. We use the real convex
hull and prove the equivalent finite ensemble formulation. No closure or limit is added.
Non-product mixed states can be separable: classical correlations are allowed.

Spectral refinement gives the equivalent convex hull of pure product states. For a pure
density operator, separability is equivalent to its unit vector being a product vector,
as in physlib's `MState.pure_separable_iff_IsProd`. This is also equivalent to purity of
either marginal, extending `MState.pure_separable_iff_traceLeft_pure` to both factors.

## Main definitions and results

* `Qudit.Density.IsSeparable`: membership in the convex hull of product densities.
* `Qudit.Density.isSeparable_iff_exists_mixture`: separability as a finite mixture of products.
* `Qudit.Density.isSeparable_iff_exists_pure_ensemble`: separability as an ensemble of pure
  products.
* `Qudit.Density.isSeparable_pure_iff`: a pure density is separable exactly for product vectors.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- A mixed state is separable if it is a finite convex combination of product states. -/
def IsSeparable (ρ : Density (H ⊗ K)) : Prop :=
  ρ.op ∈ convexHull ℝ (Set.range fun p : Density H × Density K => (p.1.tensor p.2).op)

/-- Every product density state is separable. -/
lemma isSeparable_tensor (ρ : Density H) (σ : Density K) : (ρ.tensor σ).IsSeparable :=
  subset_convexHull ℝ _ ⟨(ρ, σ), rfl⟩

/-- A finite probability mixture of product states is separable. -/
lemma isSeparable_mixture_tensor {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ρ : ι → Density H) (σ : ι → Density K) :
    (mixture w hw hs (fun i => (ρ i).tensor (σ i))).IsSeparable := by
  apply mem_convexHull_of_exists_fintype w (fun i => ((ρ i).tensor (σ i)).op) hw hs
  · exact fun i => ⟨(ρ i, σ i), rfl⟩
  · exact (op_mixture_real w hw hs _).symm

/-- Separability is exactly the existence of a finite ensemble of product density states. -/
lemma isSeparable_iff_exists_mixture (τ : Density (H ⊗ K)) :
    τ.IsSeparable ↔ ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ)
      (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
      (ρ : ι → Density H) (σ : ι → Density K),
        mixture w hw hs (fun i => (ρ i).tensor (σ i)) = τ := by
  constructor
  · intro h
    obtain ⟨ι, _, w, z, hw, hs, hz, heq⟩ := mem_convexHull_iff_exists_fintype.mp h
    choose p hp using hz
    refine ⟨ι, inferInstance, w, hw, hs, fun i => (p i).1, fun i => (p i).2, ?_⟩
    apply Density.ext
    simpa only [op_mixture_real, ← hp] using heq
  · rintro ⟨ι, _, w, hw, hs, ρ, σ, rfl⟩
    exact isSeparable_mixture_tensor w hw hs ρ σ

/-- Finite probabilistic mixing preserves separability. -/
lemma IsSeparable.mixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ρ : ι → Density (H ⊗ K)) (hρ : ∀ i, (ρ i).IsSeparable) :
    (Density.mixture w hw hs ρ).IsSeparable := by
  change (Density.mixture w hw hs ρ).op ∈ _
  rw [op_mixture_real]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw i) hs (fun i _ => hρ i)

/-- Binary convex mixing preserves separability. -/
lemma IsSeparable.mix {ρ σ : Density (H ⊗ K)} (hρ : ρ.IsSeparable) (hσ : σ.IsSeparable)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : (Density.mix p hp₀ hp₁ ρ σ).IsSeparable := by
  have h : (Density.mix p hp₀ hp₁ ρ σ).op = p • ρ.op + (1 - p) • σ.op :=
    congrArg₂ (· + ·) (RCLike.real_smul_eq_coe_smul (K := ℂ) p ρ.op).symm
      (RCLike.real_smul_eq_coe_smul (K := ℂ) (1 - p) σ.op).symm
  change (Density.mix p hp₀ hp₁ ρ σ).op ∈ _
  rw [h]
  exact convex_convexHull ℝ _ hρ hσ hp₀ (sub_nonneg.mpr hp₁) (by ring)

/-- Separable states are exactly the convex hull of pure product states. -/
lemma isSeparable_iff_mem_convexHull_pure (τ : Density (H ⊗ K)) :
    τ.IsSeparable ↔ τ.op ∈ convexHull ℝ
      (Set.range fun p : UnitState H × UnitState K => (pure (p.1.tensor p.2)).op) := by
  constructor
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨⟨ρ, σ⟩, rfl⟩
    let e := ρ.spectralEnsemble.tensor σ.spectralEnsemble
    have he : e.mix = ρ.tensor σ := by
      rw [Ensemble.mix_tensor, mix_spectralEnsemble, mix_spectralEnsemble]
    dsimp only
    rw [← he]
    apply mem_convexHull_of_exists_fintype e.weight (fun i => (e.state i).op)
      e.weight_nonneg e.sum_weight
    · intro i
      refine ⟨(UnitState.ofBasis ρ.eigenbasis i.1, UnitState.ofBasis σ.eigenbasis i.2), ?_⟩
      exact congrArg Density.op (tensor_pure _ _).symm
    · exact (op_mixture_real _ _ _ _).symm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    rintro _ ⟨⟨v, w⟩, rfl⟩
    dsimp only
    rw [← tensor_pure]
    exact isSeparable_tensor _ _

/-- Every separable state has a finite ensemble of pure product vectors, and conversely. -/
lemma isSeparable_iff_exists_pure_ensemble (τ : Density (H ⊗ K)) :
    τ.IsSeparable ↔ ∃ (ι : Type) (_ : Fintype ι) (w : Convexity.StdSimplex ℝ ι)
      (v : ι → UnitState H) (u : ι → UnitState K),
        (Ensemble.ofPure w (fun i => (v i).tensor (u i))).mix = τ := by
  rw [isSeparable_iff_mem_convexHull_pure]
  constructor
  · intro h
    obtain ⟨ι, _, w, z, hw, hs, hz, heq⟩ := mem_convexHull_iff_exists_fintype.mp h
    choose p hp using hz
    let e := Ensemble.ofWeights w hw hs (fun i => pure ((p i).1.tensor (p i).2))
    refine ⟨ι, inferInstance, e.distribution, fun i => (p i).1, fun i => (p i).2, ?_⟩
    apply Density.ext
    change (mixture w hw hs (fun i => pure ((p i).1.tensor (p i).2))).op = τ.op
    simpa only [op_mixture_real, ← hp] using heq
  · rintro ⟨ι, _, w, v, u, rfl⟩
    let e := Ensemble.ofPure w (fun i => (v i).tensor (u i))
    apply mem_convexHull_of_exists_fintype e.weight (fun i => (e.state i).op)
      e.weight_nonneg e.sum_weight
    · exact fun i => ⟨(v i, u i), rfl⟩
    · exact (op_mixture_real _ _ _ _).symm

/-- A pure density operator is separable exactly when its unit vector is a product vector.
The equality of vectors is exact: the otherwise arbitrary global phase is absorbed on the left. -/
lemma isSeparable_pure_iff (ψ : UnitState (H ⊗ K)) :
    (pure ψ).IsSeparable ↔ ψ.IsProduct := by
  constructor
  · intro h
    obtain ⟨ι, _, w, v, u, he⟩ := (isSeparable_iff_exists_pure_ensemble _).mp h
    obtain ⟨i, hi⟩ : ∃ i, w.weights i ≠ 0 := by
      by_contra! hzero
      have hs := w.total_of_fintype
      simp only [hzero, Finset.sum_const_zero] at hs
      exact zero_ne_one hs
    have hp := (Ensemble.mix_ofPure_eq_pure_iff w _ ψ).mp he i hi
    obtain ⟨c, hc, hv⟩ := (pure_eq_pure_iff ψ ((v i).tensor (u i))).mp hp.symm
    refine ⟨(v i).phase c hc, u i, ?_⟩
    apply Subtype.ext
    change ψ.val = (c • (v i).val) ⊗ₜ[ℂ] (u i).val
    rw [← TensorProduct.smul_tmul']
    exact hv
  · rintro ⟨v, u, rfl⟩
    rw [← tensor_pure]
    exact isSeparable_tensor _ _

/-- A pure bipartite state is separable exactly when its left marginal is pure. -/
lemma isSeparable_pure_iff_isPure_partialTraceRight (ψ : UnitState (H ⊗ K)) :
    (pure ψ).IsSeparable ↔ (pure ψ).partialTraceRight.IsPure := by
  rw [isSeparable_pure_iff, ψ.isProduct_iff_isPure_partialTraceRight]

/-- A pure bipartite state is separable exactly when its right marginal is pure. -/
lemma isSeparable_pure_iff_isPure_partialTraceLeft (ψ : UnitState (H ⊗ K)) :
    (pure ψ).IsSeparable ↔ (pure ψ).partialTraceLeft.IsPure := by
  rw [isSeparable_pure_iff, ψ.isProduct_iff_isPure_partialTraceLeft]

/-- For a pure bipartite density operator, separability is purity of the left marginal. -/
lemma IsPure.isSeparable_iff_isPure_partialTraceRight {ρ : Density (H ⊗ K)} (hρ : ρ.IsPure) :
    ρ.IsSeparable ↔ ρ.partialTraceRight.IsPure := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact isSeparable_pure_iff_isPure_partialTraceRight ψ

/-- For a pure bipartite density operator, separability is purity of the right marginal. -/
lemma IsPure.isSeparable_iff_isPure_partialTraceLeft {ρ : Density (H ⊗ K)} (hρ : ρ.IsPure) :
    ρ.IsSeparable ↔ ρ.partialTraceLeft.IsPure := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact isSeparable_pure_iff_isPure_partialTraceLeft ψ

end

end Qudit.Density
