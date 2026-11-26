/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Composite.Basic

/-!
# Purifying mixtures of unit states with orthogonal labels

The coherent vector `∑ i, sqrt (w i) • ψ i ⊗ b i` purifies the existing
`Density.mixture` of pure densities. Orthogonal labels ensure that overlaps of
two such vectors with the same weights are exactly the weighted sums of overlaps.
Zero weights are allowed; no division by a weight is used.

## Main definitions and results

* `Qudit.Operator.partialTraceRight_outer_sum_sqrt_smul`: the weighted outer-product sum.
* `Qudit.UnitState.purifyMixture`: purification of a finite pure-state mixture with orthogonal
  labels.
* `Qudit.UnitState.partialTraceRight_pure_purifyMixture`: discarding labels recovers the mixture.
* `Qudit.UnitState.inner_purifyMixture`: common weights and labels give a weighted overlap sum.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Operator

variable {H K : Qudit}

/-- Tracing an outer product after discarding the right factor recovers its inner product. -/
lemma trace_partialTraceRight_outer (v w : (H ⊗ K).state) :
    (partialTraceRight (outer v w)).trace = inner ℂ w v :=
  (LinearMap.trace_partialTraceRight _).trans (trace_outer (H := H ⊗ K) v w)

/-- With common orthonormal labels, the partial trace pairs vectors with the same label and
recovers the weight from the two square-root coefficients. -/
lemma partialTraceRight_outer_sum_sqrt_smul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v u : ι → H.state) :
    partialTraceRight (outer (∑ i, ((Real.sqrt (w i) : ℂ) • v i) ⊗ₜ[ℂ] b i)
      (∑ i, ((Real.sqrt (w i) : ℂ) • u i) ⊗ₜ[ℂ] b i)) =
      ∑ i, (w i : ℂ) • outer (v i) (u i) := by
  rw [partialTraceRight_outer_sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  ext x
  simp only [outer_apply, LinearMap.smul_apply, inner_smul_left, Complex.conj_ofReal, smul_smul]
  rw [mul_right_comm, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (hw i)]

end Qudit.Operator

namespace Qudit.UnitState

noncomputable section

variable {H K : Qudit} {ι : Type*} [Fintype ι]

/-- Discarding the label of a square-root-weighted coherent sum gives the corresponding
weighted sum of pure operators, even before the weights are normalized. -/
lemma partialTraceRight_outer_sum_sqrt_smul (b : OrthonormalBasis ι ℂ K.state)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ψ : ι → UnitState H) :
    Operator.partialTraceRight
      (Operator.outer (∑ i, ((Real.sqrt (w i) : ℂ) • (ψ i).val) ⊗ₜ[ℂ] b i)
        (∑ i, ((Real.sqrt (w i) : ℂ) • (ψ i).val) ⊗ₜ[ℂ] b i)) =
      ∑ i, (w i : ℂ) • (Density.pure (ψ i)).op :=
  Operator.partialTraceRight_outer_sum_sqrt_smul b w hw (fun i => (ψ i).val) (fun i => (ψ i).val)

/-- Purify a finite mixture of unit states by coherently recording an orthonormal label. -/
def purifyMixture (b : OrthonormalBasis ι ℂ K.state) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ψ : ι → UnitState H) :
    UnitState (H ⊗ K) :=
  ⟨∑ i, ((Real.sqrt (w i) : ℂ) • (ψ i).val) ⊗ₜ[ℂ] b i, by
    rw [state.Normalized, ← Operator.trace_partialTraceRight_outer,
      partialTraceRight_outer_sum_sqrt_smul b w hw ψ]
    exact (Density.mixture w hw hs (fun i => Density.pure (ψ i))).trace_one⟩

/-- Discarding the orthogonal label recovers the mixture of the original pure densities. -/
lemma partialTraceRight_pure_purifyMixture (b : OrthonormalBasis ι ℂ K.state)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ψ : ι → UnitState H) :
    (Density.pure (purifyMixture b w hw hs ψ)).partialTraceRight =
      Density.mixture w hw hs (fun i => Density.pure (ψ i)) := by
  apply Density.ext
  exact partialTraceRight_outer_sum_sqrt_smul b w hw ψ

/-- Equal weights and a common orthogonal label turn the coherent overlap into the
weighted sum of the component overlaps, with their complex phases retained. -/
lemma inner_purifyMixture (b : OrthonormalBasis ι ℂ K.state)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ψ φ : ι → UnitState H) :
    inner ℂ (purifyMixture b w hw hs ψ).val (purifyMixture b w hw hs φ).val =
      ∑ i, (w i : ℂ) * inner ℂ (ψ i).val (φ i).val := by
  change inner ℂ (∑ i, ((Real.sqrt (w i) : ℂ) • (ψ i).val) ⊗ₜ[ℂ] b i)
    (∑ i, ((Real.sqrt (w i) : ℂ) • (φ i).val) ⊗ₜ[ℂ] b i) = _
  rw [← Operator.trace_partialTraceRight_outer,
    Operator.partialTraceRight_outer_sum_sqrt_smul b w hw]
  simp only [Operator.trace, map_sum, map_smul, smul_eq_mul, Operator.trace_outer]

end

end Qudit.UnitState
