/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite

/-!
# Purifying mixtures of unit states with orthogonal labels

The coherent vector `∑ i, sqrt (w i) • ψ i ⊗ b i` purifies the existing
`Density.mixture` of pure densities. Orthogonal labels ensure that overlaps of
two such vectors with the same weights are exactly the weighted sums of overlaps.
Zero weights are allowed; no division by a weight is used.

## Main definitions and results

* `Qudit.UnitState.purifyMixture`: purification of a finite pure-state mixture with orthogonal
  labels.
* `Qudit.UnitState.partialTraceRight_pure_purifyMixture`: discarding labels recovers the mixture.
* `Qudit.UnitState.inner_purifyMixture`: common weights and labels give a weighted overlap sum.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

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
      ∑ i, (w i : ℂ) • (Density.pure (ψ i)).op := by
  rw [Operator.partialTraceRight_outer_sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Operator.outer_smul_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow, Real.sq_sqrt (hw i)]
  rfl

/-- Purify a finite mixture of unit states by coherently recording an orthonormal label. -/
def purifyMixture (b : OrthonormalBasis ι ℂ K.state) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ψ : ι → UnitState H) :
    UnitState (H ⊗ K) :=
  ⟨∑ i, ((Real.sqrt (w i) : ℂ) • (ψ i).val) ⊗ₜ[ℂ] b i, by
    have ht := (LinearMap.trace_partialTraceRight _).symm.trans
      (congrArg (Operator.trace (H := H))
        (partialTraceRight_outer_sum_sqrt_smul b w hw ψ))
    exact (Operator.trace_outer _ _).symm.trans
      (ht.trans (Density.mixture w hw hs (fun i => Density.pure (ψ i))).trace_one)⟩

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
  have h := congrArg (Operator.trace (H := H))
    (Operator.partialTraceRight_outer_sum_tmul b
      (fun i => (Real.sqrt (w i) : ℂ) • (φ i).val)
      (fun i => (Real.sqrt (w i) : ℂ) • (ψ i).val))
  have hi : inner ℂ (purifyMixture b w hw hs ψ).val (purifyMixture b w hw hs φ).val =
      Operator.trace (H := H) (∑ i, Operator.outer
        ((Real.sqrt (w i) : ℂ) • (φ i).val) ((Real.sqrt (w i) : ℂ) • (ψ i).val)) :=
    (Operator.trace_outer _ _).symm.trans
      ((LinearMap.trace_partialTraceRight _).symm.trans h)
  rw [hi]
  change LinearMap.trace ℂ H.state _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Operator.trace (H := H) (Operator.outer _ _) = _
  rw [Operator.trace_outer, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (hw i)]

end

end Qudit.UnitState
