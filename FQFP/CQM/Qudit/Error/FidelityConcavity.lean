/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Error.FidelityChannel
public import FQFP.CQM.Qudit.State.PurificationMixture
public import FQFP.CQM.Qudit.Channel.Ensemble

/-!
# Joint concavity of mixed-state fidelity

For the existing unsquared `Density.fidelity`, simultaneously mixing two families
with the same probability weights gives at least the weighted sum of fidelities.
Phase-aligned Uhlmann purifications are combined with orthogonal labels, and the
auxiliary system is then discarded. The proof allows singular states and zero weights.
The binary statement is Watrous, *The Theory of Quantum Information*, Corollary 3.26.

## Main results

* `Qudit.Density.sum_mul_fidelity_le_fidelity_mixture`: joint concavity for finite probability
  mixtures.
* `Qudit.Density.mul_fidelity_add_le_fidelity_mix`: the binary joint-concavity inequality.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- Joint concavity of unsquared fidelity for arbitrary finite probability mixtures. -/
theorem sum_mul_fidelity_le_fidelity_mixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ρ σ : ι → Density H) :
    ∑ i, w i * (ρ i).fidelity (σ i) ≤
      (mixture w hw hs ρ).fidelity (mixture w hw hs σ) := by
  classical
  choose φ hφ he using fun i => (ρ i).exists_purification_inner_eq_fidelity (σ i)
    (ρ i).purify (ρ i).partialTraceRight_pure_purify (LinearMap.finrank_range_le (σ i).op)
  let b : OrthonormalBasis ι ℂ (std (Fintype.card ι)).state :=
    (ZBasis (Fintype.card ι)).reindex (Fintype.equivFin ι).symm
  let ψ := UnitState.purifyMixture b w hw hs (fun i => (ρ i).purify)
  let χ := UnitState.purifyMixture b w hw hs φ
  have hi : inner ℂ ψ.val χ.val = (∑ i, w i * (ρ i).fidelity (σ i) : ℝ) := by
    rw [UnitState.inner_purifyMixture, Complex.ofReal_sum]
    simp only [he, Complex.ofReal_mul]
  have hb := norm_inner_le_fidelity
    (mixture w hw hs (fun i => pure (ρ i).purify))
    (mixture w hw hs (fun i => pure (φ i))) ψ χ
    (UnitState.partialTraceRight_pure_purifyMixture b w hw hs _)
    (UnitState.partialTraceRight_pure_purifyMixture b w hw hs _)
  rw [hi, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) ((ρ i).fidelity_nonneg _))]
    at hb
  have hm (τ : ι → UnitState (H ⊗ H)) :
      (mixture w hw hs (fun i => pure (τ i))).partialTraceRight =
        mixture w hw hs (fun i => (pure (τ i)).partialTraceRight) :=
    (QuantumChannel.partialTraceRight H H).map_mixture w hw hs _
  have hc := (mixture w hw hs (fun i => pure (ρ i).purify)).fidelity_le_partialTraceRight
    (mixture w hw hs (fun i => pure (φ i)))
  rw [hm, hm] at hc
  simp only [partialTraceRight_pure_purify, hφ] at hc
  exact hb.trans hc

/-- Joint concavity of unsquared fidelity under binary mixing with the same weight. -/
theorem mul_fidelity_add_le_fidelity_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ₀ ρ₁ σ₀ σ₁ : Density H) :
    p * ρ₀.fidelity σ₀ + (1 - p) * ρ₁.fidelity σ₁ ≤
      (mix p hp₀ hp₁ ρ₀ ρ₁).fidelity (mix p hp₀ hp₁ σ₀ σ₁) := by
  have hw : ∀ i : Fin 2, 0 ≤ ![p, 1 - p] i := by
    intro i
    fin_cases i
    · exact hp₀
    · exact sub_nonneg.mpr hp₁
  have hs : ∑ i : Fin 2, ![p, 1 - p] i = 1 := by simp
  have h := sum_mul_fidelity_le_fidelity_mixture ![p, 1 - p] hw hs ![ρ₀, ρ₁] ![σ₀, σ₁]
  rw [mixture_fin_two p hp₀ hp₁, mixture_fin_two p hp₀ hp₁] at h
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end

end Qudit.Density
