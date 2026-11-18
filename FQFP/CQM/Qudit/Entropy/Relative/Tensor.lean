/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Composite
public import FQFP.CQM.Qudit.State.Composite.Support

/-!
# Relative entropy of tensor products

The supported logarithm splits in expectation. Relative entropy is additive under independent
tensor products, including infinite values. Singular operators are included without asserting
an invalid global tensor-logarithm identity on their kernels.

## Main results

* `Qudit.Density.expectation_logOp_tensor`: the supported tensor logarithm splits in expectation.
* `Qudit.Density.relativeEntropy_tensor`: additivity of relative entropy, including infinite values.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- On a supported state, the logarithm of a product splits into the two local expectations. -/
lemma expectation_logOp_tensor (ρ : Density (H ⊗ K)) (σ : Density H) (τ : Density K)
    (h : ρ.AbsolutelyContinuous (σ.tensor τ)) :
    ρ.expectation (σ.tensor τ).logOp =
      ρ.partialTraceRight.expectation σ.logOp + ρ.partialTraceLeft.expectation τ.logOp := by
  let b := σ.eigenbasis.tensorProduct τ.eigenbasis
  have ht (i) : (σ.tensor τ).op (b i) =
      (↑(σ.eigenvalue i.1 * τ.eigenvalue i.2) : ℂ) • b i :=
    σ.tensor_apply_eigenbasis τ i
  have hl (i) : Operator.tensor σ.logOp (1 : Operator K) (b i) =
      (Real.log (σ.eigenvalue i.1) : ℂ) • b i := by
    rcases i with ⟨i, j⟩
    simp only [b, OrthonormalBasis.tensorProduct_apply, Operator.tensor_apply,
      σ.logOp_apply_of_eigenvector (σ.apply_eigenbasis i), Module.End.one_apply,
      ← TensorProduct.smul_tmul']
  have hr (i) : Operator.tensor (1 : Operator H) τ.logOp (b i) =
      (Real.log (τ.eigenvalue i.2) : ℂ) • b i := by
    rcases i with ⟨i, j⟩
    simp only [b, OrthonormalBasis.tensorProduct_apply, Operator.tensor_apply,
      τ.logOp_apply_of_eigenvector (τ.apply_eigenbasis j), Module.End.one_apply,
      TensorProduct.tmul_smul]
  rw [expectation_partialTraceRight, expectation_partialTraceLeft,
    ρ.expectation_eq_sum_of_diagonal b _ _ (fun i =>
      (σ.tensor τ).logOp_apply_of_eigenvector (ht i)),
    ρ.expectation_eq_sum_of_diagonal b _ _ hl,
    ρ.expectation_eq_sum_of_diagonal b _ _ hr, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : σ.eigenvalue i.1 * τ.eigenvalue i.2 = 0
  · have hb := (absolutelyContinuous_iff_of_right_eigenbasis ρ _ b _ ht).mp h i hz
    simp only [hb, inner_zero_right, Complex.zero_re, mul_zero, add_zero]
  · rw [Real.log_mul (mul_ne_zero_iff.mp hz).1 (mul_ne_zero_iff.mp hz).2, add_mul]

/-- The finite trace expression is additive when both pairs satisfy support inclusion. -/
lemma relativeEntropyReal_tensor (ρ σ : Density H) (τ ω : Density K)
    (hρ : ρ.AbsolutelyContinuous σ) (hτ : τ.AbsolutelyContinuous ω) :
    (ρ.tensor τ).relativeEntropyReal (σ.tensor ω) =
      ρ.relativeEntropyReal σ + τ.relativeEntropyReal ω := by
  rw [relativeEntropyReal_eq_neg_entropy_sub,
    expectation_logOp_tensor _ _ _ (hρ.tensor hτ), vonNeumannEntropy_tensor,
    partialTraceRight_tensor, partialTraceLeft_tensor,
    relativeEntropyReal_eq_neg_entropy_sub, relativeEntropyReal_eq_neg_entropy_sub]
  ring

/-- Quantum relative entropy is additive on tensor products, including infinite values. -/
lemma relativeEntropy_tensor (ρ σ : Density H) (τ ω : Density K) :
    (ρ.tensor τ).relativeEntropy (σ.tensor ω) = ρ.relativeEntropy σ + τ.relativeEntropy ω := by
  classical
  by_cases hρ : ρ.AbsolutelyContinuous σ
  · by_cases hτ : τ.AbsolutelyContinuous ω
    · rw [relativeEntropy, ite_eq_left (hρ.tensor hτ),
        relativeEntropyReal_tensor ρ σ τ ω hρ hτ,
        ENNReal.ofReal_add (ρ.relativeEntropyReal_nonneg σ hρ) (τ.relativeEntropyReal_nonneg ω hτ)]
      simp only [relativeEntropy, hρ, hτ, reduceIte]
    · have ht : ¬(ρ.tensor τ).AbsolutelyContinuous (σ.tensor ω) :=
        fun h => hτ ((absolutelyContinuous_tensor_iff _ _ _ _).mp h).2
      rw [(relativeEntropy_eq_top_iff _ _).mpr ht, (relativeEntropy_eq_top_iff τ ω).mpr hτ]
      simp
  · have ht : ¬(ρ.tensor τ).AbsolutelyContinuous (σ.tensor ω) :=
      fun h => hρ ((absolutelyContinuous_tensor_iff _ _ _ _).mp h).1
    rw [(relativeEntropy_eq_top_iff _ _).mpr ht, (relativeEntropy_eq_top_iff ρ σ).mpr hρ]
    simp

end

end Qudit.Density
