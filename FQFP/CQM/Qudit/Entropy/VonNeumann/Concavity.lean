/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative

/-!
# Concavity of von Neumann entropy

The entropy gained by mixing is the average relative entropy to the mixture.
Support inclusion of positive-weight components and Klein's inequality prove concavity
for arbitrary densities, including singular states and mixing probabilities zero and one.

## Main results

* `Qudit.Density.relativeEntropyReal_mix_eq_entropy_gap`: relative entropy measures the mixing gap.
* `Qudit.Density.mul_vonNeumannEntropy_add_le`: concavity under arbitrary binary mixtures.
-/

@[expose] public section

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- The entropy of mixing equals the weighted finite relative-entropy expressions. -/
lemma relativeEntropyReal_mix_eq_entropy_gap (ρ σ : Density H)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    p * ρ.relativeEntropyReal (mix p hp₀ hp₁ ρ σ) +
      (1 - p) * σ.relativeEntropyReal (mix p hp₀ hp₁ ρ σ) =
    (mix p hp₀ hp₁ ρ σ).vonNeumannEntropy -
      (p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy) := by
  have he := expectation_mix p hp₀ hp₁ ρ σ (mix p hp₀ hp₁ ρ σ).logOp
  rw [expectation_logOp_self] at he
  rw [relativeEntropyReal_eq_neg_entropy_sub, relativeEntropyReal_eq_neg_entropy_sub]
  linear_combination he

/-- Von Neumann entropy is concave under arbitrary binary mixtures. -/
lemma mul_vonNeumannEntropy_add_le (ρ σ : Density H)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    p * ρ.vonNeumannEntropy + (1 - p) * σ.vonNeumannEntropy ≤
      (mix p hp₀ hp₁ ρ σ).vonNeumannEntropy := by
  by_cases h₀ : p = 0
  · subst p
    simp
  by_cases h₁ : p = 1
  · subst p
    simp
  rw [← sub_nonneg, ← relativeEntropyReal_mix_eq_entropy_gap]
  exact add_nonneg
    (mul_nonneg hp₀ (ρ.relativeEntropyReal_nonneg _
      (ρ.absolutelyContinuous_mix_left σ p (lt_of_le_of_ne hp₀ (Ne.symm h₀)) hp₁)))
    (mul_nonneg (sub_nonneg.mpr hp₁) (σ.relativeEntropyReal_nonneg _
      (ρ.absolutelyContinuous_mix_right σ p hp₀ (lt_of_le_of_ne hp₁ h₁))))

end

end Qudit.Density
