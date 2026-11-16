/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.RelativeTensor

/-!
# Mutual information and subadditivity

Mutual information is relative entropy to the product of the marginals. Klein's inequality
therefore gives subadditivity and the upper bound on conditional entropy. Singular marginals
are included; no invalid global identity for the logarithm of a singular tensor is used.

## Main results

* `Qudit.Density.relativeEntropy_tensor_marginals`: mutual information as relative entropy.
* `Qudit.Density.mutualInfo_nonneg`: nonnegativity of mutual information.
* `Qudit.Density.vonNeumannEntropy_le_add_marginals`: subadditivity of von Neumann entropy.
* `Qudit.Density.conditionalEntropy_le_entropy`: conditioning bounds entropy by the marginal
  entropy.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- The finite relative-entropy expression to the product of marginals is mutual information. -/
lemma relativeEntropyReal_tensor_marginals (ρ : Density (H ⊗ K)) :
    ρ.relativeEntropyReal (ρ.partialTraceRight.tensor ρ.partialTraceLeft) = ρ.mutualInfo := by
  rw [relativeEntropyReal_eq_neg_entropy_sub,
    expectation_logOp_tensor _ _ _ ρ.absolutelyContinuous_tensor_marginals,
    expectation_logOp_self, expectation_logOp_self, mutualInfo]
  ring

/-- Quantum mutual information is nonnegative for all bipartite states. -/
lemma mutualInfo_nonneg (ρ : Density (H ⊗ K)) : 0 ≤ ρ.mutualInfo := by
  rw [← relativeEntropyReal_tensor_marginals]
  exact ρ.relativeEntropyReal_nonneg _ ρ.absolutelyContinuous_tensor_marginals

/-- Mutual information is relative entropy to the product of the marginals. -/
lemma relativeEntropy_tensor_marginals (ρ : Density (H ⊗ K)) :
    ρ.relativeEntropy (ρ.partialTraceRight.tensor ρ.partialTraceLeft) =
      ENNReal.ofReal ρ.mutualInfo := by
  rw [relativeEntropy, ite_eq_left ρ.absolutelyContinuous_tensor_marginals,
    relativeEntropyReal_tensor_marginals]

/-- Von Neumann entropy is subadditive for arbitrary bipartite states. -/
lemma vonNeumannEntropy_le_add_marginals (ρ : Density (H ⊗ K)) :
    ρ.vonNeumannEntropy ≤
      ρ.partialTraceRight.vonNeumannEntropy + ρ.partialTraceLeft.vonNeumannEntropy :=
  sub_nonneg.mp ρ.mutualInfo_nonneg

/-- Conditioning cannot increase quantum entropy. -/
lemma conditionalEntropy_le_entropy (ρ : Density (H ⊗ K)) :
    ρ.conditionalEntropy ≤ ρ.partialTraceRight.vonNeumannEntropy := by
  have h := ρ.vonNeumannEntropy_le_add_marginals
  unfold conditionalEntropy
  linarith

end

end Qudit.Density
