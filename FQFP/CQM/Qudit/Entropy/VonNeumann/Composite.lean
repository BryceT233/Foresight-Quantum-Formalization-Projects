/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for marginal entropies and information quantities.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/VonNeumann.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Basic
public import FQFP.CQM.Qudit.State.Composite.Schmidt

/-!
# Entropy of composite systems

Independent tensor products have additive entropy. The two marginals of a pure state
have the same entropy, including for unequal dimensions and singular marginals.
Conditional entropy means `S(left | right)`; mutual information and conditional mutual
information use natural logarithms as well. Conditional entropy can be negative.

## Main definitions and results

* `Qudit.Density.conditionalEntropy`: conditional entropy of the left system given the right.
* `Qudit.Density.mutualInfo`: mutual information of a bipartite state.
* `Qudit.Density.conditionalMutualInfo`: conditional mutual information of three systems.
* `Qudit.Density.vonNeumannEntropy_tensor`: entropy is additive on independent tensor products.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H K L : Qudit}

/-- Entropy is additive on independent tensor products. -/
lemma vonNeumannEntropy_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).vonNeumannEntropy = ρ.vonNeumannEntropy + σ.vonNeumannEntropy := by
  rw [vonNeumannEntropy_eq_sum_of_eigenbasis (ρ.tensor σ)
    (ρ.eigenbasis.tensorProduct σ.eigenbasis)
    (fun i ↦ ρ.eigenvalue i.1 * σ.eigenvalue i.2) (ρ.tensor_apply_eigenbasis σ)]
  simp only [Fintype.sum_prod_type, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, ρ.sum_eigenvalue, σ.sum_eigenvalue,
    one_mul, vonNeumannEntropy_eq_sum]

/-- Pure bipartite states have marginals with the same entropy. -/
lemma vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft (ψ : UnitState (H ⊗ K)) :
    (pure ψ).partialTraceRight.vonNeumannEntropy = (pure ψ).partialTraceLeft.vonNeumannEntropy :=
  vonNeumannEntropy_eq_of_nonzeroEigenvalues_eq _ _
    (nonzeroEigenvalues_partialTraceRight_eq_partialTraceLeft ψ)

/-- Marginal entropy equality also applies to densities known to be pure. -/
lemma IsPure.vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft
    {ρ : Density (H ⊗ K)} (hρ : ρ.IsPure) :
    ρ.partialTraceRight.vonNeumannEntropy = ρ.partialTraceLeft.vonNeumannEntropy := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact Density.vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft ψ

/-- Quantum conditional entropy `S(H | K) = S(HK) - S(K)`, in nats. -/
def conditionalEntropy (ρ : Density (H ⊗ K)) : ℝ :=
  ρ.vonNeumannEntropy - ρ.partialTraceLeft.vonNeumannEntropy

/-- Quantum mutual information `I(H : K)`, in nats. -/
def mutualInfo (ρ : Density (H ⊗ K)) : ℝ :=
  ρ.partialTraceRight.vonNeumannEntropy + ρ.partialTraceLeft.vonNeumannEntropy -
    ρ.vonNeumannEntropy

/-- Quantum conditional mutual information `I(H : L | K)`, in nats. -/
def conditionalMutualInfo (ρ : Density (H ⊗ (K ⊗ L))) : ℝ :=
  (ρ.map (α_ H K L).inv).partialTraceRight.vonNeumannEntropy +
    ρ.partialTraceLeft.vonNeumannEntropy - ρ.vonNeumannEntropy -
      ρ.partialTraceLeft.partialTraceRight.vonNeumannEntropy

/-- Mutual information is the reduction in entropy obtained by conditioning. -/
lemma mutualInfo_eq_sub_conditionalEntropy (ρ : Density (H ⊗ K)) :
    ρ.mutualInfo = ρ.partialTraceRight.vonNeumannEntropy - ρ.conditionalEntropy := by
  unfold mutualInfo conditionalEntropy
  ring

/-- Conditioning on an independent system leaves the entropy unchanged. -/
@[simp]
lemma conditionalEntropy_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).conditionalEntropy = ρ.vonNeumannEntropy := by
  simp [conditionalEntropy, vonNeumannEntropy_tensor, partialTraceLeft_tensor]

/-- Independent systems have zero mutual information. -/
@[simp]
lemma mutualInfo_tensor (ρ : Density H) (σ : Density K) : (ρ.tensor σ).mutualInfo = 0 := by
  simp [mutualInfo, vonNeumannEntropy_tensor, partialTraceRight_tensor, partialTraceLeft_tensor]

/-- The conditional entropy of a pure state is minus the entropy of its right marginal. -/
lemma conditionalEntropy_pure (ψ : UnitState (H ⊗ K)) :
    (pure ψ).conditionalEntropy = -(pure ψ).partialTraceLeft.vonNeumannEntropy := by
  simp [conditionalEntropy]

/-- Pure-state mutual information is twice the entropy of either marginal. -/
lemma mutualInfo_pure (ψ : UnitState (H ⊗ K)) :
    (pure ψ).mutualInfo = 2 * (pure ψ).partialTraceRight.vonNeumannEntropy := by
  rw [mutualInfo, ← vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft,
    vonNeumannEntropy_pure]
  ring

end

end Qudit.Density
