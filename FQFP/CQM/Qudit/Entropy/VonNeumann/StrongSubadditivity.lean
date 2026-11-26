/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for strong subadditivity and conditional mutual information.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/SSA.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Composite
public import FQFP.CQM.Qudit.Entropy.Relative.PartialTrace
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Subadditivity

/-!
# Strong subadditivity of von Neumann entropy

For a state on `A ⊗ (B ⊗ C)`, discarding `C` decreases the relative entropy to
`ρA ⊗ ρBC`. The product reference reduces to `ρA ⊗ ρB`, so this is precisely
`I(A : B) ≤ I(A : BC)`. Expanding the entropies gives strong subadditivity and
nonnegativity of the conditional mutual information `I(A : C | B)`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit.Density

noncomputable section

variable {H K L : Qudit}

/-- The middle marginal is the same whether we discard the first or the last factor first. -/
lemma partialTraceLeft_partialTraceRight_map_associator_inv (ρ : Density (H ⊗ (K ⊗ L))) :
    (ρ.map (α_ H K L).inv).partialTraceRight.partialTraceLeft =
      ρ.partialTraceLeft.partialTraceRight := by
  rw [QuantumChannel.partialTraceRight_map_associator_inv,
    QuantumChannel.partialTraceLeft_map_tensor, QuantumChannel.map_partialTraceRight]

/-- Discarding the last factor decreases the mutual information with the first factor. -/
lemma mutualInfo_partialTraceRight_le (ρ : Density (H ⊗ (K ⊗ L))) :
    (ρ.map (α_ H K L).inv).partialTraceRight.mutualInfo ≤ ρ.mutualInfo := by
  let U := (α_ H K L).inv
  let σ := ρ.partialTraceRight.tensor ρ.partialTraceLeft
  have hs := (absolutelyContinuous_map_iff ρ σ U).mpr ρ.absolutelyContinuous_tensor_marginals
  have h := relativeEntropyReal_partialTraceRight_le (ρ.map U) (σ.map U) hs
  rw [relativeEntropyReal_map_unitary, relativeEntropyReal_tensor_marginals] at h
  have href : (σ.map U).partialTraceRight =
      (ρ.map U).partialTraceRight.partialTraceRight.tensor
        (ρ.map U).partialTraceRight.partialTraceLeft := by
    simp only [σ, U, QuantumChannel.partialTraceRight_map_associator_inv,
      QuantumChannel.map_tensor, QuantumChannel.partialTraceRight_map_tensor,
      QuantumChannel.partialTraceLeft_map_tensor, QuantumChannel.map_id,
      QuantumChannel.map_partialTraceRight]
  rwa [href, relativeEntropyReal_tensor_marginals] at h

/-- **Strong subadditivity**: `S(ABC) + S(B) ≤ S(AB) + S(BC)` for every tripartite state. -/
theorem vonNeumannEntropy_strongSubadditivity (ρ : Density (H ⊗ (K ⊗ L))) :
    ρ.vonNeumannEntropy + ρ.partialTraceLeft.partialTraceRight.vonNeumannEntropy ≤
      (ρ.map (α_ H K L).inv).partialTraceRight.vonNeumannEntropy +
        ρ.partialTraceLeft.vonNeumannEntropy := by
  have h := ρ.mutualInfo_partialTraceRight_le
  rw [mutualInfo, mutualInfo, partialTraceLeft_partialTraceRight_map_associator_inv] at h
  rw [QuantumChannel.partialTraceRight_map_associator_inv,
    QuantumChannel.partialTraceRight_map_tensor, QuantumChannel.map_id] at h
  rw [QuantumChannel.partialTraceRight_map_associator_inv]
  linarith

/-- Conditioning on both `K` and `L` gives at most the entropy conditioned on `K` alone. -/
lemma conditionalEntropy_le_partialTraceRight (ρ : Density (H ⊗ (K ⊗ L))) :
    ρ.conditionalEntropy ≤ (ρ.map (α_ H K L).inv).partialTraceRight.conditionalEntropy := by
  rw [conditionalEntropy, conditionalEntropy, partialTraceLeft_partialTraceRight_map_associator_inv]
  linarith [ρ.vonNeumannEntropy_strongSubadditivity]

/-- Quantum conditional mutual information is nonnegative, including for singular marginals. -/
theorem conditionalMutualInfo_nonneg (ρ : Density (H ⊗ (K ⊗ L))) :
    0 ≤ ρ.conditionalMutualInfo := by
  unfold conditionalMutualInfo
  linarith [ρ.vonNeumannEntropy_strongSubadditivity]

end

end Qudit.Density
