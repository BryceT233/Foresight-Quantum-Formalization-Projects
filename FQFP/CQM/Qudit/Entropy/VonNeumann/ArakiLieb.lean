/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the entropy triangle inequality.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/SSA.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.VonNeumann.Exchange
import FQFP.CQM.Qudit.State.Composite.Separable

/-!
# The Araki–Lieb inequality and its equality conditions

For any purification of a bipartite state on A and B with reference R, the bound
`S(A) - S(B) ≤ S(AB)` is saturated exactly when BR is a product. The opposite
signed bound is saturated exactly when AR is a product. At equal marginal entropies
the two conditions coincide, and saturation is equivalent to purity of the joint state.
The reference can have any dimension admitting the purification.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit

noncomputable section

variable {H K E R : Qudit}

/-- The environment entropy minus the output entropy attains the input entropy precisely
when the output and the purifying reference are independent. -/
lemma QuantumChannel.Dilation.entropy_complementary_sub_output_eq_iff
    {Φ : QuantumChannel H K} (d : Φ.Dilation E) (ρ : Density H)
    (ψ : UnitState (H ⊗ R)) (hψ : (Density.pure ψ).partialTraceRight = ρ) :
    (d.complementary.map ρ).vonNeumannEntropy - (Φ.map ρ).vonNeumannEntropy =
      ρ.vonNeumannEntropy ↔ (Φ.tensor (QuantumChannel.id R)).map (Density.pure ψ) =
        (Φ.map ρ).tensor (Density.pure ψ).partialTraceLeft := by
  have h := ((Φ.tensor (.id R)).map (Density.pure ψ)).vonNeumannEntropy_eq_add_marginals_iff
  rw [partialTraceRight_map_tensor, partialTraceLeft_map_tensor, map_id,
    ← Density.vonNeumannEntropy_partialTraceRight_eq_partialTraceLeft, hψ] at h
  rw [← hψ, d.entropy_complementary_eq_joint, sub_eq_iff_eq_add, add_comm, hψ]
  exact h

namespace Density

open QuantumChannel

/-- The Araki–Lieb inequality for finite-dimensional bipartite states. -/
lemma abs_sub_marginal_entropy_le (ρ : Density (H ⊗ K)) :
    |ρ.partialTraceRight.vonNeumannEntropy - ρ.partialTraceLeft.vonNeumannEntropy| ≤
      ρ.vonNeumannEntropy := by
  have h := (QuantumChannel.partialTraceRight H K).abs_coherentInfo_le ρ
  rwa [(partialTraceRightDilation H K).coherentInfo_eq, complementary_partialTraceRightDilation,
    map_partialTraceRight, map_partialTraceLeft] at h

/-- The signed bound with the left entropy first is saturated exactly when the
right subsystem and the purifying reference are independent. -/
lemma marginal_entropy_sub_eq_iff (ρ : Density (H ⊗ K))
    (ψ : UnitState ((H ⊗ K) ⊗ R)) (hψ : (pure ψ).partialTraceRight = ρ) :
    ρ.partialTraceRight.vonNeumannEntropy - ρ.partialTraceLeft.vonNeumannEntropy =
      ρ.vonNeumannEntropy ↔
      ((QuantumChannel.partialTraceLeft H K).tensor (.id R)).map (pure ψ) =
        ρ.partialTraceLeft.tensor (pure ψ).partialTraceLeft := by
  simpa only [Dilation.complementary_symm, complementary_partialTraceRightDilation,
    map_partialTraceRight, map_partialTraceLeft] using
    (partialTraceRightDilation H K).symm.entropy_complementary_sub_output_eq_iff ρ ψ hψ

/-- The signed bound with the right entropy first is saturated exactly when the
left subsystem and the purifying reference are independent. -/
lemma marginal_entropy_sub_rev_eq_iff (ρ : Density (H ⊗ K))
    (ψ : UnitState ((H ⊗ K) ⊗ R)) (hψ : (pure ψ).partialTraceRight = ρ) :
    ρ.partialTraceLeft.vonNeumannEntropy - ρ.partialTraceRight.vonNeumannEntropy =
      ρ.vonNeumannEntropy ↔
      ((QuantumChannel.partialTraceRight H K).tensor (.id R)).map (pure ψ) =
        ρ.partialTraceRight.tensor (pure ψ).partialTraceLeft := by
  simpa only [complementary_partialTraceRightDilation, map_partialTraceRight,
    map_partialTraceLeft] using
    (partialTraceRightDilation H K).entropy_complementary_sub_output_eq_iff ρ ψ hψ

/-- Equality in Araki–Lieb means the subsystem with smaller entropy and the reference
factor in any purification. Either signed criterion applies when the entropies coincide. -/
lemma abs_sub_marginal_entropy_eq_iff (ρ : Density (H ⊗ K))
    (ψ : UnitState ((H ⊗ K) ⊗ R)) (hψ : (pure ψ).partialTraceRight = ρ) :
    |ρ.partialTraceRight.vonNeumannEntropy - ρ.partialTraceLeft.vonNeumannEntropy| =
      ρ.vonNeumannEntropy ↔
      if ρ.partialTraceLeft.vonNeumannEntropy ≤ ρ.partialTraceRight.vonNeumannEntropy then
        ((QuantumChannel.partialTraceLeft H K).tensor (.id R)).map (pure ψ) =
          ρ.partialTraceLeft.tensor (pure ψ).partialTraceLeft
      else
        ((QuantumChannel.partialTraceRight H K).tensor (.id R)).map (pure ψ) =
          ρ.partialTraceRight.tensor (pure ψ).partialTraceLeft := by
  split_ifs with h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact ρ.marginal_entropy_sub_eq_iff ψ hψ
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    exact ρ.marginal_entropy_sub_rev_eq_iff ψ hψ

/-- A state has zero entropy exactly when it is pure. At zero entropy its purification
has zero mutual information, so it factors across the system and the reference. -/
lemma vonNeumannEntropy_eq_zero_iff (ρ : Density H) : ρ.vonNeumannEntropy = 0 ↔ ρ.IsPure := by
  refine ⟨fun h => ?_, IsPure.vonNeumannEntropy_eq_zero⟩
  have hI : (pure ρ.purify).mutualInfo = 0 := by
    rw [mutualInfo_pure, partialTraceRight_pure_purify, h, mul_zero]
  have hsep : (pure ρ.purify).IsSeparable := by
    rw [(pure ρ.purify).mutualInfo_eq_zero_iff.mp hI]
    exact isSeparable_tensor _ _
  simpa only [partialTraceRight_pure_purify] using
    (isSeparable_pure_iff_isPure_partialTraceRight ρ.purify).mp hsep

/-- With equal marginal entropies, Araki–Lieb is saturated exactly for pure joint states. -/
lemma abs_sub_marginal_entropy_eq_iff_isPure_of_eq (ρ : Density (H ⊗ K))
    (h : ρ.partialTraceRight.vonNeumannEntropy = ρ.partialTraceLeft.vonNeumannEntropy) :
    |ρ.partialTraceRight.vonNeumannEntropy - ρ.partialTraceLeft.vonNeumannEntropy| =
      ρ.vonNeumannEntropy ↔ ρ.IsPure := by
  rw [h, sub_self, abs_zero, eq_comm, vonNeumannEntropy_eq_zero_iff]

end Density

end

end Qudit
