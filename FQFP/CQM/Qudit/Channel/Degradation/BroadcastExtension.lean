/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.DilationIndependence

/-!
# Joint channel extensions and antidegradability

In a Stinespring dilation of a joint channel, retaining the first output leaves the second
one inside the environment. If the two marginal channels agree, this gives an antidegrading
channel. The chosen standard complement also covers zero-dimensional inputs.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K L E : Qudit}

/-- With zero-dimensional input, the chosen Stinespring environment has dimension zero,
so every channel is antidegradable. -/
lemma isAntidegradable_of_finrank_eq_zero (Φ : QuantumChannel H K)
    (hH : Module.finrank ℂ H.state = 0) : Φ.IsAntidegradable := by
  have : Subsingleton H.state := Module.finrank_zero_iff.mp hH
  obtain ⟨D⟩ := (nonempty_iff_finrank_pos
    (std (Module.finrank ℂ K.state * Module.finrank ℂ H.state)) K).mpr (by simp [hH])
  exact ⟨D, QuantumChannel.ext (Subsingleton.elim _ _)⟩

namespace Dilation

variable {Ψ : QuantumChannel H (K ⊗ L)}

/-- Regard the second output of a joint channel as part of the Stinespring environment. -/
def marginal (d : Ψ.Dilation E) :
    ((partialTraceRight K L).comp Ψ).Dilation (L ⊗ E) where
  toHom := d.toHom ≫ (α_ K L E).hom
  isIsometry := inferInstance
  channel_eq := by
    change Operator.partialTraceRight ∘ₗ Ψ.toSuperoperator = _
    rw [hom_comp, Superoperator.conjugate_comp, hom_hom_associator,
      ← TensorProduct.toLinearEquiv_assocIsometry,
      ← Superoperator.relabel_eq_conjugate (H := (K ⊗ L) ⊗ E) (K := K ⊗ (L ⊗ E))
        (TensorProduct.assocIsometry ℂ K.state L.state E.state),
      ← LinearMap.comp_assoc, Superoperator.partialTraceRight_relabel_assoc,
      LinearMap.comp_assoc, ← d.channel_eq]

/-- Tracing out the original environment from the marginal dilation's complement gives the
second marginal channel, on all input operators. -/
lemma partialTraceRight_comp_complementary_marginal (d : Ψ.Dilation E) :
    (partialTraceRight L E).comp d.marginal.complementary = (partialTraceLeft K L).comp Ψ := by
  apply QuantumChannel.ext
  change Operator.partialTraceRight ∘ₗ Operator.partialTraceLeft ∘ₗ
    Superoperator.conjugate (d.toHom ≫ (α_ K L E).hom).hom =
      Operator.partialTraceLeft ∘ₗ Ψ.toSuperoperator
  rw [hom_comp, Superoperator.conjugate_comp, hom_hom_associator,
    ← TensorProduct.toLinearEquiv_assocIsometry,
    ← Superoperator.relabel_eq_conjugate (H := (K ⊗ L) ⊗ E) (K := K ⊗ (L ⊗ E))
      (TensorProduct.assocIsometry ℂ K.state L.state E.state)]
  conv_lhs =>
    arg 2
    rw [← LinearMap.comp_assoc, Superoperator.partialTraceLeft_relabel_assoc]
  rw [← LinearMap.comp_assoc, Superoperator.partialTraceRight_tensor_id,
    LinearMap.comp_assoc, ← d.channel_eq]

end Dilation

/-- A joint channel with two identical marginals provides an antidegrading channel. -/
theorem isAntidegradable_of_joint_channel (Φ : QuantumChannel H K)
    (Ψ : QuantumChannel H (K ⊗ K))
    (hr : (partialTraceRight K K).comp Ψ = Φ) (hl : (partialTraceLeft K K).comp Ψ = Φ) :
    Φ.IsAntidegradable := by
  by_cases hH : 0 < Module.finrank ℂ H.state
  · rw [← hr]
    apply (Ψ.dilation.marginal.isAntidegradable_iff hH).mpr
    exact ⟨partialTraceRight K _, Ψ.dilation.partialTraceRight_comp_complementary_marginal.trans
      (hl.trans hr.symm)⟩
  · exact isAntidegradable_of_finrank_eq_zero Φ (by lia)

end

end Qudit.QuantumChannel
