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

/-- Categorical compatibility means that one channel has the two prescribed partial traces. -/
theorem compatible_iff_exists_joint_channel (Φ : QuantumChannel H K) (Γ : QuantumChannel H L) :
    CQM.Compatible Φ.asHom Γ.asHom ↔ ∃ Ψ : QuantumChannel H (K ⊗ L),
      (partialTraceRight K L).comp Ψ = Φ ∧ (partialTraceLeft K L).comp Ψ = Γ :=
  exists_congr fun _ => hasMarginals_iff

/-- With zero-dimensional input the chosen environment also has dimension zero, so its
complement can simulate any channel on the same input. -/
lemma complementary_isDegradableTo_of_finrank_eq_zero (Φ : QuantumChannel H K)
    (Γ : QuantumChannel H L) (hH : Module.finrank ℂ H.state = 0) :
    Φ.complementary.IsDegradableTo Γ := by
  have : Subsingleton H.state := Module.finrank_zero_iff.mp hH
  obtain ⟨D⟩ := (nonempty_iff_finrank_pos
    (std (Module.finrank ℂ K.state * Module.finrank ℂ H.state)) L).mpr (by simp [hH])
  exact ⟨D, QuantumChannel.ext (Subsingleton.elim _ _)⟩

/-- Every channel with zero-dimensional input is antidegradable. -/
lemma isAntidegradable_of_finrank_eq_zero (Φ : QuantumChannel H K)
    (hH : Module.finrank ℂ H.state = 0) : Φ.IsAntidegradable :=
  Φ.complementary_isDegradableTo_of_finrank_eq_zero Φ hH

namespace Dilation

variable {Ψ : QuantumChannel H (K ⊗ L)}

/-- Regard the second output of a joint channel as part of the Stinespring environment. -/
def marginal (d : Ψ.Dilation E) :
    ((partialTraceRight K L).comp Ψ).Dilation (L ⊗ E) where
  toHom := d.toHom ≫ (α_ K L E).hom
  isIsometry := inferInstance
  channel_eq := by
    change _ = ((partialTraceRight K (L ⊗ E)).comp
      (ofIsometry (d.toHom ≫ (α_ K L E).hom))).toSuperoperator
    rw [ofIsometry_comp, ← comp_assoc, partialTraceRight_comp_associator, comp_assoc,
      ← d.channel_eq_comp]

/-- Tracing out the original environment from the marginal dilation's complement gives the
second marginal channel, on all input operators. -/
lemma partialTraceRight_comp_complementary_marginal (d : Ψ.Dilation E) :
    (partialTraceRight L E).comp d.marginal.complementary = (partialTraceLeft K L).comp Ψ := by
  change (partialTraceRight L E).comp ((partialTraceLeft K (L ⊗ E)).comp
    (ofIsometry (d.toHom ≫ (α_ K L E).hom))) = _
  rw [ofIsometry_comp, ← comp_assoc (partialTraceLeft K (L ⊗ E)),
    partialTraceLeft_comp_associator, ← comp_assoc, partialTraceRight_comp_tensor,
    comp_assoc, ← d.channel_eq_comp]

end Dilation

/-- Compatibility with a channel is equivalent to postprocessing its complementary output.
The standard environment has dimension zero for a zero-dimensional input. -/
theorem compatible_iff_complementary_isDegradableTo (Φ : QuantumChannel H K)
    (Γ : QuantumChannel H L) :
    CQM.Compatible Φ.asHom Γ.asHom ↔ Φ.complementary.IsDegradableTo Γ := by
  constructor
  · intro h
    obtain ⟨Ψ, rfl, hl⟩ := (compatible_iff_exists_joint_channel Φ Γ).mp h
    let d := Ψ.dilation.marginal
    by_cases hH : 0 < Module.finrank ℂ H.state
    · have h := (d.mutuallyDegradable_complementary
        ((partialTraceRight K L).comp Ψ).dilation hH).2
      exact h.trans ⟨partialTraceRight L _,
        Ψ.dilation.partialTraceRight_comp_complementary_marginal.trans hl⟩
    · exact complementary_isDegradableTo_of_finrank_eq_zero _ Γ (by lia)
  · intro h
    have hj : CQM.Compatible Φ.asHom Φ.complementary.asHom :=
      ⟨_, Φ.dilation.hasMarginals⟩
    exact hj.postprocess (CQM.IsDegradableTo.refl _) h

/-- Simulating the other channel from the complementary output is a symmetric test. -/
theorem complementary_isDegradableTo_comm (Φ : QuantumChannel H K) (Γ : QuantumChannel H L) :
    Φ.complementary.IsDegradableTo Γ ↔ Γ.complementary.IsDegradableTo Φ := by
  rw [← compatible_iff_complementary_isDegradableTo, ← compatible_iff_complementary_isDegradableTo]
  exact ⟨CQM.Compatible.symm, CQM.Compatible.symm⟩

/-- A channel has a joint extension with two copies of its marginal exactly when it is
antidegradable. The two outputs of the extension can be correlated. -/
theorem compatible_self_iff_isAntidegradable (Φ : QuantumChannel H K) :
    CQM.Compatible Φ.asHom Φ.asHom ↔ Φ.IsAntidegradable :=
  compatible_iff_complementary_isDegradableTo Φ Φ

/-- One measurement can serve two recipients by preparing a product of their chosen
states for each outcome. The two output systems may have different dimensions. -/
theorem compatible_measurePrepare {ι : Type*} [Fintype ι] (M : POVM H ι)
    (σ : ι → Density K) (τ : ι → Density L) :
    CQM.Compatible (M.measurePrepare σ).asHom (M.measurePrepare τ).asHom := by
  apply (compatible_iff_exists_joint_channel _ _).mpr
  refine ⟨M.measurePrepare (fun i => (σ i).tensor (τ i)), ?_, ?_⟩
  · simp only [POVM.comp_measurePrepare, map_partialTraceRight, Density.partialTraceRight_tensor]
  · simp only [POVM.comp_measurePrepare, map_partialTraceLeft, Density.partialTraceLeft_tensor]

/-- The joint preparation for two recipients also witnesses antidegradability when both
recipients request the same states. -/
theorem isAntidegradable_measurePrepare {ι : Type*} [Fintype ι] (M : POVM H ι)
    (σ : ι → Density K) : (M.measurePrepare σ).IsAntidegradable :=
  (compatible_self_iff_isAntidegradable _).mp (compatible_measurePrepare M σ σ)

/-- A joint channel with two identical marginals provides an antidegrading channel. -/
theorem isAntidegradable_of_joint_channel (Φ : QuantumChannel H K)
    (Ψ : QuantumChannel H (K ⊗ K))
    (hr : (partialTraceRight K K).comp Ψ = Φ) (hl : (partialTraceLeft K K).comp Ψ = Φ) :
    Φ.IsAntidegradable := by
  exact (compatible_self_iff_isAntidegradable Φ).mp
    ((compatible_iff_exists_joint_channel Φ Φ).mpr ⟨Ψ, hr, hl⟩)

end

end Qudit.QuantumChannel
