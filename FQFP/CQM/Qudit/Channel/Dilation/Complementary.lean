/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the complementary channel.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Dilation.Basic
public import FQFP.CQM.Qudit.Channel.Composite

/-!
# Complementary quantum channels

A dilation records an isometry and its channel identity on all operators. Its complementary
channel retains the environment instead of the original output. `dilation` selects a dilation
with environment dimension `dim(output) * dim(input)`; `complementary` uses this choice.
The explicit `Dilation.complementary` interface also works with other environment dimensions.
No nonzero-dimension assumption is required.

## Main definitions and results

* `Qudit.QuantumChannel.Dilation`: a channel realized by an isometry and a right partial trace.
* `Qudit.QuantumChannel.Dilation.complementary`: the environment output for a specified dilation.
* `Qudit.QuantumChannel.complementary`: the complement from the chosen standard dilation.
* `Qudit.QuantumChannel.Dilation.complementary_symm`: the double complement recovers the channel.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K E : Qudit}

/-- A Stinespring isometry realizing a channel by discarding the right environment. -/
structure Dilation (Φ : QuantumChannel H K) (E : Qudit) where
  /-- The isometry from the input into output and environment. -/
  toHom : H ⟶ K ⊗ E
  /-- The dilation preserves vector inner products. -/
  isIsometry : IsIsometry toHom
  /-- Discarding the environment gives the channel on every operator. -/
  channel_eq : Φ.toSuperoperator =
    (Operator.partialTraceRight : Superoperator (K ⊗ E) K) ∘ₗ
      Superoperator.conjugate toHom.hom

attribute [instance] Dilation.isIsometry

namespace Dilation

variable {Φ : QuantumChannel H K}

/-- The channel retaining the environment of this particular dilation. -/
def complementary (d : Φ.Dilation E) : QuantumChannel H E :=
  (partialTraceLeft K E).comp (ofIsometry d.toHom)

/-- Discarding the environment of a dilation recovers the bundled channel. -/
lemma channel_eq_comp (d : Φ.Dilation E) :
    Φ = (partialTraceRight K E).comp (ofIsometry d.toHom) :=
  QuantumChannel.ext d.channel_eq

/-- The isometric realization has the channel and its complement as its two marginals. -/
lemma hasMarginals (d : Φ.Dilation E) :
    CQM.HasMarginals (ofIsometry d.toHom).asHom Φ.asHom d.complementary.asHom :=
  hasMarginals_iff.mpr ⟨d.channel_eq_comp.symm, rfl⟩

/-- A dilation realizes the output density by its right partial trace. -/
lemma map_eq_partialTraceRight (d : Φ.Dilation E) (ρ : Density H) :
    Φ.map ρ = (ρ.map d.toHom).partialTraceRight :=
  Density.ext (LinearMap.congr_fun d.channel_eq ρ.op)

/-- The complementary output density is the left partial trace of the joint output. -/
lemma map_complementary (d : Φ.Dilation E) (ρ : Density H) :
    d.complementary.map ρ = (ρ.map d.toHom).partialTraceLeft := rfl

/-- Swapping the isometry's outputs realizes the complementary marginal first. -/
lemma hasMarginals_swap (d : Φ.Dilation E) :
    CQM.HasMarginals (ofIsometry (d.toHom ≫ (β_ K E).hom)).asHom d.complementary.asHom Φ.asHom := by
  rw [ofIsometry_comp]
  exact d.hasMarginals.swap

/-- Swapping the two outputs gives a dilation of the complementary channel. -/
def symm (d : Φ.Dilation E) : d.complementary.Dilation K where
  toHom := d.toHom ≫ (β_ K E).hom
  isIsometry := inferInstance
  channel_eq := congrArg QuantumChannel.toSuperoperator
    (hasMarginals_iff.mp d.hasMarginals_swap).1.symm

/-- For a fixed dilation, taking the complementary channel twice recovers the original. -/
lemma complementary_symm (d : Φ.Dilation E) : d.symm.complementary = Φ :=
  (hasMarginals_iff.mp d.hasMarginals_swap).2

/-- Lift a dilation to an input with a reference system, grouped with the environment. -/
def lift (d : Φ.Dilation E) (R : Qudit) : H ⊗ R ⟶ K ⊗ (E ⊗ R) :=
  (d.toHom ⊗ₘ 𝟙 R) ≫ (α_ K E R).hom

/-- The reference extension of a dilation remains an isometry. -/
instance (d : Φ.Dilation E) (R : Qudit) : IsIsometry (d.lift R) := by
  unfold lift
  infer_instance

/-- The lifted isometry discards the reference on the system side and retains it
on the complementary side. Both equalities hold on all input operators. -/
lemma hasMarginals_lift (d : Φ.Dilation E) (R : Qudit) :
    CQM.HasMarginals (ofIsometry (d.lift R)).asHom
      (Φ.comp (partialTraceRight H R)).asHom (d.complementary.tensor (id R)).asHom := by
  dsimp only [lift]
  rw [ofIsometry_comp, ofIsometry_tensor, ofIsometry_id]
  simpa only [CausalQudit.fst_eq_partialTraceRight] using!
    d.hasMarginals.tensorRight (𝟙 (⟨R⟩ : CausalQudit))

/-- Discarding environment and reference after lifting gives the channel on the input marginal. -/
lemma partialTraceRight_lift (d : Φ.Dilation E) (R : Qudit) :
    (Operator.partialTraceRight : Superoperator (K ⊗ (E ⊗ R)) K) ∘ₗ
        Superoperator.conjugate (d.lift R).hom =
      Φ.toSuperoperator ∘ₗ (Operator.partialTraceRight : Superoperator (H ⊗ R) H) :=
  congrArg QuantumChannel.toSuperoperator (hasMarginals_iff.mp (d.hasMarginals_lift R)).1

/-- The other marginal is the complementary channel with the reference left untouched. -/
lemma partialTraceLeft_lift (d : Φ.Dilation E) (R : Qudit) :
    (Operator.partialTraceLeft : Superoperator (K ⊗ (E ⊗ R)) (E ⊗ R)) ∘ₗ
        Superoperator.conjugate (d.lift R).hom =
      (d.complementary.tensor (id R)).toSuperoperator :=
  congrArg QuantumChannel.toSuperoperator (hasMarginals_iff.mp (d.hasMarginals_lift R)).2

/-- A lifted pure state purifies the channel output on its input marginal. -/
lemma partialTraceRight_pure_lift (d : Φ.Dilation E) {R : Qudit}
    (ψ : UnitState (H ⊗ R)) :
    (Density.pure (ψ.map (d.lift R))).partialTraceRight =
      Φ.map (Density.pure ψ).partialTraceRight := by
  rw [← Density.map_pure]
  exact Density.ext (LinearMap.congr_fun (d.partialTraceRight_lift R) (Density.pure ψ).op)

/-- The environment-reference marginal is the complementary channel applied to the pure input. -/
lemma partialTraceLeft_pure_lift (d : Φ.Dilation E) {R : Qudit}
    (ψ : UnitState (H ⊗ R)) :
    (Density.pure (ψ.map (d.lift R))).partialTraceLeft =
      (d.complementary.tensor (id R)).map (Density.pure ψ) := by
  rw [← Density.map_pure]
  exact Density.ext (LinearMap.congr_fun (d.partialTraceLeft_lift R) (Density.pure ψ).op)

end Dilation

/-- The identity isometry dilates the channel discarding the right subsystem. -/
def partialTraceRightDilation (H K : Qudit) : (partialTraceRight H K).Dilation K where
  toHom := 𝟙 (H ⊗ K)
  isIsometry := inferInstance
  channel_eq := by
    rw [hom_id, Superoperator.conjugate_id, LinearMap.comp_id]
    rfl

/-- The two partial-trace channels are complementary under the identity dilation. -/
lemma complementary_partialTraceRightDilation (H K : Qudit) :
    (partialTraceRightDilation H K).complementary = partialTraceLeft H K := by
  change (partialTraceLeft H K).comp (ofIsometry (𝟙 (H ⊗ K))) = _
  rw [ofIsometry_id, comp_id]

/-- A chosen Stinespring dilation in a standard environment of sufficient dimension. -/
def dilation (Φ : QuantumChannel H K) :
    Φ.Dilation (std (Module.finrank ℂ K.state * Module.finrank ℂ H.state)) where
  toHom := Φ.exists_dilation_finrank.choose
  isIsometry := Φ.exists_dilation_finrank.choose_spec.1
  channel_eq := Φ.exists_dilation_finrank.choose_spec.2

/-- A complementary channel, obtained from the chosen standard Stinespring dilation. -/
def complementary (Φ : QuantumChannel H K) :
    QuantumChannel H (std (Module.finrank ℂ K.state * Module.finrank ℂ H.state)) :=
  Φ.dilation.complementary

/-- The chosen complementary channel returns the environment marginal. -/
lemma map_complementary (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.complementary.map ρ = (ρ.map Φ.dilation.toHom).partialTraceLeft := rfl

end

end Qudit.QuantumChannel
