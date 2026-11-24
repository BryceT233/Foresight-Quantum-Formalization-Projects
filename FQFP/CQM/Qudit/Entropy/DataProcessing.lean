/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for data processing for relative entropy.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/DPI.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative.PartialTrace
public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.PartialTrace
public import FQFP.CQM.Qudit.Channel.DataProcessing
public import FQFP.CQM.Qudit.Channel.MeasurePrepare

/-!
# Data processing for quantum relative entropy

Apply a common Stinespring isometry to both densities, then trace out the environment
on the right. Both Umegaki and sandwiched Rényi relative entropy (at order above one) are
invariant under the isometry and decrease under the partial trace, including for singular states.
-/

@[expose] public section

namespace Qudit.QuantumChannel

variable {H K : Qudit}

/-- Umegaki relative entropy is a distinguishability measure on causal processes. -/
theorem satisfiesDataProcessing_relativeEntropy :
    CQM.SatisfiesDataProcessing CausalQudit.densityFunctor (fun _ ρ σ => ρ.relativeEntropy σ) :=
  CausalQudit.satisfiesDataProcessing_of_dilation Density.relativeEntropy
    (fun V _ ρ σ => (ρ.relativeEntropy_map_isometry σ V).le)
    Density.relativeEntropy_partialTraceRight_le

/-- **Data processing inequality** for Umegaki relative entropy under any quantum channel,
including inputs with infinite relative entropy. -/
theorem relativeEntropy_map_le (Φ : QuantumChannel H K) (ρ σ : Density H) :
    (Φ.map ρ).relativeEntropy (Φ.map σ) ≤ ρ.relativeEntropy σ :=
  satisfiesDataProcessing_relativeEntropy Φ.asHom ρ σ

/-- A channel preserves inclusion of the source support in the reference support. -/
lemma absolutelyContinuous_map (Φ : QuantumChannel H K) {ρ σ : Density H}
    (h : ρ.AbsolutelyContinuous σ) : (Φ.map ρ).AbsolutelyContinuous (Φ.map σ) :=
  (Density.relativeEntropy_ne_top_iff _ _).mp
    (ne_top_of_le_ne_top ((ρ.relativeEntropy_ne_top_iff σ).mpr h) (Φ.relativeEntropy_map_le ρ σ))

/-- On the finite-value domain, data processing also holds for the real trace formula. -/
theorem relativeEntropyReal_map_le (Φ : QuantumChannel H K) (ρ σ : Density H)
    (h : ρ.AbsolutelyContinuous σ) :
    (Φ.map ρ).relativeEntropyReal (Φ.map σ) ≤ ρ.relativeEntropyReal σ := by
  rw [← Density.toReal_relativeEntropy _ _ (Φ.absolutelyContinuous_map h),
    ← ρ.toReal_relativeEntropy σ h]
  exact ENNReal.toReal_mono ((ρ.relativeEntropy_ne_top_iff σ).mpr h) (Φ.relativeEntropy_map_le ρ σ)

/-- The sandwiched trace functional decreases under channels on the support-inclusion domain. -/
theorem sandwichedTraceFunctional_map_le (Φ : QuantumChannel H K) (ρ σ : Density H)
    {α : ℝ} (hα : 1 < α) (h : ρ.AbsolutelyContinuous σ) :
    (Φ.map ρ).sandwichedTraceFunctional (Φ.map σ) α ≤ ρ.sandwichedTraceFunctional σ α := by
  obtain ⟨n, V, hV, hΦ⟩ := Φ.exists_dilation_map
  rw [hΦ ρ, hΦ σ, ← ρ.sandwichedTraceFunctional_map_isometry σ hα V]
  exact (ρ.map V).sandwichedTraceFunctional_partialTraceRight_le (σ.map V) hα
    ((ρ.absolutelyContinuous_map_iff σ V).mpr h)

/-- Sandwiched Rényi relative entropy satisfies categorical data processing above order one. -/
theorem satisfiesDataProcessing_sandwichedRenyiRelativeEntropy (α : Set.Ioi (1 : ℝ)) :
    CQM.SatisfiesDataProcessing CausalQudit.densityFunctor
      (fun _ ρ σ => ρ.sandwichedRenyiRelativeEntropy σ α) :=
  CausalQudit.satisfiesDataProcessing_of_dilation (fun ρ σ => ρ.sandwichedRenyiRelativeEntropy σ α)
    (fun V _ ρ σ => (ρ.sandwichedRenyiRelativeEntropy_map_isometry σ α V).le)
    (fun ρ σ => ρ.sandwichedRenyiRelativeEntropy_partialTraceRight_le σ α)

/-- **Data processing for sandwiched Rényi relative entropy** of every real order above one.
The Stinespring environment is discarded on the right. -/
theorem sandwichedRenyiRelativeEntropy_map_le (Φ : QuantumChannel H K) (ρ σ : Density H)
    (α : Set.Ioi (1 : ℝ)) :
    (Φ.map ρ).sandwichedRenyiRelativeEntropy (Φ.map σ) α ≤
      ρ.sandwichedRenyiRelativeEntropy σ α :=
  satisfiesDataProcessing_sandwichedRenyiRelativeEntropy α Φ.asHom ρ σ

end Qudit.QuantumChannel

namespace Qudit.Density

variable {H : Qudit}

/-- On the finite domain the trace functional is at least one, by discarding the input
and preparing a fixed state. Consequently its logarithm is nonnegative. -/
lemma one_le_sandwichedTraceFunctional (ρ σ : Density H) {α : ℝ} (hα : 1 < α)
    (h : ρ.AbsolutelyContinuous σ) : 1 ≤ ρ.sandwichedTraceFunctional σ α := by
  simpa only [QuantumChannel.map_replacement, sandwichedTraceFunctional_self ρ hα] using
    (QuantumChannel.replacement H ρ).sandwichedTraceFunctional_map_le ρ σ hα h

/-- Real-valued formula for finite sandwiched Rényi relative entropy, including singular
reference states whose support contains the source support. -/
lemma toReal_sandwichedRenyiRelativeEntropy (ρ σ : Density H) (α : Set.Ioi (1 : ℝ))
    (h : ρ.AbsolutelyContinuous σ) : (ρ.sandwichedRenyiRelativeEntropy σ α).toReal =
      Real.log (ρ.sandwichedTraceFunctional σ α) / (α.val - 1) := by
  rw [sandwichedRenyiRelativeEntropy, ite_eq_left h, ENNReal.toReal_ofReal]
  exact div_nonneg (Real.log_nonneg (ρ.one_le_sandwichedTraceFunctional σ α.property h))
    (sub_nonneg.mpr α.property.le)

end Qudit.Density
