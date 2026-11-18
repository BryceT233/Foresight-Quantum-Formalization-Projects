/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative.PartialTrace
public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.PartialTrace
public import FQFP.CQM.Qudit.Channel.Dilation.Basic
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

/-- **Data processing inequality** for Umegaki relative entropy under any quantum channel,
including inputs with infinite relative entropy. -/
theorem relativeEntropy_map_le (Φ : QuantumChannel H K) (ρ σ : Density H) :
    (Φ.map ρ).relativeEntropy (Φ.map σ) ≤ ρ.relativeEntropy σ := by
  obtain ⟨n, V, hV, hΦ⟩ := Φ.exists_dilation_map
  rw [hΦ ρ, hΦ σ]
  calc
    _ ≤ (ρ.map V).relativeEntropy (σ.map V) :=
      (ρ.map V).relativeEntropy_partialTraceRight_le (σ.map V)
    _ = ρ.relativeEntropy σ := ρ.relativeEntropy_map_isometry σ V

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

/-- **Data processing for sandwiched Rényi relative entropy** of every real order above one.
The Stinespring environment is discarded on the right. -/
theorem sandwichedRenyiRelativeEntropy_map_le (Φ : QuantumChannel H K) (ρ σ : Density H)
    (α : Set.Ioi (1 : ℝ)) :
    (Φ.map ρ).sandwichedRenyiRelativeEntropy (Φ.map σ) α ≤
      ρ.sandwichedRenyiRelativeEntropy σ α := by
  obtain ⟨n, V, hV, hΦ⟩ := Φ.exists_dilation_map
  rw [hΦ ρ, hΦ σ, ← ρ.sandwichedRenyiRelativeEntropy_map_isometry σ α V]
  exact (ρ.map V).sandwichedRenyiRelativeEntropy_partialTraceRight_le (σ.map V) α

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
