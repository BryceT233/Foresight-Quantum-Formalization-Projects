/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the upstream statement of channel monotonicity.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/Fidelity.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Error.Fidelity
public import FQFP.CQM.Qudit.Channel.Dilation.Purification

/-!
# Fidelity is monotone under quantum channels

Uhlmann's theorem supplies input purifications attaining `Density.fidelity`.
A common channel dilation preserves their overlap, which is bounded by the output
fidelity. This proves the density-state case of Watrous, *The Theory of Quantum
Information*, Theorem 3.27, using the existing unsquared fidelity convention.
No rank, invertibility, or dimension assumptions are imposed on the channel or states.

## Main results

* `Qudit.QuantumChannel.fidelity_le_map`: a quantum channel cannot decrease fidelity.
* `Qudit.QuantumChannel.fidelity_le_tensor_id_map`: monotonicity with an arbitrary reference system.
* `Qudit.Density.fidelity_le_partialTraceRight`: discarding the right subsystem cannot decrease
  fidelity.
* `Qudit.Density.fidelity_le_partialTraceLeft`: the corresponding left-discarding inequality.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit

noncomputable section

namespace QuantumChannel

variable {H K : Qudit}

/-- Applying the same quantum channel cannot decrease mixed-state fidelity. -/
theorem fidelity_le_map (Φ : QuantumChannel H K) (ρ σ : Density H) :
    ρ.fidelity σ ≤ (Φ.map ρ).fidelity (Φ.map σ) := by
  obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ρ.purify
    ρ.partialTraceRight_pure_purify (LinearMap.finrank_range_le σ.op)
  obtain ⟨n, W, hW, hΦ⟩ := Φ.exists_purification_map H
  have hρ := hΦ ρ.purify
  rw [ρ.partialTraceRight_pure_purify] at hρ
  have hσ := hΦ φ
  rw [hφ] at hσ
  calc
    ρ.fidelity σ = ‖inner ℂ ρ.purify.val φ.val‖ := he.symm
    _ = ‖inner ℂ (ρ.purify.map W).val (φ.map W).val‖ := by
      rw [UnitState.coe_map, UnitState.coe_map, inner_map_map_of_isIsometry]
    _ ≤ (Φ.map ρ).fidelity (Φ.map σ) :=
      Density.norm_inner_le_fidelity _ _ _ _ hρ hσ

/-- The squared-fidelity convention also cannot decrease under a quantum channel. -/
theorem fidelity_sq_le_map (Φ : QuantumChannel H K) (ρ σ : Density H) :
    ρ.fidelity σ ^ 2 ≤ (Φ.map ρ).fidelity (Φ.map σ) ^ 2 :=
  pow_le_pow_left₀ (ρ.fidelity_nonneg σ) (Φ.fidelity_le_map ρ σ) 2

/-- Fidelity is monotone also for inputs entangled with an arbitrary reference system. -/
theorem fidelity_le_tensor_id_map (Φ : QuantumChannel H K) (R : Qudit)
    (ρ σ : Density (H ⊗ R)) :
    ρ.fidelity σ ≤ ((Φ.tensor (id R)).map ρ).fidelity ((Φ.tensor (id R)).map σ) :=
  (Φ.tensor (id R)).fidelity_le_map ρ σ

end QuantumChannel

namespace Density

variable {H K : Qudit}

/-- Discarding the right subsystem cannot decrease fidelity. -/
theorem fidelity_le_partialTraceRight (ρ σ : Density (H ⊗ K)) :
    ρ.fidelity σ ≤ ρ.partialTraceRight.fidelity σ.partialTraceRight :=
  (QuantumChannel.partialTraceRight H K).fidelity_le_map ρ σ

/-- Discarding the left subsystem cannot decrease fidelity. -/
theorem fidelity_le_partialTraceLeft (ρ σ : Density (H ⊗ K)) :
    ρ.fidelity σ ≤ ρ.partialTraceLeft.fidelity σ.partialTraceLeft :=
  (QuantumChannel.partialTraceLeft H K).fidelity_le_map ρ σ

end Density

end

end Qudit
