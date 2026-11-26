/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.Basic
public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import FQFP.CQM.Qudit.Error.Channel
public import FQFP.CQM.Qudit.Error.FidelityChannel

/-!
# Distinguishability bounds for channel degradation

A pair of input states can rule out simulation of one channel by another. Trace distance
and relative entropies decrease along the postprocessing order, while fidelity increases.
The channels being compared can have different output systems.
-/

@[expose] public section

namespace Qudit.QuantumChannel

open CausalQudit

/-- Trace distance is contractive on deterministic processes. -/
theorem satisfiesDataProcessing_traceDistance :
    CQM.SatisfiesDataProcessing densityFunctor (fun X => Density.traceDistance (H := X.toQudit)) :=
  fun f ρ σ => f.traceDistance_map_le ρ σ

/-- Fidelity satisfies data processing in the reverse order. -/
theorem satisfiesDataProcessing_fidelity :
    CQM.SatisfiesDataProcessing densityFunctor
      (fun X (ρ σ : Density X.toQudit) => OrderDual.toDual (ρ.fidelity σ)) :=
  fun f ρ σ => f.fidelity_le_map ρ σ

namespace IsDegradableTo

variable {H K L : Qudit} {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}

/-- The simulating channel retains at least as much trace distance. -/
theorem traceDistance_le (h : Φ.IsDegradableTo Ψ) (ρ σ : Density H) :
    (Ψ.map ρ).traceDistance (Ψ.map σ) ≤ (Φ.map ρ).traceDistance (Φ.map σ) :=
  satisfiesDataProcessing_traceDistance.le_of_isDegradableTo ((isDegradableTo_iff _ _).mp h) ρ σ

/-- The simulated outputs have at least the fidelity of the simulating outputs. -/
theorem fidelity_le (h : Φ.IsDegradableTo Ψ) (ρ σ : Density H) :
    (Φ.map ρ).fidelity (Φ.map σ) ≤ (Ψ.map ρ).fidelity (Ψ.map σ) :=
  satisfiesDataProcessing_fidelity.le_of_isDegradableTo ((isDegradableTo_iff _ _).mp h) ρ σ

/-- Umegaki relative entropy cannot increase along a degradation, including at infinity. -/
theorem relativeEntropy_le (h : Φ.IsDegradableTo Ψ) (ρ σ : Density H) :
    (Ψ.map ρ).relativeEntropy (Ψ.map σ) ≤ (Φ.map ρ).relativeEntropy (Φ.map σ) :=
  satisfiesDataProcessing_relativeEntropy.le_of_isDegradableTo ((isDegradableTo_iff _ _).mp h) ρ σ

/-- Sandwiched Rényi relative entropy cannot increase along a degradation above order one. -/
theorem sandwichedRenyiRelativeEntropy_le (h : Φ.IsDegradableTo Ψ) (ρ σ : Density H)
    (α : Set.Ioi (1 : ℝ)) : (Ψ.map ρ).sandwichedRenyiRelativeEntropy (Ψ.map σ) α ≤
      (Φ.map ρ).sandwichedRenyiRelativeEntropy (Φ.map σ) α :=
  CQM.SatisfiesDataProcessing.le_of_isDegradableTo (F := densityFunctor)
    (q := fun _ ρ σ => ρ.sandwichedRenyiRelativeEntropy σ α)
    (satisfiesDataProcessing_sandwichedRenyiRelativeEntropy α) ((isDegradableTo_iff _ _).mp h) ρ σ

end IsDegradableTo

end Qudit.QuantumChannel
