/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.State.Separable

/-!
# Channels acting on finite ensembles and separable states

Channels commute with finite mixtures. In particular, local channels preserve mixed-state
separability. The classical ensemble labels and their probabilities are retained.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit

noncomputable section

variable {H K L M : Qudit} {ι : Type*} [Fintype ι]

/-- Quantum channels commute with arbitrary finite probability mixtures. -/
lemma QuantumChannel.map_mixture (Φ : QuantumChannel H K)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ρ : ι → Density H) :
    Φ.map (Density.mixture w hw hs ρ) = Density.mixture w hw hs (fun i => Φ.map (ρ i)) := by
  apply Density.ext
  simp only [QuantumChannel.op_map, Density.op_mixture, map_sum, map_smul]

/-- Apply a channel to every member of an ensemble, retaining its classical distribution. -/
def Ensemble.map (e : Ensemble H ι) (Φ : QuantumChannel H K) : Ensemble K ι :=
  ⟨e.distribution, fun i => Φ.map (e.state i)⟩

/-- Evolving the ensemble then forgetting its label gives the evolved mixed state. -/
@[simp]
lemma Ensemble.mix_map (e : Ensemble H ι) (Φ : QuantumChannel H K) :
    (e.map Φ).mix = Φ.map e.mix :=
  (Φ.map_mixture e.weight e.weight_nonneg e.sum_weight e.state).symm

/-- Local channels preserve finite convex combinations of product density operators. -/
lemma Density.IsSeparable.map_tensor {ρ : Density (H ⊗ L)} (hρ : ρ.IsSeparable)
    (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) : ((Φ.tensor Ψ).map ρ).IsSeparable := by
  obtain ⟨ι, _, w, hw, hs, σ, τ, rfl⟩ := ρ.isSeparable_iff_exists_mixture.mp hρ
  simp only [QuantumChannel.map_mixture, QuantumChannel.map_tensor]
  exact Density.isSeparable_mixture_tensor w hw hs _ _

end

end Qudit
