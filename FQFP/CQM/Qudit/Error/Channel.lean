/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.Error.TraceDistance

/-!
# Contractivity and composable channel errors

Positive trace-preserving maps contract the trace norm of self-adjoint operators;
quantum channels therefore contract trace distance. Sequential errors add when each
step's error is bounded uniformly over all input density states. Reference systems
are explicit: unextended error bounds are not asserted to be diamond-norm bounds.

## Main definitions and results

* `Qudit.QuantumChannel.traceDistance_map_le`: contractivity of trace distance under a channel.
* `Qudit.QuantumChannel.traceDistance_comp_map_le`: error bounds for sequential channel composition.
* `Qudit.QuantumChannel.trajectory`: states evolving along a sequence of channels.
* `Qudit.QuantumChannel.traceDistance_trajectory_le`: accumulated error along a channel trajectory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators

namespace Qudit

noncomputable section

namespace QuantumChannel

variable {H K L : Qudit}

/-- Applying the same quantum channel cannot increase trace distance. -/
theorem traceDistance_map_le (Φ : QuantumChannel H K) (ρ σ : Density H) :
    (Φ.map ρ).traceDistance (Φ.map σ) ≤ ρ.traceDistance σ := by
  have h := (ρ.positive.isSymmetric.sub σ.positive.isSymmetric).traceNorm_map_le
    Φ.toSuperoperator Φ.completelyPositive.isPositive Φ.tracePreserving
  simpa only [Density.traceDistance, op_map, map_sub] using
    div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)

/-- Contractivity also holds for arbitrary, possibly entangled, reference-system inputs. -/
theorem traceDistance_tensor_id_map_le (Φ : QuantumChannel H K) (R : Qudit)
    (ρ σ : Density (H ⊗ R)) :
    ((Φ.tensor (id R)).map ρ).traceDistance ((Φ.tensor (id R)).map σ) ≤
      ρ.traceDistance σ :=
  (Φ.tensor (id R)).traceDistance_map_le ρ σ

/-- A uniform single-step channel error adds to the incoming state error. -/
theorem traceDistance_map_map_le (Φ Ψ : QuantumChannel H K) {ε : ℝ}
    (hε : ∀ τ : Density H, (Φ.map τ).traceDistance (Ψ.map τ) ≤ ε)
    (ρ σ : Density H) :
    (Φ.map ρ).traceDistance (Ψ.map σ) ≤ ρ.traceDistance σ + ε :=
  (Density.traceDistance_triangle _ (Φ.map σ) _).trans
    (add_le_add (Φ.traceDistance_map_le ρ σ) (hε σ))

/-- Two sequential approximations have error at most the sum of their uniform bounds. -/
theorem traceDistance_comp_map_le (Φ Ψ : QuantumChannel H K)
    (Φ' Ψ' : QuantumChannel K L) {ε δ : ℝ}
    (hε : ∀ τ : Density H, (Φ.map τ).traceDistance (Ψ.map τ) ≤ ε)
    (hδ : ∀ τ : Density K, (Φ'.map τ).traceDistance (Ψ'.map τ) ≤ δ)
    (ρ : Density H) :
    ((Φ'.comp Φ).map ρ).traceDistance ((Ψ'.comp Ψ).map ρ) ≤ ε + δ := by
  rw [map_comp, map_comp]
  exact (Φ'.traceDistance_map_map_le Ψ' hδ _ _).trans (add_le_add (hε ρ) le_rfl)

/-- Run a sequence of channels, allowing the state space to change at each step. -/
def trajectory {S : ℕ → Qudit} (Φ : ∀ n, QuantumChannel (S n) (S (n + 1)))
    (ρ : Density (S 0)) : ∀ n, Density (S n)
  | 0 => ρ
  | n + 1 => (Φ n).map (trajectory Φ ρ n)

/-- Finite sequential error is bounded by initial error plus the sum of uniform step errors. -/
theorem traceDistance_trajectory_le {S : ℕ → Qudit}
    (Φ Ψ : ∀ n, QuantumChannel (S n) (S (n + 1))) (ε : ℕ → ℝ)
    (hε : ∀ n (τ : Density (S n)), ((Φ n).map τ).traceDistance ((Ψ n).map τ) ≤ ε n)
    (ρ σ : Density (S 0)) (n : ℕ) :
    (trajectory Φ ρ n).traceDistance (trajectory Ψ σ n) ≤
      ρ.traceDistance σ + ∑ i ∈ Finset.range n, ε i := by
  induction n with
  | zero => simp only [trajectory, Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ n ih =>
    calc
      _ ≤ (trajectory Φ ρ n).traceDistance (trajectory Ψ σ n) + ε n :=
        (Φ n).traceDistance_map_map_le (Ψ n) (hε n) _ _
      _ ≤ (ρ.traceDistance σ + ∑ i ∈ Finset.range n, ε i) + ε n :=
        add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_range_succ, add_assoc]

end QuantumChannel

namespace Density

variable {H K : Qudit}

/-- Discarding the right subsystem contracts trace distance. -/
theorem traceDistance_partialTraceRight_le (ρ σ : Density (H ⊗ K)) :
    ρ.partialTraceRight.traceDistance σ.partialTraceRight ≤ ρ.traceDistance σ :=
  (QuantumChannel.partialTraceRight H K).traceDistance_map_le ρ σ

/-- Discarding the left subsystem contracts trace distance. -/
theorem traceDistance_partialTraceLeft_le (ρ σ : Density (H ⊗ K)) :
    ρ.partialTraceLeft.traceDistance σ.partialTraceLeft ≤ ρ.traceDistance σ :=
  (QuantumChannel.partialTraceLeft H K).traceDistance_map_le ρ σ

end Density

namespace POVM

/-- Any common channel before measurement preserves a trace-distance error bound. -/
theorem abs_probability_channel_sub_le_traceDistance {H K : Qudit}
    {ι : Type*} [Fintype ι] (M : POVM K ι) (Φ : QuantumChannel H K)
    (ρ σ : Density H) (i : ι) :
    |M.probability (Φ.map ρ) i - M.probability (Φ.map σ) i| ≤ ρ.traceDistance σ :=
  (M.abs_probability_sub_le_traceDistance _ _ i).trans (Φ.traceDistance_map_le ρ σ)

end POVM

end

end Qudit
