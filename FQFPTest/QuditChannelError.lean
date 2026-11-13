/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Error.ProductFormula
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Noisy and sequential error clients

These clients exercise discarded entanglement, rectangular channels, explicit joint-input
error assumptions, noisy unitary sequences, and product-formula output measurements.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Qudit
open scoped BigOperators

noncomputable section

-- Discarding half of an entangled input is covered without a product-state assumption.
example (σ : Density (Qubit ⊗ Qubit)) :
    (Density.maximallyMixed Qubit (by simp [Qubit])).traceDistance σ.partialTraceRight ≤
      bellDensity.traceDistance σ := by
  simpa only [bellDensity_partialTraceRight] using
    bellDensity.traceDistance_partialTraceRight_le σ

example (ρ σ : Density (std 3 ⊗ Qubit)) :
    ρ.partialTraceLeft.traceDistance σ.partialTraceLeft ≤ ρ.traceDistance σ :=
  ρ.traceDistance_partialTraceLeft_le σ

-- A common local channel contracts distance even for the entangled Bell input.
example (Φ : QuantumChannel Qubit Qubit) (σ : Density (Qubit ⊗ Qubit)) :
    ((Φ.tensor (QuantumChannel.id Qubit)).map bellDensity).traceDistance
        ((Φ.tensor (QuantumChannel.id Qubit)).map σ) ≤ bellDensity.traceDistance σ :=
  Φ.traceDistance_tensor_id_map_le Qubit bellDensity σ

-- The reference-system approximation hypothesis is explicitly over joint density states.
example (Φ Ψ : QuantumChannel Qubit Qubit) {ε : ℝ}
    (hε : ∀ τ : Density (Qubit ⊗ std 3),
      ((Φ.tensor (QuantumChannel.id (std 3))).map τ).traceDistance
        ((Ψ.tensor (QuantumChannel.id (std 3))).map τ) ≤ ε)
    (ρ σ : Density (Qubit ⊗ std 3)) :
    ((Φ.tensor (QuantumChannel.id (std 3))).map ρ).traceDistance
        ((Ψ.tensor (QuantumChannel.id (std 3))).map σ) ≤ ρ.traceDistance σ + ε :=
  (Φ.tensor (QuantumChannel.id (std 3))).traceDistance_map_map_le
    (Ψ.tensor (QuantumChannel.id (std 3))) hε ρ σ

-- A second, dimension-changing stage contributes zero error when shared by both processes.
example (Φ Ψ : QuantumChannel Qubit (Qubit ⊗ std 3)) {ε : ℝ}
    (hε : ∀ τ, (Φ.map τ).traceDistance (Ψ.map τ) ≤ ε) (ρ : Density Qubit) :
    (((QuantumChannel.partialTraceRight Qubit (std 3)).comp Φ).map ρ).traceDistance
        (((QuantumChannel.partialTraceRight Qubit (std 3)).comp Ψ).map ρ) ≤ ε := by
  simpa only [add_zero] using Φ.traceDistance_comp_map_le Ψ
    (QuantumChannel.partialTraceRight Qubit (std 3))
    (QuantumChannel.partialTraceRight Qubit (std 3)) hε
    (fun τ => le_of_eq (Density.traceDistance_self _)) ρ

-- The empty process retains precisely the incoming state error.
example {S : ℕ → Qudit} (Φ Ψ : ∀ n, QuantumChannel (S n) (S (n + 1)))
    (ρ σ : Density (S 0)) :
    (QuantumChannel.trajectory Φ ρ 0).traceDistance (QuantumChannel.trajectory Ψ σ 0) =
      ρ.traceDistance σ := rfl

-- Each approximate unitary can be followed by its own common noise channel.
example {H : Qudit} (U V : ℕ → unitary (H.state →L[ℂ] H.state))
    (N : ℕ → QuantumChannel H H) (ρ σ : Density H) (n : ℕ) :
    (QuantumChannel.trajectory
      (fun k => (N k).comp (QuantumChannel.ofIsometry (unitaryHom (U k)))) ρ n).traceDistance
      (QuantumChannel.trajectory
        (fun k => (N k).comp (QuantumChannel.ofIsometry (unitaryHom (V k)))) σ n) ≤
      ρ.traceDistance σ + ∑ k ∈ Finset.range n, ‖(U k).val - (V k).val‖ := by
  apply QuantumChannel.traceDistance_trajectory_le
  intro k τ
  rw [QuantumChannel.map_comp, QuantumChannel.map_comp,
    QuantumChannel.map_ofIsometry, QuantumChannel.map_ofIsometry]
  exact ((N k).traceDistance_map_le _ _).trans (τ.traceDistance_evolve_le_opNorm (U k) (V k))

-- A noisy qutrit simulation can be measured on a different output system.
example {Υ Γ : ℕ} (P : TrotterError.ProductFormulaData Υ Γ)
    (A : Fin Γ → (std 3).state →L[ℂ] (std 3).state) (hA : ∀ i, star (A i) = -(A i))
    (p : ℕ) (hp : 1 ≤ p) (horder : P.IsOrderOf p A) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (Φ : QuantumChannel (std 3) Qubit)
    (ρ : Density (std 3)) (i : Fin 2) :
    |(POVM.computational 2).probability
        (Φ.map (ρ.evolve (productFormulaEvolution P A hA t))) i -
      (POVM.computational 2).probability (Φ.map (ρ.evolve (exactEvolution A hA t))) i| ≤
      2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * TrotterError.αComm p A * t ^ (p + 1) :=
  abs_probability_channel_productFormula_sub_le
    (POVM.computational 2) Φ P A hA p hp horder hΥ t ht ρ i

-- Zero-dimensional inputs need no density inhabitant in the operator-level theorem.
example (Φ : QuantumChannel (std 0) Qubit) :
    LinearMap.traceNorm (Φ.toSuperoperator 0) ≤ LinearMap.traceNorm (0 : Operator (std 0)) :=
  LinearMap.IsSymmetric.zero.traceNorm_map_le Φ.toSuperoperator
    Φ.completelyPositive.isPositive Φ.tracePreserving

end
