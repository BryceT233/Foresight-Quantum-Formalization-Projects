/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/

/-
Physlib reference for the pure-state no-cloning statement.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Operators/Unitary.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Error.FidelityChannel
public import FQFP.CQM.Qudit.Error.FidelityTensor

/-!
# Exact cloning of two states

A single channel can produce two independent copies of either of two density states
exactly when the states coincide or their supports are orthogonal. In the orthogonal case,
measuring the first support distinguishes the inputs and permits exact preparation.

`Qudit.QuantumChannel.no_cloning_pure` specializes the obstruction to a pure input and
a common blank, as in physlib's `MState.no_cloning`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

variable {H K : Qudit}

private lemma eq_or_isOrtho_of_fidelity_le_mul_self (ρ σ : Density H)
    (h : ρ.fidelity σ ≤ ρ.fidelity σ * ρ.fidelity σ) : ρ = σ ∨ ρ.support ⟂ σ.support := by
  rcases (ρ.fidelity_nonneg σ).eq_or_lt with hz | hp
  · exact Or.inr ((ρ.fidelity_eq_zero_iff σ).mp hz.symm)
  · apply Or.inl ∘ (ρ.fidelity_eq_one_iff σ).mp
    apply le_antisymm (ρ.fidelity_le_one σ)
    exact le_of_mul_le_mul_left ((mul_one _).le.trans h) hp

/-- Two states cloned by the same channel are equal or have orthogonal supports. -/
theorem no_cloning (Φ : QuantumChannel H (H ⊗ H)) {ρ σ : Density H}
    (hρ : Φ.map ρ = ρ.tensor ρ) (hσ : Φ.map σ = σ.tensor σ) :
    ρ = σ ∨ ρ.support ⟂ σ.support := by
  apply eq_or_isOrtho_of_fidelity_le_mul_self
  simpa only [hρ, hσ, Density.fidelity_tensor] using Φ.fidelity_le_map ρ σ

/-- With a common blank state, the same obstruction holds for a channel on both inputs. -/
theorem no_cloning_with_ancilla (Φ : QuantumChannel (H ⊗ K) (H ⊗ H))
    (τ : Density K) {ρ σ : Density H} (hρ : Φ.map (ρ.tensor τ) = ρ.tensor ρ)
    (hσ : Φ.map (σ.tensor τ) = σ.tensor σ) : ρ = σ ∨ ρ.support ⟂ σ.support := by
  apply eq_or_isOrtho_of_fidelity_le_mul_self
  simpa only [hρ, hσ, Density.fidelity_tensor_right, Density.fidelity_tensor] using
    Φ.fidelity_le_map (ρ.tensor τ) (σ.tensor τ)

/-- Distinct pure states copied with a common blank must have zero transition probability. -/
theorem no_cloning_pure (U : H ⊗ H ⟶ H ⊗ H) [IsIsometry U] (ψ φ f : UnitState H)
    (hψ : (Density.pure (ψ.tensor f)).map U = Density.pure (ψ.tensor ψ))
    (hφ : (Density.pure (φ.tensor f)).map U = Density.pure (φ.tensor φ))
    (hlt : (Density.pure ψ).expectation (Density.pure φ).op < 1) :
    (Density.pure ψ).expectation (Density.pure φ).op = 0 := by
  have h := (ofIsometry U).no_cloning_with_ancilla (Density.pure f)
    (ρ := Density.pure ψ) (σ := Density.pure φ)
    (by simpa only [map_ofIsometry, Density.tensor_pure] using hψ)
    (by simpa only [map_ofIsometry, Density.tensor_pure] using hφ)
  rcases h with he | ho
  · exact (hlt.ne ((Density.expectation_pure_pure_eq_one_iff ψ φ).mpr he)).elim
  · rw [← Density.fidelity_pure_pure_sq, (Density.fidelity_eq_zero_iff _ _).mpr ho, sq, zero_mul]

/-- A channel can clone both densities exactly when they coincide or have orthogonal supports. -/
theorem exists_cloning_iff (ρ σ : Density H) :
    (∃ Φ : QuantumChannel H (H ⊗ H), Φ.map ρ = ρ.tensor ρ ∧ Φ.map σ = σ.tensor σ) ↔
      ρ = σ ∨ ρ.support ⟂ σ.support := by
  constructor
  · rintro ⟨Φ, hρ, hσ⟩
    exact Φ.no_cloning hρ hσ
  · rintro (rfl | ho)
    · exact ⟨replacement H (ρ.tensor ρ), map_replacement _ _, map_replacement _ _⟩
    · let P : Operator H := ρ.support.starProjection.toLinearMap
      have hρ : P * ρ.op = ρ.op := by
        exact LinearMap.ext fun x => Submodule.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
      have hσ : P * σ.op = 0 := by
        exact LinearMap.ext fun x => (ρ.support.starProjection_apply_eq_zero_iff).mpr
          (ho.symm (show σ.op x ∈ σ.support from ⟨x, rfl⟩))
      let M := POVM.ofSubmodule ρ.support
      let out (b : Bool) := if b then ρ.tensor ρ else σ.tensor σ
      have hm (τ : Density H) : ((M.measurePrepare out).map τ).op =
          (P * τ.op).trace • (ρ.tensor ρ).op + ((1 - P) * τ.op).trace • (σ.tensor σ).op := by
        rw [op_map, POVM.measurePrepare_apply, Fintype.sum_bool]
        rfl
      refine ⟨M.measurePrepare out, Density.ext ?_, Density.ext ?_⟩
      · simp [hm, sub_mul, hρ, ρ.trace_one]
      · simp [hm, sub_mul, hσ, σ.trace_one]

end Qudit.QuantumChannel
