/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Capacity/Capacity.lean: emulation, fidelity approximation, achievable rates,
and the operational quantum capacity with its elementary bounds.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Composite
public import FQFP.CQM.Qudit.Channel.Process.State
public import FQFP.CQM.Qudit.Error.Fidelity
public import FQFP.CQM.Qudit.TensorPower
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Operational quantum capacity

A code simulates the identity on a logical qudit by encoding, using a channel in parallel,
and decoding. Its error is measured by root fidelity on every input density state. Its rate
is measured in qubits per channel use. The index `n` of `Qudit.tensorPower` counts the
sites following the first, so the number of channel uses in the rate inequality is `n + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

variable {H K L M S T : Qudit}

/-- Parallel uses of a channel on a register of `n + 1` sites. -/
def tensorPower (Φ : QuantumChannel H K) : (n : ℕ) →
    QuantumChannel (Qudit.tensorPower H n) (Qudit.tensorPower K n)
  | 0 => Φ
  | n + 1 => Φ.tensor (Φ.tensorPower n)

/-- A channel emulates another if encoding and decoding realize it exactly. -/
def Emulates (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) : Prop :=
  ∃ (E : QuantumChannel L H) (D : QuantumChannel K M), D.comp (Φ.comp E) = Ψ

/-- Exact emulation allows identity encoders and decoders. -/
@[refl]
theorem Emulates.refl (Φ : QuantumChannel H K) : Φ.Emulates Φ :=
  ⟨id H, id K, by rw [comp_id, id_comp]⟩

/-- Unitarily equivalent registers can transmit each other's identity channel. -/
theorem id_emulates_id (e : H.state ≃ₗᵢ[ℂ] K.state) : (id H).Emulates (id K) := by
  let u : H ≅ K := isoMk e.toLinearEquiv
  have : DaggerCategory.IsUnitary u.hom := isUnitary_isoMk_coe_LIEquiv e
  let v := CausalQudit.unitaryIso u.hom
  exact ⟨v.inv, v.hom, by rw [id_comp]; exact v.inv_hom_id⟩

/-- Encoders and decoders for two successive simulations compose. -/
@[trans]
theorem Emulates.trans {Φ : QuantumChannel H K} {Ψ : QuantumChannel L M}
    {Γ : QuantumChannel S T} (h : Φ.Emulates Ψ) (h' : Ψ.Emulates Γ) : Φ.Emulates Γ := by
  obtain ⟨E, D, rfl⟩ := h
  obtain ⟨E', D', rfl⟩ := h'
  exact ⟨E.comp E', D'.comp D, by simp only [comp_assoc]⟩

/-- Independent encoders and decoders give an emulation on parallel channels. -/
theorem Emulates.tensor {H' K' L' M' : Qudit} {Φ : QuantumChannel H K} {Ψ : QuantumChannel L M}
    {Φ' : QuantumChannel H' K'} {Ψ' : QuantumChannel L' M'}
    (h : Φ.Emulates Ψ) (h' : Φ'.Emulates Ψ') : (Φ.tensor Φ').Emulates (Ψ.tensor Ψ') := by
  obtain ⟨E, D, rfl⟩ := h
  obtain ⟨E', D', rfl⟩ := h'
  exact ⟨E.tensor E', D.tensor D', by simp only [tensor_comp]⟩

/-- The same simulation can be run on every site of a register. -/
theorem Emulates.tensorPower {Φ : QuantumChannel H K} {Ψ : QuantumChannel L M}
    (h : Φ.Emulates Ψ) (n : ℕ) : (Φ.tensorPower n).Emulates (Ψ.tensorPower n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact h.tensor ih

/-- Worst-case root fidelity on input densities is at least `1 - ε`. -/
def Approximates (Φ Ψ : QuantumChannel H K) (ε : ℝ) : Prop :=
  ∀ ρ : Density H, 1 - ε ≤ (Φ.map ρ).fidelity (Ψ.map ρ)

/-- Every channel approximates itself with zero error. -/
theorem approximates_self (Φ : QuantumChannel H K) : Φ.Approximates Φ 0 :=
  fun ρ => by rw [sub_zero, Density.fidelity_self]

/-- Increasing the error tolerance preserves an approximation. -/
theorem Approximates.mono {Φ Ψ : QuantumChannel H K} {ε δ : ℝ}
    (h : Φ.Approximates Ψ ε) (hle : ε ≤ δ) : Φ.Approximates Ψ δ :=
  fun ρ => (sub_le_sub_left hle 1).trans (h ρ)

/-- A rate is achievable if, at every positive tolerance, a nonempty block of channel uses
simulates the identity on a logical system of the required dimension. -/
def AchievesRate (Φ : QuantumChannel H K) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n d : ℕ) (Ψ : QuantumChannel (std d) (std d)),
    (Φ.tensorPower n).Emulates Ψ ∧ R * (n + 1 : ℝ) ≤ Real.logb 2 d ∧ Ψ.Approximates (id _) ε

/-- Operational quantum capacity in qubits per channel use. -/
def quantumCapacity (Φ : QuantumChannel H K) : ℝ := sSup {R | Φ.AchievesRate R}

/-- A code for a higher rate also witnesses every lower rate. -/
theorem AchievesRate.mono {Φ : QuantumChannel H K} {R r : ℝ}
    (h : Φ.AchievesRate R) (hle : r ≤ R) : Φ.AchievesRate r := by
  intro ε hε
  obtain ⟨n, d, Ψ, hΨ, hR, hδ⟩ := h ε hε
  exact ⟨n, d, Ψ, hΨ, (mul_le_mul_of_nonneg_right hle (by positivity)).trans hR, hδ⟩

/-- A channel can achieve every rate achievable by a channel it emulates. -/
theorem Emulates.achievesRate {Φ : QuantumChannel H K} {Ψ : QuantumChannel L M} {R : ℝ}
    (h : Φ.Emulates Ψ) (hR : Ψ.AchievesRate R) : Φ.AchievesRate R := by
  intro ε hε
  obtain ⟨n, d, Γ, hΓ, hr, hδ⟩ := hR ε hε
  exact ⟨n, d, Γ, (h.tensorPower n).trans hΓ, hr, hδ⟩

/-- The identity transmits its full log-dimension in one use. -/
theorem id_achievesRate_log_finrank (H : Qudit) :
    (id H).AchievesRate (Real.logb 2 (Module.finrank ℂ H.state)) := by
  intro ε hε
  refine ⟨0, Module.finrank ℂ H.state, id _, ?_, by simp, (approximates_self _).mono hε.le⟩
  exact id_emulates_id (stdOrthonormalBasis ℂ H.state).repr

/-- A channel with positive input dimension achieves rate zero using the trivial logical system. -/
theorem achievesRate_zero (Φ : QuantumChannel H K) (hH : Module.finrank ℂ H.state ≠ 0) :
    Φ.AchievesRate 0 := by
  have h : Φ.Emulates (id (𝟙_ Qudit)) := by
    refine ⟨(Density.maximallyMixed H hH).toState, CausalQudit.discard ⟨K⟩, ?_⟩
    exact (CausalQudit.eq_discard (H := 𝟙_ CausalQudit) _).trans
      (CausalQudit.eq_discard (H := 𝟙_ CausalQudit) (𝟙 _)).symm
  simpa [state_tensorUnit] using h.achievesRate (id_achievesRate_log_finrank _)

/-- Quantum capacity is nonnegative for channels with positive input dimension. -/
theorem quantumCapacity_nonneg (Φ : QuantumChannel H K) (hH : Module.finrank ℂ H.state ≠ 0) :
    0 ≤ Φ.quantumCapacity := by
  by_cases hb : BddAbove {R | Φ.AchievesRate R}
  · exact le_csSup hb (Φ.achievesRate_zero hH)
  · exact (Real.sSup_of_not_bddAbove hb).ge

end Qudit.QuantumChannel
