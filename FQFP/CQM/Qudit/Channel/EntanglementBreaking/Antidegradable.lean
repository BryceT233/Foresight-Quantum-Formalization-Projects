/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the statement of Wilde's antidegradability exercise.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.BroadcastExtension
public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.ChoiDecomposition

/-!
# Entanglement-breaking channels are antidegradable

Applying an entanglement-breaking channel to the maximally entangled input gives a separable
Choi state. Its measure-and-prepare decomposition provides a joint channel by preparing
two output states for each measurement outcome. Self-compatibility then gives antidegradability.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped ComplexOrder

namespace Qudit.QuantumChannel

noncomputable section

variable {H K E : Qudit} {Φ : QuantumChannel H K} {ι : Type*} [Fintype ι]

/-- An entanglement-breaking channel has separable normalized Choi state in every input basis.
The definition tests the right factor, whereas the Choi convention places the output first. -/
theorem IsEntanglementBreaking.isSeparable_choiState (hΦ : Φ.IsEntanglementBreaking)
    (b : OrthonormalBasis ι ℂ H.state) (hH : 0 < Module.finrank ℂ H.state) :
    (Φ.choiState b hH).IsSeparable := by
  let ρ := (id H).choiState b hH
  obtain ⟨ι', _, w, hw, hs, r, s, he⟩ :=
    (Density.isSeparable_iff_exists_mixture _).mp (hΦ H ρ)
  apply (Density.isSeparable_iff_exists_mixture _).mpr
  refine ⟨ι', inferInstance, w, hw, hs, s, r, Density.ext ?_⟩
  let swap : Superoperator (H ⊗ K) (K ⊗ H) :=
    Superoperator.relabel (TensorProduct.commIsometry ℂ H.state K.state)
  have h := congrArg (fun τ => swap (Density.op τ)) he
  change swap (Density.mixture w hw hs (fun i => (r i).tensor (s i))).op =
    swap (Superoperator.tensor LinearMap.id Φ.toSuperoperator
      ((Module.finrank ℂ H.state : ℂ)⁻¹ • Superoperator.choi b LinearMap.id)) at h
  simpa only [swap, Density.op_mixture, Density.op_tensor, map_sum, map_smul,
    Superoperator.choi_apply, Superoperator.tensor_apply, LinearMap.id_apply,
    Superoperator.relabel_comm_tensor, choiState] using h

/-- A separable normalized Choi state yields a channel with two copies of the original
channel as its marginals. The prepared output states may be mixed and nonorthogonal. -/
theorem exists_joint_channel_of_isSeparable_choiState (b : OrthonormalBasis ι ℂ H.state)
    (hH : 0 < Module.finrank ℂ H.state) (hsep : (Φ.choiState b hH).IsSeparable) :
    ∃ Ψ : QuantumChannel H (K ⊗ K),
      (partialTraceRight K K).comp Ψ = Φ ∧ (partialTraceLeft K K).comp Ψ = Φ := by
  obtain ⟨α, _, M, σ, rfl⟩ := exists_measurePrepare_of_isSeparable_choiState b hH hsep
  exact (compatible_iff_exists_joint_channel _ _).mp (compatible_measurePrepare M σ σ)

/-- Every entanglement-breaking channel is antidegradable for its chosen standard complement,
including a channel with zero-dimensional input or output. -/
theorem IsEntanglementBreaking.isAntidegradable (hΦ : Φ.IsEntanglementBreaking) :
    Φ.IsAntidegradable := by
  by_cases hH : 0 < Module.finrank ℂ H.state
  · let b := stdOrthonormalBasis ℂ H.state
    obtain ⟨Ψ, hr, hl⟩ := exists_joint_channel_of_isSeparable_choiState b hH
      (hΦ.isSeparable_choiState b hH)
    exact isAntidegradable_of_joint_channel Φ Ψ hr hl
  · exact isAntidegradable_of_finrank_eq_zero Φ (by lia)

/-- For an explicit dilation of an entanglement-breaking channel, antidegradation is possible
exactly when the environment admits a channel to the output. -/
theorem IsEntanglementBreaking.complementary_isDegradableTo_iff (hΦ : Φ.IsEntanglementBreaking)
    (d : Φ.Dilation E) :
    d.complementary.IsDegradableTo Φ ↔
      (0 < Module.finrank ℂ E.state → 0 < Module.finrank ℂ K.state) := by
  refine ⟨fun ⟨D, _⟩ => D.finrank_pos_of_input, fun h => ?_⟩
  by_cases hH : 0 < Module.finrank ℂ H.state
  · exact (d.isAntidegradable_iff hH).mp hΦ.isAntidegradable
  · have : Subsingleton H.state := Module.finrank_zero_iff.mp (Nat.eq_zero_of_not_pos hH)
    obtain ⟨D⟩ := (nonempty_iff_finrank_pos E K).mpr h
    exact ⟨D, QuantumChannel.ext (Subsingleton.elim _ _)⟩

/-- For zero-dimensional input there are no joint input densities, so every channel is
entanglement-breaking for every reference dimension. -/
theorem isEntanglementBreaking_of_finrank_eq_zero (Φ : QuantumChannel H K)
    (hH : Module.finrank ℂ H.state = 0) : Φ.IsEntanglementBreaking := by
  intro R ρ
  have hd : Module.finrank ℂ (R ⊗ H).state = Module.finrank ℂ R.state * Module.finrank ℂ H.state :=
    Module.finrank_tensorProduct
  have : Subsingleton (R ⊗ H).state := Module.finrank_zero_iff.mp (by rw [hd, hH, mul_zero])
  exact isEmptyElim ρ

end

end Qudit.QuantumChannel
