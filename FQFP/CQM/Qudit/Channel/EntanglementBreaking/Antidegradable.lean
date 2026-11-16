/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.BroadcastExtension
public import FQFP.CQM.Qudit.Channel.ChoiState
public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.Basic

/-!
# Entanglement-breaking channels are antidegradable

Applying an entanglement-breaking channel to the maximally entangled input gives a separable
Choi state. Each product term admits a joint extension with two copies of its output density.
The extended positive Choi operator defines a joint channel with both marginals equal to the
original channel. A partial trace of the joint Stinespring environment recovers the output.
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
  obtain ⟨j, _, w, hw, hs, s, r, he⟩ := (Density.isSeparable_iff_exists_mixture _).mp hsep
  let τ := Density.mixture w hw hs (fun i => ((s i).tensor (s i)).tensor (r i))
  let n : ℂ := Module.finrank ℂ H.state
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast hH.ne'
  obtain ⟨S, hcp, hS⟩ := Superoperator.exists_of_choi_positive b (n • τ.op)
    (τ.positive.smul_of_nonneg (by dsimp [n]; positivity))
  have hm (Γ : QuantumChannel (K ⊗ K) K)
      (hΓ : ∀ i, Γ.map ((s i).tensor (s i)) = s i) :
      Γ.toSuperoperator ∘ₗ S = Φ.toSuperoperator := by
    apply Superoperator.choi_injective b
    rw [Superoperator.choi_comp, hS, map_smul]
    have hτ : Superoperator.tensor Γ.toSuperoperator (LinearMap.id : Superoperator H H) τ.op =
        (Φ.choiState b hH).op := by
      rw [← he]
      simp only [τ, Density.op_mixture, Density.op_tensor, map_sum, map_smul,
        Superoperator.tensor_apply, LinearMap.id_apply]
      exact Finset.sum_congr rfl fun i _ =>
        congrArg (fun A => (w i : ℂ) • Operator.tensor A (r i).op) (congrArg Density.op (hΓ i))
    rw [hτ]
    change n • (n⁻¹ • _) = _
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hr := hm (partialTraceRight K K) (fun i => (map_partialTraceRight _).trans
    (Density.partialTraceRight_tensor _ _))
  have hl := hm (partialTraceLeft K K) (fun i => (map_partialTraceLeft _).trans
    (Density.partialTraceLeft_tensor _ _))
  have htp : S.IsTracePreserving := by
    intro A
    calc
      _ = (Operator.partialTraceRight (S A)).trace := (LinearMap.trace_partialTraceRight _).symm
      _ = _ := (congrArg Operator.trace (LinearMap.congr_fun hr A)).trans (Φ.tracePreserving A)
  exact ⟨⟨S, hcp, htp⟩, QuantumChannel.ext hr, QuantumChannel.ext hl⟩

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
