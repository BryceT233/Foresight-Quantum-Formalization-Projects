/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Channel.Classical

/-!
# State, effect and measurement process clients

Exercise the public bridges in complete experiments: a nonprojective POVM, complex
off-diagonal input, classical recording and readout, impossible outcomes, tensor
preparation, and mixed-state teleportation. Zero-dimensional states remain impossible.
-/

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped ComplexOrder BigOperators

noncomputable section

private def coin : POVM Qubit (Fin 2) where
  op _ := (1 / 2 : ℂ) • 1
  positive _ := LinearMap.isPositive_one.smul_of_nonneg
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  sum_op := by simp only [Fin.sum_univ_two, ← add_smul]; norm_num

-- A full-rank nonprojective effect gives probability 1/2, not its square 1/4.
example (ρ : Density Qubit) (i : Fin 2) :
    CPQudit.scalarValue (ρ.toCPState ≫ coin.effect i) = 1 / 2 := by
  rw [POVM.scalarValue_toCPState_comp_effect]
  simp [POVM.probability, coin, Density.expectation, Density.expectationComplex,
    Operator.trace, ρ.trace_one]

-- The same probability is obtained by actual recording, then reading the result register.
example (ρ : Density Qubit) (i : Fin 2) :
    CPQudit.scalarValue (ρ.toCPState ≫ (coin.outcomeChannel (ZBasis 2)).toCPMap ≫
      (POVM.ofBasis (ZBasis 2)).effect i) = 1 / 2 := by
  have h := congrArg
    (fun f : (⟨Qubit⟩ : CPQudit) ⟶ 𝟙_ CPQudit => CPQudit.scalarValue (ρ.toCPState ≫ f))
    (coin.outcomeChannel_comp_effect (ZBasis 2) i)
  apply h.trans
  rw [POVM.scalarValue_toCPState_comp_effect]
  simp [POVM.probability, coin, Density.expectation, Density.expectationComplex,
    Operator.trace, ρ.trace_one]

-- A branch is trace-nonincreasing but is not a deterministic channel.
example (i : Fin 2) : (coin.effect i).toSuperoperator.IsTraceNonincreasing ∧
    ¬ CPQudit.IsCausal (coin.effect i) := by
  refine ⟨coin.effect_isTraceNonincreasing i, ?_⟩
  rw [POVM.effect, CPQudit.effectOfPositive_isCausal_iff]
  intro h
  have e := congrArg (fun A : Operator Qubit => A (ZBasis 2 0)) h
  have e' := congrArg (fun v => inner ℂ (ZBasis 2 0) v) e
  norm_num [coin, inner_smul_right] at e'

-- The trace pairing is complex-linear on all operators, not just on density inputs.
example :
    (CPQudit.effectOfPositive
      (Operator.outer (ZBasis 2 0 + Complex.I • ZBasis 2 1)
        (ZBasis 2 0 + Complex.I • ZBasis 2 1))
      (Operator.isPositive_outer _)).toSuperoperator
        (Operator.outer (ZBasis 2 0) (ZBasis 2 1)) =
      Complex.I • (1 : Operator (𝟙_ Qudit)) := by
  rw [CPQudit.effectOfPositive_apply, Operator.trace_mul_outer]
  simp [Operator.outer_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, (ZBasis 2).inner_eq_ite]

-- Density and causal CP states round-trip without selecting a preferred basis.
example (H : Qudit) (f : 𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit)) (hf : CPQudit.IsCausal f) :
    ((Density.causalCPStateEquiv H).symm ⟨f, hf⟩).toCPState = f :=
  congrArg Subtype.val ((Density.causalCPStateEquiv H).apply_symm_apply ⟨f, hf⟩)

-- The zero-dimensional CP system has a zero preparation, but no density preparation.
example : (CPQudit.stateEquiv (std 0) ⟨0, LinearMap.isPositive_zero⟩).toSuperoperator 1 = 0 :=
  Superoperator.prepare_one _

example : IsEmpty (𝟙_ CausalQudit ⟶ (⟨std 0⟩ : CausalQudit)) :=
  ⟨fun f => isEmptyElim ((Density.causalStateEquiv (std 0)).symm f)⟩

-- Parallel preparation followed by independent channels agrees with the product output density.
example {H K L M : Qudit} (ρ : Density H) (σ : Density K)
    (Φ : QuantumChannel H L) (Ψ : QuantumChannel K M) :
    (λ_ (𝟙_ CausalQudit)).inv ≫ (ρ.toState ⊗ₘ σ.toState) ≫ (Φ ⊗ₘ Ψ) =
      ((Φ.map ρ).tensor (Ψ.map σ)).toState := by
  rw [← Category.assoc, ← Density.toState_tensor, Density.toState_comp]
  exact congrArg Density.toState (Φ.map_tensor Ψ ρ σ)

-- Recording and reading a general instrument preserves the full unnormalized branch state.
example {H K C : Qudit} {ι : Type*} [Fintype ι] (I : Instrument H K ι)
    (b : OrthonormalBasis ι ℂ C.state) (ρ : Density H) (i : ι) :
    ρ.toCPState ≫ (I.record b).toCPMap ≫ (Instrument.read K b).branchCPMap i =
      ρ.toCPState ≫ I.branchCPMap i := by
  rw [Instrument.record_comp_read]

-- Reading an impossible basis outcome gives zero, with no conditional density invented.
example :
    ((Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))).toCPState ≫
      (POVM.computational 2).luders.branchCPMap 1).toSuperoperator = 0 := by
  apply Instrument.toCPState_comp_branch_eq_zero
  simp [POVM.probability_luders, POVM.computational, POVM.probability_ofBasis_pure]

-- A real teleportation branch has probability 1/4 in the categorical experiment.
example (ρ : Density Qubit) (i : Fin 4) :
    CPQudit.scalarValue (ρ.toCPState ≫ teleportationMeasurement.branchCPMap i ≫
      CPQudit.discard ⟨Qubit⟩) = 1 / 4 := by
  rw [Instrument.scalarValue_branch, probability_teleportationMeasurement]

-- After correction, every branch is 1/4 times the original preparation.
example (ρ : Density Qubit) (i : Fin 4) :
    (ρ.toCPState ≫ teleportationInstrument.branchCPMap i).toSuperoperator =
      (1 / 4 : ℂ) • ρ.toCPState.toSuperoperator := by
  have hp : 0 < teleportationInstrument.probability ρ i := by
    rw [probability_teleportationInstrument]
    norm_num
  rw [Instrument.toCPState_comp_branch_conditional _ _ _ hp,
    conditional_teleportationInstrument, probability_teleportationInstrument]
  norm_num

-- The complete measured, recorded and corrected protocol preserves every prepared mixed state.
example (ρ : Density Qubit) :
    ρ.toState ≫ (teleportationMeasurement.record (ZBasis 4) :
      (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit ⊗ std 4⟩) ≫
      QuantumChannel.controlled (ZBasis 4) (fun i => QuantumChannel.ofIsometry (corrections i)) ≫
      QuantumChannel.partialTraceRight Qubit (std 4) = ρ.toState := by
  exact (congrArg (fun f : (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit⟩ => ρ.toState ≫ f)
    teleportation_causal_composite).trans (Category.comp_id _)
