/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Ensemble
public import FQFP.CQM.Qudit.Measurement.Process

/-!
# Replacement and measurement followed by preparation

A replacement channel discards its input and prepares a fixed density state, as in
physlib's `CPTPMap.replacement`. More generally, a POVM and a family of density states
define an instrument whose branches are CP effects followed by CP preparations.
Forgetting the outcome gives the channel `A ↦ ∑ i, Tr(Eᵢ A) • σᵢ`.
The concrete state, instrument, and categorical process APIs agree on this construction.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators ComplexOrder

namespace Qudit

noncomputable section

namespace QuantumChannel

variable {H K : Qudit}

/-- Discard the input and prepare a fixed density state. -/
def replacement (H : Qudit) (σ : Density K) : QuantumChannel H K :=
  CausalQudit.discard ⟨H⟩ ≫ σ.toState

/-- Replacement acts by multiplying the prepared state by the input trace. -/
lemma replacement_apply (σ : Density K) (A : Operator H) :
    (replacement H σ).toSuperoperator A = A.trace • σ.op := by
  change Superoperator.prepare σ.op (Superoperator.discard H A) = _
  rw [Superoperator.prepare_apply, Superoperator.isTracePreserving_discard H A]

/-- Replacement sends every input density state to its specified output. -/
@[simp]
lemma map_replacement (σ : Density K) (ρ : Density H) : (replacement H σ).map ρ = σ := by
  apply Density.ext
  simp only [op_map, replacement_apply, ρ.trace_one, one_smul]

end QuantumChannel

namespace POVM

variable {H K L : Qudit} {ι : Type*} [Fintype ι]

/-- Measure a POVM and prepare the density state associated with the observed label. -/
def measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) : Instrument H K ι where
  branch i := (M.effect i ≫ (σ i).toCPState).toSuperoperator
  completelyPositive i := (M.effect i ≫ (σ i).toCPState).completelyPositive
  tracePreserving A := by
    change ((∑ i, Superoperator.prepare (σ i).op ∘ₗ (M.effect i).toSuperoperator) A).trace = _
    simp only [LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
      Superoperator.prepare_apply, map_smul, Density.trace_one, smul_eq_mul, mul_one]
    rw [← map_sum, ← LinearMap.sum_apply, M.sum_effect]
    exact Superoperator.isTracePreserving_discard H A

/-- Each branch is exactly the Born weight times its prepared output, on all operators. -/
lemma measurePrepareInstrument_branch (M : POVM H ι) (σ : ι → Density K)
    (i : ι) (A : Operator H) :
    (M.measurePrepareInstrument σ).branch i A = (M.op i * A).trace • (σ i).op := by
  change Superoperator.prepare (σ i).op ((M.effect i).toSuperoperator A) = _
  rw [Superoperator.prepare_apply, M.effect_apply, Operator.trace_scalar]
  simp only [LinearMap.smul_apply, Module.End.one_apply, smul_eq_mul, mul_one]

/-- The instrument branch is the categorical effect followed by preparation. -/
lemma branchCPMap_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) (i : ι) :
    (M.measurePrepareInstrument σ).branchCPMap i = M.effect i ≫ (σ i).toCPState := rfl

/-- Forget the outcome of a measurement followed by outcome-dependent preparation. -/
def measurePrepare (M : POVM H ι) (σ : ι → Density K) : QuantumChannel H K :=
  (M.measurePrepareInstrument σ).toChannel

/-- The measure-and-prepare formula holds on all operators, without positivity assumptions. -/
lemma measurePrepare_apply (M : POVM H ι) (σ : ι → Density K) (A : Operator H) :
    (M.measurePrepare σ).toSuperoperator A = ∑ i, (M.op i * A).trace • (σ i).op := by
  change (∑ i, (M.measurePrepareInstrument σ).branch i) A = _
  simp only [LinearMap.sum_apply, measurePrepareInstrument_branch]

/-- The output ensemble is distributed by the input state's Born probabilities. -/
def prepareEnsemble (M : POVM H ι) (σ : ι → Density K) (ρ : Density H) : Ensemble K ι :=
  Ensemble.ofWeights (M.probability ρ) (M.probability_nonneg ρ) (M.sum_probability ρ) σ

/-- The output density state is the mixture of the prepared ensemble. -/
lemma map_measurePrepare (M : POVM H ι) (σ : ι → Density K) (ρ : Density H) :
    (M.measurePrepare σ).map ρ = (M.prepareEnsemble σ ρ).mix := by
  apply Density.ext
  simp only [QuantumChannel.op_map, measurePrepare_apply, Ensemble.op_mix]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (· • (σ i).op) (M.probability_eq_trace ρ i).symm

/-- Preparing a new state does not change the probability of the preceding measurement. -/
lemma probability_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K)
    (ρ : Density H) (i : ι) :
    (M.measurePrepareInstrument σ).probability ρ i = M.probability ρ i := by
  simp only [Instrument.probability, measurePrepareInstrument_branch, map_smul,
    Density.trace_one, smul_eq_mul, mul_one]
  rfl

/-- The POVM induced by this instrument is the original measurement. -/
lemma toPOVM_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) :
    (M.measurePrepareInstrument σ).toPOVM = M := by
  apply POVM.ext
  funext i
  apply Operator.ext_trace
  intro A
  rw [Instrument.toPOVM, CPMap.trace_dual, one_mul]
  change ((M.measurePrepareInstrument σ).branch i A).trace = _
  simp only [measurePrepareInstrument_branch, map_smul, Density.trace_one, smul_eq_mul, mul_one]

/-- If every outcome prepares the same state, the channel is replacement. -/
lemma measurePrepare_const (M : POVM H ι) (σ : Density K) :
    M.measurePrepare (fun _ => σ) = QuantumChannel.replacement H σ := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  rw [measurePrepare_apply, QuantumChannel.replacement_apply, ← Finset.sum_smul,
    ← map_sum, ← Finset.sum_mul, M.sum_op, one_mul]

/-- Subsequent quantum processing acts only on the prepared states. -/
lemma comp_measurePrepare (M : POVM H ι) (σ : ι → Density K) (Φ : QuantumChannel K L) :
    Φ.comp (M.measurePrepare σ) = M.measurePrepare (fun i => Φ.map (σ i)) := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change Φ.toSuperoperator ((M.measurePrepare σ).toSuperoperator A) = _
  simp only [measurePrepare_apply, map_sum, map_smul, QuantumChannel.op_map]

end POVM

end

end Qudit
