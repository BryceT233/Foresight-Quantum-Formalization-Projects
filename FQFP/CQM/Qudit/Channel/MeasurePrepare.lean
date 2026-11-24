/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the replacement channel.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
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

## Main definitions and results

* `Qudit.QuantumChannel.replacement`: the channel that prepares a fixed density.
* `Qudit.POVM.measurePrepare`: measurement followed by outcome-dependent state preparation.
* `Qudit.POVM.measurePrepareInstrument`: the corresponding instrument with outcomes retained.
* `Qudit.POVM.map_measurePrepare`: the output is the ensemble mixed with Born probabilities.
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
def measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) : Instrument H K ι :=
  Instrument.ofCPMaps (fun i => M.effect i ≫ (σ i).toCPState)
    (M.isInstrument_effect.postprocess fun i => (σ i).isCausal_toCPState)

/-- Each branch is exactly the Born weight times its prepared output, on all operators. -/
lemma measurePrepareInstrument_branch (M : POVM H ι) (σ : ι → Density K)
    (i : ι) (A : Operator H) :
    (M.measurePrepareInstrument σ).branch i A = (M.op i * A).trace • (σ i).op := by
  change Superoperator.prepare (σ i).op ((M.effect i).toSuperoperator A) = _
  rw [Superoperator.prepare_apply, M.effect_apply, Operator.trace_scalar]
  simp only [LinearMap.smul_apply, one_apply_eq_self, smul_eq_mul, mul_one]

/-- The instrument branch is the categorical effect followed by preparation. -/
lemma branchCPMap_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) (i : ι) :
    (M.measurePrepareInstrument σ).branchCPMap i = M.effect i ≫ (σ i).toCPState := rfl

/-- Forget the outcome of a measurement followed by outcome-dependent preparation. -/
def measurePrepare (M : POVM H ι) (σ : ι → Density K) : QuantumChannel H K :=
  (M.measurePrepareInstrument σ).toChannel

/-- Forgetting the outcome sums the composites of effects and preparations as CP arrows. -/
lemma toCPMap_measurePrepare (M : POVM H ι) (σ : ι → Density K) :
    (M.measurePrepare σ).toCPMap = ∑ i, M.effect i ≫ (σ i).toCPState :=
  (M.measurePrepareInstrument σ).sum_branchCPMap_eq.symm

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

/-- The POVM induced by this instrument is the original measurement. -/
lemma toPOVM_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K) :
    (M.measurePrepareInstrument σ).toPOVM = M := by
  apply ext_effect
  intro i
  rw [Instrument.effect_toPOVM, branchCPMap_measurePrepareInstrument, Category.assoc]
  have hs : (σ i).toCPState ≫ CPQudit.discard ⟨K⟩ = 𝟙 _ :=
    (CPQudit.discarding.isCausal_state_iff _).mp (σ i).isCausal_toCPState
  rw [hs, Category.comp_id]

/-- Preparing a new state does not change the probability of the preceding measurement. -/
lemma probability_measurePrepareInstrument (M : POVM H ι) (σ : ι → Density K)
    (ρ : Density H) (i : ι) :
    (M.measurePrepareInstrument σ).probability ρ i = M.probability ρ i := by
  rw [← Instrument.probability_toPOVM, toPOVM_measurePrepareInstrument]

/-- If every outcome prepares the same state, the channel is replacement. -/
lemma measurePrepare_const (M : POVM H ι) (σ : Density K) :
    M.measurePrepare (fun _ => σ) = QuantumChannel.replacement H σ := by
  apply CausalQudit.inclusion.map_injective (X := ⟨H⟩) (Y := ⟨K⟩)
  change (M.measurePrepare _).toCPMap = CPQudit.discard ⟨H⟩ ≫ σ.toCPState
  rw [toCPMap_measurePrepare, ← Semiadditive.sum_comp, M.sum_effect_eq_discard]

/-- Subsequent quantum processing acts only on the prepared states. -/
lemma comp_measurePrepare (M : POVM H ι) (σ : ι → Density K) (Φ : QuantumChannel K L) :
    Φ.comp (M.measurePrepare σ) = M.measurePrepare (fun i => Φ.map (σ i)) := by
  apply QuantumChannel.asCPHom_injective
  rw [QuantumChannel.asCPHom_comp]
  simp only [QuantumChannel.asCPHom, toCPMap_measurePrepare, Semiadditive.sum_comp,
    Category.assoc, Density.toCPState_comp]

/-- Prior quantum processing pulls back the measurement and leaves the preparation family fixed. -/
lemma measurePrepare_comp {G : Qudit} (M : POVM H ι) (σ : ι → Density K)
    (Φ : QuantumChannel G H) :
    (M.measurePrepare σ).comp Φ = (M.pullback Φ).measurePrepare σ := by
  apply QuantumChannel.asCPHom_injective
  rw [QuantumChannel.asCPHom_comp]
  simp only [QuantumChannel.asCPHom, toCPMap_measurePrepare, Semiadditive.comp_sum,
    effect_pullback, Category.assoc]

end POVM

end

end Qudit
