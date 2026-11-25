/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Ensemble
public import FQFP.CQM.Qudit.Channel.Process.Category
public import FQFP.CQM.Qudit.Measurement.Instrument

/-!
# Instruments and their output ensembles

An instrument determines a finite ensemble of conditional outputs. A supplied fallback
state fills zero-probability labels, where conditioning has no meaning; it does not affect
the mixed output. Tensoring an instrument with an independent channel retains the labels.

## Main definitions and results

* `Qudit.Instrument.outputEnsemble`: the ensemble of conditional outputs, with a zero-weight
  fallback.
* `Qudit.Instrument.mix_outputEnsemble`: mixing outputs agrees with forgetting the instrument
  outcome.
* `Qudit.Instrument.tensorLeft` and `Qudit.Instrument.tensorRight` adjoin an independent channel.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit.Instrument

noncomputable section

variable {H K R S : Qudit} {ι : Type*} [Fintype ι]

/-- Extend the conditional states to all labels using a fallback at impossible outcomes. -/
def outputEnsemble (I : Instrument H K ι) (ρ : Density H) (fallback : Density K) :
    Ensemble K ι :=
  Ensemble.ofWeights (I.probability ρ) (I.probability_nonneg ρ) (I.sum_probability ρ)
    (fun i => if hp : 0 < I.probability ρ i then I.conditional ρ i hp else fallback)

/-- Multiplying an ensemble member by its weight recovers the unnormalized branch. -/
lemma weight_smul_outputEnsemble (I : Instrument H K ι) (ρ : Density H)
    (fallback : Density K) (i : ι) :
    ((I.outputEnsemble ρ fallback).weight i : ℂ) •
      ((I.outputEnsemble ρ fallback).state i).op = I.branch i ρ.op := by
  change (I.probability ρ i : ℂ) •
    (if hp : 0 < I.probability ρ i then I.conditional ρ i hp else fallback).op = _
  split_ifs with hp
  · exact I.probability_smul_conditional ρ i hp
  · have hz : I.probability ρ i = 0 := le_antisymm (le_of_not_gt hp) (I.probability_nonneg ρ i)
    rw [I.branch_eq_zero_of_probability_eq_zero ρ i hz, hz, Complex.ofReal_zero, zero_smul]

/-- Forgetting the label recovers the channel output, independently of the fallback. -/
@[simp]
lemma mix_outputEnsemble (I : Instrument H K ι) (ρ : Density H) (fallback : Density K) :
    (I.outputEnsemble ρ fallback).mix = I.toChannel.map ρ := by
  apply Density.ext
  simp only [Ensemble.op_mix, weight_smul_outputEnsemble, op_toChannel_map]

/-- Run an independent channel on the left while retaining the instrument's outcomes. -/
def tensorLeft (I : Instrument H K ι) (Φ : QuantumChannel R S) :
    Instrument (R ⊗ H) (S ⊗ K) ι where
  branch i := Superoperator.tensor Φ.toSuperoperator (I.branch i)
  completelyPositive i := Φ.completelyPositive.tensor (I.completelyPositive i)
  tracePreserving := by
    rw [← Superoperator.tensor_sum_right]
    exact Φ.tracePreserving.tensor I.tracePreserving

/-- Forgetting the outcome commutes with adjoining the independent channel. -/
lemma toChannel_tensorLeft (I : Instrument H K ι) (Φ : QuantumChannel R S) :
    (I.tensorLeft Φ).toChannel = Φ.tensor I.toChannel := by
  apply QuantumChannel.ext
  exact (Superoperator.tensor_sum_right _ _ _).symm

/-- Run an independent channel on the right while retaining the instrument's outcomes. -/
def tensorRight (I : Instrument H K ι) (Φ : QuantumChannel R S) :
    Instrument (H ⊗ R) (K ⊗ S) ι where
  branch i := Superoperator.tensor (I.branch i) Φ.toSuperoperator
  completelyPositive i := (I.completelyPositive i).tensor Φ.completelyPositive
  tracePreserving := by
    rw [← Superoperator.tensor_sum_left]
    exact I.tracePreserving.tensor Φ.tracePreserving

/-- Forgetting the outcome commutes with adjoining a channel on the right. -/
lemma toChannel_tensorRight (I : Instrument H K ι) (Φ : QuantumChannel R S) :
    (I.tensorRight Φ).toChannel = I.toChannel.tensor Φ := by
  apply QuantumChannel.ext
  exact (Superoperator.tensor_sum_left _ _ _).symm

end

end Qudit.Instrument
