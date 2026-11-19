/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the proposed entanglement-breaking predicate.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Measurement.Ensemble

/-!
# Measurement and preparation break entanglement

An entanglement-breaking channel produces a separable state when applied to one part of
any bipartite input, with an arbitrary finite-dimensional reference system. This is stronger
than preserving already separable states. Measurement followed by preparation has this
property: the reference's conditional states give an explicit finite product decomposition.
Zero-probability outcomes are handled by the instrument ensemble API without division by zero.

## Main definitions and results

* `Qudit.QuantumChannel.IsEntanglementBreaking`: separable outputs for every reference system.
* `Qudit.POVM.isEntanglementBreaking_measurePrepare`: measurement and preparation break
  entanglement.
* `Qudit.QuantumChannel.IsEntanglementBreaking.comp_left`: closure under channel postprocessing.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit

noncomputable section

variable {H K : Qudit} {ι : Type*} [Fintype ι]

/-- A channel breaks all entanglement with any finite-dimensional reference system. -/
def QuantumChannel.IsEntanglementBreaking (Φ : QuantumChannel H K) : Prop :=
  ∀ (R : Qudit) (ρ : Density (R ⊗ H)), (((QuantumChannel.id R).tensor Φ).map ρ).IsSeparable

namespace POVM

/-- Measure the right subsystem and retain only the reference system and outcome label. -/
def referenceInstrument (M : POVM H ι) (R : Qudit) : Instrument (R ⊗ H) R ι :=
  (M.luders.tensorLeft (QuantumChannel.id R)).postprocess
    (fun _ => QuantumChannel.partialTraceRight R H)

/-- On product operators, a reference branch is the local effect weight times the reference. -/
lemma referenceInstrument_branch_tensor (M : POVM H ι) (R : Qudit) (i : ι)
    (A : Operator R) (B : Operator H) :
    (M.referenceInstrument R).branch i (Operator.tensor A B) = (M.op i * B).trace • A := by
  change Operator.partialTraceRight
    (Superoperator.tensor LinearMap.id (M.luders.branch i) (Operator.tensor A B)) = _
  rw [Superoperator.tensor_apply, LinearMap.id_apply, Operator.partialTraceRight_tensor,
    M.trace_luders_branch]

/-- The joint output is a sum of unnormalized reference branches tensored with prepared states. -/
lemma tensor_measurePrepare_apply (M : POVM H ι) (σ : ι → Density K) (R : Qudit)
    (A : Operator (R ⊗ H)) :
    ((QuantumChannel.id R).tensor (M.measurePrepare σ)).toSuperoperator A =
      ∑ i, Operator.tensor ((M.referenceInstrument R).branch i A) (σ i).op := by
  induction A using Operator.tensor_induction_on with
  | htensor A B =>
    change Superoperator.tensor LinearMap.id (M.measurePrepare σ).toSuperoperator
      (Operator.tensor A B) = _
    rw [Superoperator.tensor_apply, LinearMap.id_apply, M.measurePrepare_apply]
    simp only [referenceInstrument_branch_tensor]
    simp only [Operator.tensor,
      ← TensorProduct.mapBilinear_apply, map_sum, map_smul, LinearMap.smul_apply]
  | hadd A B hA hB =>
    simp only [map_add, hA, hB, Operator.tensor, TensorProduct.map_add_left,
      Finset.sum_add_distrib]

/-- Measurement and preparation give separable outputs even from entangled joint inputs. -/
lemma isEntanglementBreaking_measurePrepare (M : POVM H ι) (σ : ι → Density K) :
    (M.measurePrepare σ).IsEntanglementBreaking := by
  intro R ρ
  let e := (M.referenceInstrument R).outputEnsemble ρ ρ.partialTraceRight
  have heq : ((QuantumChannel.id R).tensor (M.measurePrepare σ)).map ρ =
      Density.mixture e.weight e.weight_nonneg e.sum_weight
        (fun i => (e.state i).tensor (σ i)) := by
    apply Density.ext
    rw [QuantumChannel.op_map, tensor_measurePrepare_apply, Density.op_mixture]
    apply Finset.sum_congr rfl
    intro i _
    rw [Density.op_tensor]
    rw [← Instrument.weight_smul_outputEnsemble _ ρ ρ.partialTraceRight i]
    exact TensorProduct.map_smul_left _ _ _
  rw [heq]
  exact Density.isSeparable_mixture_tensor _ _ _ _ _

end POVM

namespace QuantumChannel

/-- Processing an entanglement-breaking output by a channel cannot recreate entanglement. -/
lemma IsEntanglementBreaking.comp_left {Φ : QuantumChannel H K} (hΦ : Φ.IsEntanglementBreaking)
    {L : Qudit} (Ψ : QuantumChannel K L) : (Ψ.comp Φ).IsEntanglementBreaking := by
  intro R ρ
  have h := (hΦ R ρ).map_tensor (QuantumChannel.id R) Ψ
  have heq : ((QuantumChannel.id R).tensor Ψ).comp ((QuantumChannel.id R).tensor Φ) =
      (QuantumChannel.id R).tensor (Ψ.comp Φ) := by
    apply QuantumChannel.ext
    exact (Superoperator.tensor_comp _ _ _ _).symm
  simpa only [← map_comp, heq] using h

end QuantumChannel

end

end Qudit
