/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the recorded measurement and its two marginals.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Measurements/POVM.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.Instrument
public import FQFP.CQM.Qudit.Measurement.POVM

/-!
# Instruments with a classical result register

An explicit orthonormal basis encodes the finite outcomes. Recording an instrument gives
a channel with block-diagonal output `∑ i, Iᵢ(A) ⊗ |bᵢ⟩⟨bᵢ|`. Its two marginals recover
the unread quantum output and the classical probability distribution. Classical control
reads this register, applies an outcome-dependent channel, and retains the result label.

## Main definitions and results

* `Qudit.Instrument.record`: the channel retaining the output and an orthogonal outcome register.
* `Qudit.Instrument.read`: reading and discarding a classical register.
* `Qudit.Instrument.read_record`: reading a recorded outcome recovers the original branch.
* `Qudit.QuantumChannel.controlled`: a channel controlled by the classical basis label.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators

namespace Qudit

noncomputable section

namespace Density

variable {H C : Qudit} {ι : Type*} [Fintype ι]

/-- A mixture with its classical label retained as an orthogonal state in the right register. -/
def flaggedMixture (b : OrthonormalBasis ι ℂ C.state) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (ρ : ι → Density H) : Density (H ⊗ C) :=
  mixture w hw hs fun i => (ρ i).tensor (pure (UnitState.ofBasis b i))

/-- Discarding the classical register recovers the original mixture. -/
lemma partialTraceRight_flaggedMixture (b : OrthonormalBasis ι ℂ C.state)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ρ : ι → Density H) :
    (flaggedMixture b w hw hs ρ).partialTraceRight = mixture w hw hs ρ := by
  apply Density.ext
  simp [flaggedMixture, Operator.partialTraceRight_tensor]

/-- On label `i` the flagged density acts as its weighted quantum block `w i • (ρ i).op`. -/
lemma flaggedMixture_apply_tmul (b : OrthonormalBasis ι ℂ C.state)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (ρ : ι → Density H)
    (i : ι) (x : H.state) :
    (flaggedMixture b w hw hs ρ).op (x ⊗ₜ[ℂ] b i) = (w i : ℂ) • ((ρ i).op x ⊗ₜ[ℂ] b i) := by
  classical
  simp only [flaggedMixture, op_mixture, LinearMap.sum_apply, LinearMap.smul_apply, op_tensor,
    Operator.tensor_apply, pure_apply, UnitState.coe_ofBasis, b.inner_eq_ite]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

end Density

namespace Superoperator

variable {H C : Qudit}

/-- Appending a pure state is conjugation by tensor insertion, hence is completely positive. -/
lemma conjugate_tensorInsertion (v : C.state) (A : Operator H) :
    conjugate ((TensorProduct.mk ℂ H.state C.state).flip v) A =
      Operator.tensor A (Operator.outer v v) := by
  apply TensorProduct.ext'
  intro x y
  change ((TensorProduct.mk ℂ H.state C.state).flip v)
    (A (((TensorProduct.mk ℂ H.state C.state).flip v).adjoint (x ⊗ₜ y))) =
      A x ⊗ₜ (inner ℂ v y • v)
  rw [adjoint_tensorInsertion_apply, map_smul]
  change (inner ℂ v y • A x) ⊗ₜ v = A x ⊗ₜ (inner ℂ v y • v)
  exact TensorProduct.smul_tmul _ _ _

end Superoperator

namespace Instrument

variable {H K L C : Qudit} {ι : Type*} [Fintype ι]

/-- Retain the quantum output and record the outcome in the chosen classical basis. -/
def record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state) :
    QuantumChannel H (K ⊗ C) where
  toSuperoperator := ∑ i,
    Superoperator.conjugate ((TensorProduct.mk ℂ K.state C.state).flip (b i)) ∘ₗ I.branch i
  completelyPositive := Superoperator.IsCompletelyPositive.sum _ _ fun i _ =>
    (Superoperator.isCompletelyPositive_conjugate _).comp (I.completelyPositive i)
  tracePreserving A := by
    rw [LinearMap.sum_apply, Operator.trace, map_sum]
    change ∑ i, (Superoperator.conjugate (H := K) (K := K ⊗ C)
      ((TensorProduct.mk ℂ K.state C.state).flip (b i)) (I.branch i A)).trace = A.trace
    simpa only [Superoperator.conjugate_tensorInsertion, Operator.trace_tensor,
      Operator.trace_outer, b.inner_eq_one, mul_one] using I.sum_trace_branch A

/-- The recorded operator is block diagonal, with the unnormalized branches as its blocks. -/
lemma record_apply (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state) (A : Operator H) :
    (I.record b).toSuperoperator A =
      ∑ i, Operator.tensor (I.branch i A) (Operator.outer (b i) (b i)) :=
  by simp only [record, LinearMap.sum_apply, LinearMap.comp_apply,
    Superoperator.conjugate_tensorInsertion]

/-- Recording an outcome and discarding its register implements the unread instrument channel. -/
lemma partialTraceRight_comp_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state) :
    (QuantumChannel.partialTraceRight K C).comp (I.record b) = I.toChannel := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change Operator.partialTraceRight ((I.record b).toSuperoperator A) = I.toChannel.toSuperoperator A
  simp only [record_apply, map_sum,
    Operator.partialTraceRight_tensor, Operator.trace_outer, b.inner_eq_one, one_smul]
  exact (LinearMap.sum_apply _ _ _).symm

/-- Discarding the classical register gives the unread instrument channel. -/
lemma partialTraceRight_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) : ((I.record b).map ρ).partialTraceRight = I.toChannel.map ρ := by
  rw [← I.partialTraceRight_comp_record b, QuantumChannel.map_comp,
    QuantumChannel.map_partialTraceRight]

/-- The classical outcome distribution as a diagonal density operator in the chosen basis. -/
def outcomeState (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) : Density C :=
  Density.mixture (I.probability ρ) (I.probability_nonneg ρ) (I.sum_probability ρ)
    (fun i => Density.pure (UnitState.ofBasis b i))

/-- The operator of the classical outcome distribution. -/
lemma op_outcomeState (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) :
    (I.outcomeState b ρ).op = ∑ i, (I.probability ρ i : ℂ) • Operator.outer (b i) (b i) := rfl

/-- Discarding the quantum output leaves precisely the classical distribution. -/
lemma partialTraceLeft_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) : ((I.record b).map ρ).partialTraceLeft = I.outcomeState b ρ := by
  apply Density.ext
  simp only [Density.op_partialTraceLeft, QuantumChannel.op_map, record_apply, map_sum,
    Operator.partialTraceLeft_tensor, op_outcomeState, probability_eq_trace]

/-- Reading the recorded classical distribution reproduces the instrument probabilities. -/
lemma probability_outcomeState (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) (i : ι) :
    (POVM.ofBasis b).probability (I.outcomeState b ρ) i = I.probability ρ i := by
  classical
  rw [outcomeState, POVM.probability_mixture]
  simp [POVM.probability_ofBasis_ofBasis, apply_ite]

/-- Read a classical register and discard its carrier, retaining the quantum subsystem. -/
def read (K : Qudit) (b : OrthonormalBasis ι ℂ C.state) : Instrument (K ⊗ C) K ι :=
  ofOperators (fun i => ((TensorProduct.mk ℂ K.state C.state).flip (b i)).adjoint)
    ((Superoperator.isTracePreserving_kraus_iff _).mp (by
      rw [← Superoperator.partialTraceRight_eq_kraus b]
      exact (QuantumChannel.partialTraceRight K C).tracePreserving))

/-- Reading a diagonal block selects exactly its classical label. -/
lemma read_branch_tensor [DecidableEq ι] (b : OrthonormalBasis ι ℂ C.state)
    (A : Operator K) (i j : ι) :
    (read K b).branch i (Operator.tensor A (Operator.outer (b j) (b j))) =
      if i = j then A else 0 := by
  classical
  change Superoperator.conjugate (H := K ⊗ C) (K := K)
    (((TensorProduct.mk ℂ K.state C.state).flip (b i)).adjoint) _ = _
  rw [Superoperator.conjugate_apply, LinearMap.adjoint_adjoint]
  ext x
  change ((TensorProduct.mk ℂ K.state C.state).flip (b i)).adjoint
    (A x ⊗ₜ (inner ℂ (b j) (b i) • b j)) = _
  rw [TensorProduct.tmul_smul, map_smul, Superoperator.adjoint_tensorInsertion_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [b.inner_eq_ite, hij, Ne.symm hij]

/-- Selecting a recorded result recovers its original unnormalized quantum branch. -/
lemma read_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (A : Operator H) (i : ι) :
    (read K b).branch i ((I.record b).toSuperoperator A) = I.branch i A := by
  classical
  rw [record_apply, map_sum]
  simp only [read_branch_tensor]
  simp

/-- Reading the register of a recorded measurement recovers the original outcome probability. -/
lemma probability_read_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) (i : ι) :
    (read K b).probability ((I.record b).map ρ) i = I.probability ρ i := by
  simp only [probability, QuantumChannel.op_map, read_record]

/-- Reading a recorded positive-probability outcome recovers its original conditional state. -/
lemma conditional_read_record (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (ρ : Density H) (i : ι) (hp : 0 < I.probability ρ i) :
    (read K b).conditional ((I.record b).map ρ) i
      (by simpa only [probability_read_record] using hp) = I.conditional ρ i hp := by
  apply Density.ext
  simp only [op_conditional, probability_read_record, QuantumChannel.op_map, read_record]

end Instrument

namespace QuantumChannel

variable {K L C : Qudit} {ι : Type*} [Fintype ι]

/-- Classical control: read the basis label, apply its channel, and retain the label.
On general inputs this also dephases the register; it is not a coherent controlled unitary. -/
def controlled (b : OrthonormalBasis ι ℂ C.state) (Φ : ι → QuantumChannel K L) :
    QuantumChannel (K ⊗ C) (L ⊗ C) := ((Instrument.read K b).postprocess Φ).record b

/-- On a classical block the channel indexed by that label is applied. -/
lemma controlled_tensor (b : OrthonormalBasis ι ℂ C.state) (Φ : ι → QuantumChannel K L)
    (A : Operator K) (j : ι) :
    (controlled b Φ).toSuperoperator (Operator.tensor A (Operator.outer (b j) (b j))) =
      Operator.tensor ((Φ j).toSuperoperator A) (Operator.outer (b j) (b j)) := by
  classical
  rw [controlled, Instrument.record_apply]
  simp only [Instrument.postprocess_branch_apply, Instrument.read_branch_tensor]
  simp [apply_ite, Operator.tensor, ← TensorProduct.mapBilinear_apply, ite_apply]

end QuantumChannel

namespace Instrument

/-- Recording followed by classical control agrees with conditional processing then recording. -/
lemma record_postprocess {H K L C : Qudit} {ι : Type*} [Fintype ι]
    (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (Φ : ι → QuantumChannel K L) :
    (I.postprocess Φ).record b = (QuantumChannel.controlled b Φ).comp (I.record b) := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change _ = (QuantumChannel.controlled b Φ).toSuperoperator ((I.record b).toSuperoperator A)
  rw [record_apply, record_apply, map_sum]
  simp only [QuantumChannel.controlled_tensor, postprocess_branch_apply]

/-- Reading the register after classical control selects the processed branch at that label. -/
lemma read_controlled_record {H K L C : Qudit} {ι : Type*} [Fintype ι]
    (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state)
    (Φ : ι → QuantumChannel K L) (A : Operator H) (i : ι) :
    (read L b).branch i ((QuantumChannel.controlled b Φ).toSuperoperator
      ((I.record b).toSuperoperator A)) = (Φ i).toSuperoperator (I.branch i A) := by
  change (read L b).branch i (((QuantumChannel.controlled b Φ).comp (I.record b)).toSuperoperator A)
    = _
  rw [← I.record_postprocess b Φ, read_record, postprocess_branch_apply]

end Instrument

end

end Qudit
