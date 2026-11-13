/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Causal
public import FQFP.CQM.Qudit.Channel.Dual
public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Classical
public import FQFP.CQM.Qudit.Measurement.Luders
public import FQFP.CQM.Qudit.Measurement.Process
public import FQFP.CQM.Qudit.Teleportation.Instrument

/-!
# Classical structures inside the quantum process category

Copying in an orthonormal basis and discarding one copy is the unread projective
measurement. Its idempotent CP map represents the diagonal classical sector. Recorded
instrument outputs are fixed by this map on the register. This realizes classical
interfaces inside full matrix algebras; it does not identify arbitrary quantum maps
with maps of classical algebras, or construct the general `CP[C]` category.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

variable {H C : Qudit} {ι : Type*} [Fintype ι]

/-- Classical copying is an isometric pure process. -/
instance isIsometry_basisCopy (b : OrthonormalBasis ι ℂ H.state) : IsIsometry (basisCopy b) :=
  ⟨basisCopy_special b⟩

/-- Classical copying is the coherent dilation of the basis projection Kraus family. -/
lemma basisCopy_eq_krausDilation (b : OrthonormalBasis ι ℂ H.state) :
    (basisCopy b).hom = Superoperator.krausDilation b (fun i => Operator.outer (b i) (b i)) := by
  classical
  apply b.toBasis.ext
  intro j
  change basisCopy b (b j) = _
  rw [basisCopy_basis, Superoperator.krausDilation_apply]
  simp only [Operator.outer_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

namespace QuantumChannel

/-- Dephasing in a chosen classical structure: copy and discard the second output. -/
def dephase (b : OrthonormalBasis ι ℂ H.state) : QuantumChannel H H :=
  (partialTraceRight H H).comp (ofIsometry (basisCopy b))

/-- The copy-and-discard process is the sum of basis projection conjugations. -/
lemma dephase_eq_kraus (b : OrthonormalBasis ι ℂ H.state) :
    (dephase b).toSuperoperator = Superoperator.kraus (fun i => Operator.outer (b i) (b i)) := by
  change (Operator.partialTraceRight : Superoperator (H ⊗ H) H) ∘ₗ
    Superoperator.conjugate (basisCopy b).hom = _
  rw [basisCopy_eq_krausDilation]
  exact Superoperator.partialTraceRight_conjugate_krausDilation b _

/-- The classical structure induces precisely the unread basis Lüders measurement. -/
lemma dephase_eq_luders (b : OrthonormalBasis ι ℂ H.state) :
    dephase b = (POVM.ofBasis b).luders.toChannel := by
  apply QuantumChannel.ext
  rw [dephase_eq_kraus]
  apply LinearMap.ext
  intro A
  rw [Superoperator.kraus_apply]
  change _ = (∑ i, (POVM.ofBasis b).luders.branch i) A
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [POVM.luders_ofBasis_branch]
  ext x
  simp [smul_smul, mul_comm]

/-- Dephasing retains diagonal coefficients and erases off-diagonal coherence. -/
lemma dephase_apply (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (dephase b).toSuperoperator A =
      ∑ i, inner ℂ (b i) (A (b i)) • Operator.outer (b i) (b i) := by
  rw [dephase_eq_luders]
  change (∑ i, (POVM.ofBasis b).luders.branch i) A = _
  simp only [LinearMap.sum_apply, POVM.luders_ofBasis_branch]

/-- A classical basis projection is fixed by dephasing. -/
lemma dephase_outer (b : OrthonormalBasis ι ℂ H.state) (j : ι) :
    (dephase b).toSuperoperator (Operator.outer (b j) (b j)) = Operator.outer (b j) (b j) := by
  classical
  rw [dephase_apply]
  simp [b.inner_eq_ite, apply_ite]

/-- Dephasing is idempotent on all operators, not only density states. -/
lemma dephase_idempotent (b : OrthonormalBasis ι ℂ H.state) :
    (dephase b).comp (dephase b) = dephase b := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change (dephase b).toSuperoperator ((dephase b).toSuperoperator A) = _
  rw [dephase_apply b A, map_sum]
  simp only [map_smul, dephase_outer]

end QuantumChannel

namespace CPQudit

/-- The classical structure's CP decoherence process is its copying followed by discarding. -/
lemma dephase_copy_discard (b : OrthonormalBasis ι ℂ H.state) :
    (CausalQudit.inclusion.map (QuantumChannel.dephase b :
      (⟨H⟩ : CausalQudit) ⟶ ⟨H⟩)) =
      pure.map (basisCopy b) ≫ (𝟙 (⟨H⟩ : CPQudit) ⊗ₘ discard ⟨H⟩) ≫ (ρ_ (⟨H⟩ : CPQudit)).hom := by
  apply CPMap.ext
  exact congrArg (fun S => S ∘ₗ Superoperator.conjugate (basisCopy b).hom)
    (tensor_discard ⟨H⟩ ⟨H⟩).symm

end CPQudit

namespace Instrument

/-- A recorded instrument output is classical in its result register, even when the
retained quantum output is entangled with an external reference. -/
lemma record_dephase {K : Qudit} (I : Instrument H K ι)
    (b : OrthonormalBasis ι ℂ C.state) :
    ((QuantumChannel.id K).tensor (QuantumChannel.dephase b)).comp (I.record b) = I.record b := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change Superoperator.tensor LinearMap.id (QuantumChannel.dephase b).toSuperoperator
    ((I.record b).toSuperoperator A) = _
  rw [record_apply, map_sum]
  simp only [Superoperator.tensor_apply, LinearMap.id_apply, QuantumChannel.dephase_outer]

end Instrument

namespace POVM

/-- The classical outcome channel of a POVM, encoded in a chosen result basis.
The quantum post-measurement output is discarded. -/
def outcomeChannel (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) : QuantumChannel H C :=
  (QuantumChannel.partialTraceLeft H C).comp (M.luders.record b)

/-- The outcome channel depends only on the POVM effects through their trace pairings. -/
lemma outcomeChannel_apply (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state)
    (A : Operator H) :
    (M.outcomeChannel b).toSuperoperator A =
      ∑ i, (M.op i * A).trace • Operator.outer (b i) (b i) := by
  change Operator.partialTraceLeft ((M.luders.record b).toSuperoperator A) = _
  rw [Instrument.record_apply, map_sum]
  simp only [Operator.partialTraceLeft_tensor, trace_luders_branch]

/-- Encoding a POVM outcome in a basis is measurement followed by pure-state preparation. -/
lemma measurePrepare_basis (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) :
    M.measurePrepare (fun i => Density.pure (UnitState.ofBasis b i)) = M.outcomeChannel b := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  simp only [measurePrepare_apply, outcomeChannel_apply, Density.op_pure, UnitState.ofBasis]

/-- In the Heisenberg picture a classical outcome projection pulls back to its POVM
effect. This is the classical-to-quantum bridge, with the direction explicit. -/
lemma dual_outcomeChannel_projection (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state)
    (i : ι) :
    (M.outcomeChannel b).toCPMap.dual.toSuperoperator
        (Operator.outer (b i) (b i)) = M.op i := by
  classical
  apply Operator.ext_trace
  intro A
  rw [CPMap.trace_dual]
  change (Operator.outer (b i) (b i) * (M.outcomeChannel b).toSuperoperator A).trace = _
  rw [outcomeChannel_apply, Finset.mul_sum, Operator.trace, map_sum]
  simp only [mul_smul_comm, map_smul]
  change (∑ j, (M.op j * A).trace *
    (Operator.outer (b i) (b i) * Operator.outer (b j) (b j)).trace) = _
  simp [Operator.trace_mul_outer, b.inner_eq_ite, apply_ite]

/-- Reading a classical outcome after the measurement channel recovers the original effect. -/
lemma outcomeChannel_comp_effect (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) (i : ι) :
    (M.outcomeChannel b).toCPMap ≫ (ofBasis b).effect i = M.effect i := by
  change (M.outcomeChannel b).toCPMap ≫
    CPQudit.effectOfPositive (Operator.outer (b i) (b i)) (Operator.isPositive_outer (b i)) = _
  rw [CPQudit.comp_effectOfPositive]
  simp only [dual_outcomeChannel_projection, effect]

end POVM

/-- The measured, recorded, classically corrected and discarded teleportation protocol
is the identity arrow in the deterministic process category. -/
lemma teleportation_causal_composite :
    (teleportationMeasurement.record (ZBasis 4) :
      (⟨Qubit⟩ : CausalQudit) ⟶ ⟨Qubit ⊗ std 4⟩) ≫
      QuantumChannel.controlled (ZBasis 4) (fun i => QuantumChannel.ofIsometry (corrections i)) ≫
      QuantumChannel.partialTraceRight Qubit (std 4) = 𝟙 (⟨Qubit⟩ : CausalQudit) := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change Operator.partialTraceRight
    ((QuantumChannel.controlled (ZBasis 4)
      (fun i => QuantumChannel.ofIsometry (corrections i))).toSuperoperator
        ((teleportationMeasurement.record (ZBasis 4)).toSuperoperator A)) = A
  have h := congrArg (fun Φ : QuantumChannel Qubit (Qubit ⊗ std 4) => Φ.toSuperoperator A)
    teleportationInstrument_record
  change (teleportationInstrument.record (ZBasis 4)).toSuperoperator A =
    (QuantumChannel.controlled (ZBasis 4)
      (fun i => QuantumChannel.ofIsometry (corrections i))).toSuperoperator
        ((teleportationMeasurement.record (ZBasis 4)).toSuperoperator A) at h
  rw [← h, Instrument.record_apply, map_sum]
  simp only [Operator.partialTraceRight_tensor, Operator.trace_outer,
    (ZBasis 4).inner_eq_one, one_smul, teleportationInstrument_branch]
  exact congrArg (fun Φ : Superoperator Qubit Qubit => Φ A) sum_teleportationBranchMap

end

end Qudit
