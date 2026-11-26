/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Category.Postprocessing
public import FQFP.CQM.Qudit.Channel.Composite
public import FQFP.CQM.Qudit.Channel.Process.Dual
public import FQFP.CQM.Qudit.Channel.MeasurePrepare
public import FQFP.CQM.Qudit.Classical
public import FQFP.CQM.Qudit.Measurement.Luders
public import FQFP.CQM.Qudit.Measurement.Process
public import FQFP.CQM.Qudit.Teleportation.Instrument
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Classical structures inside the quantum process category

Copying in an orthonormal basis and discarding one copy is the unread projective
measurement. Its idempotent CP map represents the diagonal classical sector. Recorded
instrument outputs are fixed by this map on the register. This realizes classical
interfaces inside full matrix algebras; it does not identify arbitrary quantum maps
with maps of classical algebras, or construct the general `CP[C]` category.

## Main definitions and results

* `Qudit.QuantumChannel.dephase`: dephasing in a chosen orthonormal basis.
* `Qudit.QuantumChannel.dephase_idempotent`: dephasing twice is dephasing once.
* `Qudit.QuantumChannel.broadcasts_basisCopy_iff_isDiag`: basis copying broadcasts exactly
  the density matrices diagonal in that basis (§§7.3.2 and 7.5).
* `Qudit.POVM.outcomeChannel`: the classical register of measurement outcomes.
* `Qudit.teleportation_causal_composite`: corrected teleportation in causal CP semantics.
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

open SemiCartesianMonoidalCategory

/-- Coherent basis copying remains coassociative as a deterministic channel. -/
lemma ofIsometry_basisCopy_coassoc (b : OrthonormalBasis ι ℂ H.state) :
    let d := (ofIsometry (basisCopy b)).asHom
    d ≫ ((⟨H⟩ : CausalQudit) ◁ d) = d ≫ (d ▷ (⟨H⟩ : CausalQudit)) ≫ (α_ _ _ _).hom := by
  apply CausalQudit.inclusion.map_injective
  have h := congrArg CPQudit.pure.map (basisComonObj b).comul_assoc
  simp only [← id_tensorHom, ← tensorHom_id, CPQudit.pure.map_comp, CPQudit.pure_tensor,
    CPQudit.pure.map_id] at h
  exact h

/-- Exchanging the two output registers preserves coherent basis copying. -/
lemma ofIsometry_basisCopy_swap (b : OrthonormalBasis ι ℂ H.state) :
    (ofIsometry (basisCopy b)).asHom ≫ (β_ (⟨H⟩ : CausalQudit) ⟨H⟩).hom =
      (ofIsometry (basisCopy b)).asHom := by
  apply CausalQudit.inclusion.map_injective
  exact (CPQudit.pure.map_comp ..).symm.trans (congrArg CPQudit.pure.map (basisCopy_comm b))

/-- Dephasing in a chosen classical structure: copy and discard the second output. -/
def dephase (b : OrthonormalBasis ι ℂ H.state) : QuantumChannel H H :=
  (partialTraceRight H H).comp (ofIsometry (basisCopy b))

/-- The first marginal of coherent copying is the unread basis measurement. -/
lemma ofIsometry_basisCopy_comp_fst (b : OrthonormalBasis ι ℂ H.state) :
    (ofIsometry (basisCopy b)).asHom ≫ fst _ _ = (dephase b).asHom := by
  rw [CausalQudit.fst_eq_partialTraceRight]
  rfl

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
  exact Superoperator.conjugate_ket_comp_bra_apply (b i) (b i) A

/-- Dephasing retains diagonal coefficients and erases off-diagonal coherence. -/
lemma dephase_apply (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (dephase b).toSuperoperator A =
      ∑ i, inner ℂ (b i) (A (b i)) • Operator.outer (b i) (b i) := by
  rw [dephase_eq_luders]
  change (∑ i, (POVM.ofBasis b).luders.branch i) A = _
  simp only [LinearMap.sum_apply, POVM.luders_ofBasis_branch]

/-- Dephasing keeps the diagonal matrix units of its basis and kills the others. -/
lemma dephase_basis_outer [DecidableEq ι] (b : OrthonormalBasis ι ℂ H.state) (i j : ι) :
    (dephase b).toSuperoperator (Operator.outer (b i) (b j)) =
      if i = j then Operator.outer (b i) (b j) else 0 := by
  rw [dephase_eq_luders, ← POVM.ofOrthogonalResolution_basisResolution]
  apply POVM.luders_toChannel_outer <;> simp [POVM.hom_basisResolution_proj]

/-- A classical basis projection is fixed by dephasing. -/
lemma dephase_outer (b : OrthonormalBasis ι ℂ H.state) (j : ι) :
    (dephase b).toSuperoperator (Operator.outer (b j) (b j)) = Operator.outer (b j) (b j) := by
  classical
  exact (dephase_basis_outer b j j).trans (ite_eq_left rfl)

/-- Dephasing is idempotent on all operators, not only density states. -/
lemma dephase_idempotent (b : OrthonormalBasis ι ℂ H.state) :
    (dephase b).comp (dephase b) = dephase b := by
  simpa only [ofIsometry_basisCopy_comp_fst] using!
    comp_fst_idempotent_of_coassoc _ (ofIsometry_basisCopy_coassoc b)

/-- Basis copying broadcasts a channel's outputs exactly when dephasing fixes them. -/
lemma broadcasts_basisCopy_iff {K : Qudit} (b : OrthonormalBasis ι ℂ H.state)
    (Φ : QuantumChannel K H) :
    CQM.Broadcasts (ofIsometry (basisCopy b)).asHom Φ.asHom ↔ (dephase b).comp Φ = Φ := by
  rw [CQM.broadcasts_iff_of_swap _ (ofIsometry_basisCopy_swap b), ofIsometry_basisCopy_comp_fst]
  rfl

/-- In the chosen coordinates, dephasing keeps exactly the diagonal of the input matrix. -/
lemma toMatrix_map_dephase [DecidableEq ι] (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H) :
    ((dephase b).map ρ).toMatrix b = Matrix.diagonal (ρ.toMatrix b).diag := by
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.diag_apply, Density.toMatrix,
    LinearMap.toMatrixOrthonormal_apply_apply, op_map, dephase_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Operator.outer_apply]
  by_cases h : i = j <;> simp [h, b.inner_eq_ite, inner_smul_right]

/-- A density preparation is broadcast by this copier exactly when its matrix is diagonal. -/
theorem broadcasts_basisCopy_iff_isDiag [DecidableEq ι] (b : OrthonormalBasis ι ℂ H.state)
    (ρ : Density H) :
    CQM.Broadcasts (ofIsometry (basisCopy b)).asHom ρ.toState ↔ (ρ.toMatrix b).IsDiag := by
  rw [CQM.broadcasts_iff_of_swap _ (ofIsometry_basisCopy_swap b), ofIsometry_basisCopy_comp_fst,
    Density.toState_comp, Density.toState_injective.eq_iff, Matrix.isDiag_iff_diagonal_diag,
    ← toMatrix_map_dephase]
  exact ⟨fun h => congrArg (Density.toMatrix · b) h,
    fun h => Density.ext ((LinearMap.toMatrixOrthonormal b).injective h)⟩

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

/-- Coherent copying in the register basis broadcasts the outcome of any POVM. -/
lemma broadcasts_outcomeChannel (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) :
    CQM.Broadcasts (QuantumChannel.ofIsometry (basisCopy b)).asHom (M.outcomeChannel b).asHom := by
  apply (QuantumChannel.broadcasts_basisCopy_iff b _).mpr
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change (QuantumChannel.dephase b).toSuperoperator ((M.outcomeChannel b).toSuperoperator A) = _
  simp only [outcomeChannel_apply, map_sum, map_smul, QuantumChannel.dephase_outer]

/-- Encoding a POVM outcome in a basis is measurement followed by pure-state preparation. -/
lemma measurePrepare_basis (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) :
    M.measurePrepare (fun i => Density.pure (UnitState.ofBasis b i)) = M.outcomeChannel b := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  simp only [measurePrepare_apply, outcomeChannel_apply, Density.op_pure, UnitState.ofBasis]

/-- Reading a classical outcome after the measurement channel recovers the original effect. -/
lemma outcomeChannel_comp_effect (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) (i : ι) :
    (M.outcomeChannel b).toCPMap ≫ (ofBasis b).effect i = M.effect i := by
  classical
  rw [← measurePrepare_basis]
  change (M.measurePrepare _).asCPHom ≫ _ = _
  rw [asCPHom_measurePrepare]
  exact CQM.measurePrepare_comp_readout _ _ i _ (fun j => toCPState_ofBasis_comp_effect b j i)

/-- In the Heisenberg picture a classical outcome projection pulls back to its POVM
effect. This is the classical-to-quantum bridge, with the direction explicit. -/
lemma dual_outcomeChannel_projection (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state)
    (i : ι) :
    (M.outcomeChannel b).toCPMap.dual.toSuperoperator
        (Operator.outer (b i) (b i)) = M.op i := by
  have h := M.outcomeChannel_comp_effect b i
  rw [effect, CPQudit.comp_effectOfPositive] at h
  exact CPQudit.eq_of_effectOfPositive_eq h

/-- Reading the basis of the outcome register pulls back to the entire original measurement. -/
lemma pullback_ofBasis_outcomeChannel (M : POVM H ι) (b : OrthonormalBasis ι ℂ C.state) :
    (ofBasis b).pullback (M.outcomeChannel b) = M :=
  ext_effect fun i => (effect_pullback ..).trans (M.outcomeChannel_comp_effect b i)

/-- Reading the registered label and preparing its state realizes the measure-and-prepare map. -/
lemma measurePrepare_comp_outcomeChannel {K : Qudit} (M : POVM H ι)
    (b : OrthonormalBasis ι ℂ C.state) (σ : ι → Density K) :
    ((ofBasis b).measurePrepare σ).comp (M.outcomeChannel b) = M.measurePrepare σ := by
  rw [measurePrepare_comp, pullback_ofBasis_outcomeChannel]

/-- The postprocessings of a fixed measurement register are exactly the channels that use
that POVM and prepare an arbitrary density state for each outcome. -/
theorem isDegradableTo_iff_exists_measurePrepare {K : Qudit} (M : POVM H ι)
    (b : OrthonormalBasis ι ℂ C.state) (Φ : QuantumChannel H K) :
    CQM.IsDegradableTo (M.outcomeChannel b).asHom Φ.asHom ↔
      ∃ σ : ι → Density K, Φ = M.measurePrepare σ := by
  constructor
  · rintro ⟨D, hD⟩
    change D.comp (M.outcomeChannel b) = Φ at hD
    exact ⟨_, hD.symm.trans ((congrArg D.comp (M.measurePrepare_basis b).symm).trans
      (M.comp_measurePrepare _ D))⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨((ofBasis b).measurePrepare σ).asHom, M.measurePrepare_comp_outcomeChannel b σ⟩

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
