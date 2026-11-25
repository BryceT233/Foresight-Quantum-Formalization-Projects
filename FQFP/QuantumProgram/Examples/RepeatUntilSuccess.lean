/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the one-shot block and the repeat-until-success triple.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Gate/RUSBlock.lean
Qhl/Examples/RUSTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Iteration.AlmostSure
public import FQFP.QuantumProgram.ControlledPhase
public import FQFP.CQM.Qudit.Teleportation.Basic
import FQFP.CQM.Qudit.Channel.Process.Dual

/-!
# Repeat until a single-qubit gate succeeds

The first qubit is a resettable ancilla. A Hadamard, a coherent controlled gate and a bit flip
place the transformed data in the zero branch and the original data in the one branch.
The two classical bits store the success flag and the most recent ancilla measurement, as in
`Qhl/Examples/RUSTriple.lean`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct ENNReal NNReal

namespace QuantumProgram.RepeatUntilSuccess

noncomputable section

/-- The ancilla followed by the data qubit. -/
abbrev Memory := Qubit ⊗ Qubit

/-- The success flag and the last measurement outcome. -/
abbrev Store := Bool × Bool

/-- The computational basis ket of the ancilla. -/
abbrev ket (i : Fin 2) := ZBasis 2 i

/-- Project onto an ancilla outcome. -/
def proj (i : Fin 2) : Operator Qubit := Operator.outer (ket i) (ket i)

private theorem proj_basis (i j : Fin 2) :
    proj i (ket j) = if i = j then ket i else 0 := by
  simp [proj, Operator.outer_apply, ket, OrthonormalBasis.inner_eq_ite, ite_smul]

private theorem proj_adjoint (i : Fin 2) : (proj i).adjoint = proj i := Operator.adjoint_outer ..

/-- Coherently apply an operator on the one sector of the ancilla. -/
def controlOp (T : Operator Qubit) : Operator Memory :=
  Qubit.controlledOp T

private theorem controlOp_basis (T : Operator Qubit) (i : Fin 2) (x : Qubit.state) :
    controlOp T (ket i ⊗ₜ[ℂ] x) = ket i ⊗ₜ[ℂ] (if i = 0 then x else T x) :=
  Qubit.controlledOp_basis T i x

/-- The coherent controlled unitary acts as the identity on zero and as the target gate on one. -/
def controlledGate (V : Qubit ⟶ Qubit) : Memory ⟶ Memory := Qubit.controlled V

instance (V : Qubit ⟶ Qubit) [IsUnitary V] : IsUnitary (controlledGate V) := by
  unfold controlledGate
  infer_instance

/-- The RUS block in execution order: Hadamard, controlled target, then ancilla bit flip. -/
def block (V : Qubit ⟶ Qubit) [IsUnitary V] : UnitaryProgram Memory :=
  .seq (.gate (.left .whole) Qubit.H)
    (.seq (.gateHom .whole (controlledGate V)) (.gate (.left .whole) Qubit.pauliX))

/-- Inserting an ancilla basis state leaves the data untouched. -/
def insert (i : Fin 2) : Qubit ⟶ Memory :=
  ofLinearIsometry (H := Qubit) (K := Memory)
    ⟨TensorProduct.mk ℂ Qubit.state Qubit.state (ket i), fun x => by
      change ‖ket i ⊗ₜ[ℂ] x‖ = ‖x‖
      simp [ket, TensorProduct.norm_tmul]⟩

instance (i : Fin 2) : IsIsometry (insert i) := by unfold insert; infer_instance

/-- Erase the ancilla by partial trace and reinsert the zero ket. -/
def reset : QuantumChannel Memory Memory :=
  (QuantumChannel.ofIsometry (insert 0)).comp (QuantumChannel.partialTraceLeft Qubit Qubit)

/-- The two possible ancilla projectors tensored with the data identity. -/
def selectAncilla (i : Fin 2) : Operator Memory := Operator.tensor (proj i) 1

/-- The ancilla projector selects exactly its basis sector. -/
theorem select_basis (i j : Fin 2) (x : Qubit.state) :
    selectAncilla i (ket j ⊗ₜ[ℂ] x) = if i = j then ket j ⊗ₜ[ℂ] x else 0 := by
  by_cases h : i = j <;> simp [selectAncilla, proj_basis, h]

/-- Computational-basis measurement retaining both qubits and the unnormalized branch weights. -/
def measurement : Instrument Memory Memory (Fin 2) :=
  Instrument.ofOperators selectAncilla (by
    have adj (i : Fin 2) : (selectAncilla i).adjoint = selectAncilla i := by
      unfold selectAncilla Operator.tensor
      rw [TensorProduct.adjoint_map, proj_adjoint, LinearMap.adjoint_one]
    rw [Fin.sum_univ_two, adj, adj]
    apply ((ZBasis 2).tensorProduct (ZBasis 2)).toBasis.ext
    rintro ⟨i, j⟩
    simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
    change selectAncilla 0 (selectAncilla 0 (ket i ⊗ₜ[ℂ] ket j)) +
      selectAncilla 1 (selectAncilla 1 (ket i ⊗ₜ[ℂ] ket j)) = ket i ⊗ₜ[ℂ] ket j
    fin_cases i <;> simp [select_basis])

private theorem block_insert (V : Qubit ⟶ Qubit) [IsUnitary V] (x : Qubit.state) :
    (block V).denoteHom.hom ((insert 0).hom x) =
      bellFactor • (ket 0 ⊗ₜ[ℂ] V.hom x + ket 1 ⊗ₜ[ℂ] x) := by
  have hh : Qubit.H.asHom (ket 0) = bellFactor • (ket 0 + ket 1) := by
    rw [Qubit.H, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
    simp [bellFactor, smul_add]
  have hx (i : Fin 2) : Qubit.pauliX.asHom (ket i) = ket (1 - i) := by
    rw [Qubit.pauliX, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
    fin_cases i <;> simp [ket]
  change (Qubit.pauliX.asHom ▷ Qubit).hom (controlOp V.hom (Qubit.H.asHom (ket 0) ⊗ₜ[ℂ] x)) = _
  rw [hh, ← TensorProduct.smul_tmul', TensorProduct.add_tmul, map_smul, map_add, map_smul, map_add,
    controlOp_basis, controlOp_basis]
  simp [whiskerRight_apply, hx, add_comm]

/-- After the reset, each measured branch acts on the reduced data by this isometry. -/
def outputMap (V : Qubit ⟶ Qubit) (i : Fin 2) : Qubit ⟶ Memory :=
  if i = 0 then V ≫ insert 0 else insert 1

instance (V : Qubit ⟶ Qubit) [IsUnitary V] (i : Fin 2) : IsIsometry (outputMap V i) := by
  unfold outputMap
  split <;> infer_instance

/-- A scalar multiple of an outcome isometry contributes its squared modulus after reset. -/
theorem branch_after_reset_of_select (U : UnitaryProgram Memory) (i : Fin 2)
    (f : Qubit ⟶ Memory) (c : ℂ)
    (h : selectAncilla i ∘ₗ U.denoteHom.hom ∘ₗ (insert 0).hom = c • f.hom)
    (A : Operator Memory) :
    measurement.branch i (U.toChannel.toSuperoperator (reset.toSuperoperator A)) =
      (‖c‖ ^ 2 : ℂ) • Superoperator.conjugate f.hom (Operator.partialTraceLeft A) := by
  let ρ := Operator.partialTraceLeft A
  change Superoperator.conjugate (selectAncilla i)
    (Superoperator.conjugate U.denoteHom.hom (Superoperator.conjugate (insert 0).hom ρ)) = _
  change (Superoperator.conjugate (selectAncilla i) ∘ₗ
    (Superoperator.conjugate U.denoteHom.hom ∘ₗ
      Superoperator.conjugate (insert 0).hom)) ρ = _
  rw [← Superoperator.conjugate_comp, ← Superoperator.conjugate_comp, h]
  simp only [Superoperator.conjugate_apply, map_smulₛₗ,
    LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, Complex.conj_mul', ρ]

/-- The unnormalized post-measurement operator is half the reduced input, embedded with the
outcome label. Only outcome zero applies the target gate. -/
theorem branch_after_reset (V : Qubit ⟶ Qubit) [IsUnitary V] (A : Operator Memory) (i : Fin 2) :
    measurement.branch i ((block V).toChannel.toSuperoperator (reset.toSuperoperator A)) =
      (1 / 2 : ℂ) • Superoperator.conjugate (outputMap V i).hom (Operator.partialTraceLeft A) := by
  have branchMap : selectAncilla i ∘ₗ (block V).denoteHom.hom ∘ₗ (insert 0).hom =
      bellFactor • (outputMap V i).hom := by
    ext x : 1
    simp only [LinearMap.comp_apply, block_insert, map_smul, map_add, select_basis]
    fin_cases i <;> simp [outputMap] <;> rfl
  rw [branch_after_reset_of_select _ _ _ _ branchMap]
  congr 1
  rw [← Complex.mul_conj', conj_bellFactor, bellFactor_mul_self]

/-- The guard holds until the success flag is set. -/
def guard (σ : Store) : Bool := !σ.1

/-- Write the ancilla outcome while preserving the success bit. -/
def record (i : Fin 2) (σ : Store) : Store := (σ.1, decide (i = 1))

/-- Exit precisely when the last measurement returned zero. -/
def setSuccess (σ : Store) : Store := (!σ.2, σ.2)

/-- Reset the ancilla, execute the block, measure the ancilla and update the flag. -/
def body (V : Qubit ⟶ Qubit) [IsUnitary V] : Command Store (Fin 2) Memory :=
  .seq (.channel fun _ => reset)
    (.seq (.unitary (fun _ => id) (fun _ _ => block V))
      (.seq (.measure (fun _ (_ : Fin 1) => 0) (fun _ _ => measurement) record)
        (.assign setSuccess)))

/-- Clear the success flag before entering the probabilistic loop. -/
def program (V : Qubit ⟶ Qubit) [IsUnitary V] : Command Store (Fin 2) Memory :=
  .seq (.assign fun σ => (false, σ.2)) (.whileDo guard (body V))

/-- The precondition observes the data projector and accepts any ancilla state. -/
def pre (ψ : UnitState Qubit) : Assertion Store Memory := fun _ =>
  let E := ((Assertion.pure ψ : Assertion Unit Qubit) ())
  ⟨Operator.oneTensorHom Qubit Qubit E.val, LinearMap.nonneg_iff_isPositive.mpr
    (Operator.isPositive_tensor LinearMap.isPositive_one (Density.pure ψ).positive), by
    change Operator.oneTensorHom Qubit Qubit E.val ≤ 1
    rw [← map_one (Operator.oneTensorHom Qubit Qubit), ← sub_nonneg, ← map_sub]
    exact LinearMap.nonneg_iff_isPositive.mpr
      (Operator.isPositive_tensor LinearMap.isPositive_one (LinearMap.le_def.mp E.2.2))⟩

/-- Success requires the flag and the pure state with ancilla zero and data transformed by `V`. -/
def post (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) : Assertion Store Memory :=
  (Assertion.pure ((UnitState.ofBasis (ZBasis 2) 0).tensor (ψ.map V))).mask fun σ => σ.1 = true

/-- While retrying only the data is constrained. On success the ancilla is also fixed. -/
def invariant (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) : Assertion Store Memory :=
  Assertion.guard Prod.fst (post V ψ) (pre ψ)

/-- Pull a postcondition back through write-back, measurement, the unitary block and reset. -/
def bodyPre (V : Qubit ⟶ Qubit) [IsUnitary V] (A : Assertion Store Memory) :
    Assertion Store Memory :=
  let M := Assertion.measurePre (A ∘ setSuccess) (fun _ (_ : Fin 1) => (0 : Fin 2))
    (fun _ _ => measurement) record
  (M.unitaryPre (fun _ => id (α := Fin 2)) (fun _ _ => block V)).channelPre fun _ => reset

/-- The four primitive total-correctness rules compose at their backward preconditions. -/
theorem derivTot_bodyPre (V : Qubit ⟶ Qubit) [IsUnitary V] (A : Assertion Store Memory) :
    DerivTot (bodyPre V A) (body V) A :=
  .seq (.channel _ _) (.seq (.unitary _ _ _) (.seq (.measure _ _ _ _) (.assign _ A)))

/-- The dual of reset, a heralded circuit and ancilla readout acts on the reduced data.
Each branch effect is pulled back along its outcome map and weighted by its probability. -/
theorem reset_measure_effect (U : UnitaryProgram Memory) (f : Fin 2 → (Qubit ⟶ Memory))
    (p : Fin 2 → ℂ) (h : ∀ i ρ, measurement.branch i
      (U.toChannel.toSuperoperator (reset.toSuperoperator ρ)) =
        p i • Superoperator.conjugate (f i).hom (Operator.partialTraceLeft ρ))
    (E : Fin 2 → Set.Icc (0 : Operator Memory) 1) :
    (channelEffect reset (channelEffect U.toChannel (instrumentEffect measurement E)) :
      Operator Memory) = Operator.oneTensorHom Qubit Qubit
        (∑ i, p i • Superoperator.conjugate (f i).hom.adjoint (E i)) := by
  apply Operator.ext_trace
  intro ρ
  simp only [channelEffect, QuantumChannel.pullbackEffect, instrumentEffect, CPMap.trace_dual]
  change ((∑ i, (measurement.branchCPMap i).dual.toSuperoperator (E i)) *
    U.toChannel.toSuperoperator (reset.toSuperoperator ρ)).trace =
      LinearMap.trace ℂ Memory.state (TensorProduct.map LinearMap.id _ * ρ)
  apply Eq.trans _ (LinearMap.trace_mul_partialTraceLeft ρ _)
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Operator.trace, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine ((measurement.branchCPMap i).trace_dual _ _).trans ?_
  change ((E i : Operator Memory) * measurement.branch i
    (U.toChannel.toSuperoperator (reset.toSuperoperator ρ))).trace = _
  rw [h, mul_smul_comm, Operator.trace, map_smul]
  exact congrArg (p i * ·) (Superoperator.trace_conjugate_adjoint _ _ _).symm

/-- Reset discards the input ancilla. On the reduced data, the precondition is the average
of the two final effects pulled back along their outcome isometries. -/
theorem bodyPre_op (V : Qubit ⟶ Qubit) [IsUnitary V] (A : Assertion Store Memory) (σ : Store) :
    (bodyPre V A σ : Operator Memory) = Operator.oneTensorHom Qubit Qubit
      ((2⁻¹ : ℂ) • ∑ i, Superoperator.conjugate (outputMap V i).hom.adjoint
        (A (setSuccess (record i σ)))) := by
  have hr : Function.Injective (fun _ : Fin 1 => (0 : Fin 2)) :=
    Function.injective_of_subsingleton _
  simp only [bodyPre, Assertion.channelPre, Assertion.unitaryPre, Assertion.measurePre,
    Function.injective_id, hr, dite_true, Function.comp_apply]
  rw [reset_measure_effect (block V) (outputMap V) (fun _ => (1 / 2 : ℂ))
    (fun i ρ => branch_after_reset V ρ i), Finset.smul_sum, one_div]

private theorem expectation_pre (s : CQState Store Memory) (ψ : UnitState Qubit) :
    s.expectation (pre ψ s.store) =
      (s.map (QuantumChannel.partialTraceLeft Qubit Qubit)).expectation (Density.pure ψ).op :=
  congrArg Complex.re (LinearMap.trace_mul_partialTraceLeft s.op (Density.pure ψ).op).symm

/-- The successful output isometry pulls the desired projector back to the input projector. -/
theorem pull_success (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    Superoperator.conjugate (outputMap V 0).hom.adjoint (post V ψ (true, false)) =
      (Density.pure ψ).op := by
  rw [post, Assertion.mask_of_pos _ (by rfl)]
  let f := outputMap V 0
  change Superoperator.conjugate f.hom.adjoint (Operator.outer (f.hom ψ) (f.hom ψ)) = _
  rw [Superoperator.conjugate_outer, hom_adjoint_apply_of_isIsometry]
  rfl

/-- In the retry sector the data effect pulls back to the original data projector. -/
theorem pull_retry (V : Qubit ⟶ Qubit) (ψ : UnitState Qubit) :
    Superoperator.conjugate (outputMap V 1).hom.adjoint (pre ψ (false, true)) =
      (Density.pure ψ).op := by
  let f := insert 1
  let E := (Density.pure ψ).op
  ext x : 1
  change f.hom.adjoint (Operator.tensor 1 E (f.hom.adjoint.adjoint x)) = E x
  rw [LinearMap.adjoint_adjoint]
  exact hom_adjoint_apply_of_isIsometry f (E x)

private theorem half_smul_add_self (E : Operator Qubit) : (2⁻¹ : ℂ) • (E + E) = E := by
  rw [← two_smul ℂ E, smul_smul]
  norm_num

private theorem guarded_eq_pre {σ : Store} (hb : guard σ = true)
    (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    invariant V ψ σ = pre ψ σ := by
  have hσ : σ.1 = false := by simpa [guard] using hb
  simp [invariant, Assertion.guard, hσ]

/-- Pulling the invariant back through the body recovers the original data effect at every store. -/
theorem bodyPre_invariant (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    bodyPre V (invariant V ψ) = pre ψ := by
  funext σ
  apply Subtype.ext
  rw [bodyPre_op, Fin.sum_univ_two]
  change Operator.oneTensorHom Qubit Qubit ((2⁻¹ : ℂ) •
    (Superoperator.conjugate (outputMap V 0).hom.adjoint (post V ψ (true, false)) +
     Superoperator.conjugate (outputMap V 1).hom.adjoint (pre ψ (false, true)))) = _
  rw [pull_success, pull_retry, half_smul_add_self]
  rfl

/-- The guarded invariant is a derivable precondition for one execution of the loop body. -/
theorem bodyDeriv (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    DerivTot ((invariant V ψ).mand guard) (body V) (invariant V ψ) := by
  refine .conseq ?_ (derivTot_bodyPre V (invariant V ψ)) le_rfl
  rw [bodyPre_invariant]
  intro σ
  cases hb : guard σ with
  | true => rw [Assertion.mand_of_true _ hb, guarded_eq_pre hb]
  | false =>
    change ((invariant V ψ).mand guard σ : Operator Memory) ≤ _
    rw [Assertion.mand_of_false _ hb]
    exact (pre ψ σ).2.1

/-- Semantic invariant preservation follows from the total derivation for the body. -/
theorem validTot_body (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    validTot ((invariant V ψ).mand guard) (body V) (invariant V ψ) :=
  (bodyDeriv V ψ).sound

/-- The backward precondition for the complement of the invariant that returns to the guard. -/
def complPre (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) : Assertion Store Memory :=
  bodyPre V ((invariant V ψ).mand guard).compl

/-- The complementary triple is derived by the same four primitive rules. -/
theorem complDeriv (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    DerivTot (complPre V ψ) (body V) ((invariant V ψ).mand guard).compl :=
  derivTot_bodyPre V _

/-- The complement precondition excludes exactly half the original data effect. -/
theorem complPre_op (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) (σ : Store) :
    (complPre V ψ σ : Operator Memory) = 1 - (2⁻¹ : ℂ) • (pre ψ σ : Operator Memory) := by
  let J := invariant V ψ
  have unital (i : Fin 2) :
      Superoperator.conjugate (outputMap V i).hom.adjoint 1 = (1 : Operator Qubit) := by
    rw [Superoperator.conjugate_apply, LinearMap.adjoint_adjoint, Module.End.one_eq_id,
      LinearMap.id_comp, hom_adjoint_comp_of_isIsometry]
    rfl
  rw [complPre, bodyPre_op, Fin.sum_univ_two]
  change Operator.oneTensorHom Qubit Qubit ((2⁻¹ : ℂ) •
    (Superoperator.conjugate (outputMap V 0).hom.adjoint (1 - (J.mand guard (true, false)).val) +
     Superoperator.conjugate (outputMap V 1).hom.adjoint
       (1 - (J.mand guard (false, true)).val))) = _
  rw [J.mand_of_false (b := guard) (σ := (true, false)) rfl, sub_zero,
    J.mand_of_true (b := guard) (σ := (false, true)) rfl, map_sub, unital, unital]
  change Operator.oneTensorHom Qubit Qubit ((2⁻¹ : ℂ) • (1 + (1 -
    Superoperator.conjugate (outputMap V 1).hom.adjoint (pre ψ (false, true))))) = _
  rw [pull_retry, ← add_sub_assoc, smul_sub, half_smul_add_self, map_sub, map_one, map_smul]
  rfl

/-- On guarded inputs the complement expectation is the input mass minus half the invariant. -/
theorem expectation_complPre (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit)
    (s : CQState Store Memory) (hb : guard s.store = true) :
    s.expectation (complPre V ψ s.store) =
      s.mass - (2⁻¹ : ℝ) * s.expectation (invariant V ψ s.store) := by
  rw [complPre_op, guarded_eq_pre hb, ← s.expectation_one]
  simp [CQState.expectation, sub_mul, Operator.trace, Complex.mul_re]

/-- The complementary total triple bounds the fraction returning to the guard by one half. -/
theorem contraction (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    LoopBodyContraction guard (body V) (invariant V ψ) (2⁻¹ : ℝ≥0) := by
  apply LoopBodyContraction.of_complement (complDeriv V ψ).sound
  intro s hb
  have hn := s.expectation_nonneg ((invariant V ψ).isPositive s.store)
  rw [expectation_complPre V ψ s hb, ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) hn),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_coe_nnreal (p := (2⁻¹ : ℝ≥0))]
  norm_num

/-- The geometric loop rule establishes total correctness for the arbitrary initial flag. -/
theorem validTot_loop (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    validTot (invariant V ψ) (.whileDo guard (body V)) (post V ψ) := by
  have exit_eq : (invariant V ψ).mandNot guard = post V ψ := by
    funext σ
    obtain ⟨flag, m⟩ := σ
    cases flag <;> simp [invariant, Assertion.guard, guard, post, Assertion.mandNot, Assertion.mask]
  rw [← exit_eq]
  exact (bodyDeriv V ψ).validTot_while_of_contraction (by norm_num) (contraction V ψ)

/-- Total correctness of the initialized repeat-until-success program, for every single-qubit
unitary and unit data ket, evaluated on all positive two-qubit input operators. -/
theorem validTot_program (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    validTot (pre ψ) (program V) (post V ψ) :=
  validTot_seq (validTot_assign (fun σ : Store => (false, σ.2)) (invariant V ψ)) (validTot_loop V ψ)

/-- Any normalized ancilla paired with the specified pure data satisfies the precondition
with expectation one, at either initial value of the success flag. -/
theorem expectation_pre_tensor (σ : Store) (ρ : Density Qubit) (ψ : UnitState Qubit) :
    let input := ρ.tensor (Density.pure ψ)
    (CQState.mk σ input.op input.positive).expectation (pre ψ σ) = 1 := by
  dsimp only
  rw [expectation_pre]
  change ((Density.pure ψ).op * (ρ.tensor (Density.pure ψ)).partialTraceLeft.op).trace.re = 1
  rw [Density.partialTraceLeft_tensor, Density.pure_mul_self, Density.trace_one, Complex.one_re]

end

end QuantumProgram.RepeatUntilSuccess
