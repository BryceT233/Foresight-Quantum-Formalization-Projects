/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the phase ladder and the output of a Fourier stage.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/Fourier.lean
Qhl/Examples/QFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.ControlledPhase
public import FQFP.QuantumProgram.Logic.ForUnitary

/-!
# The controlled-phase ladder of a Fourier stage

Wire zero carries an equatorial state and the following wires carry computational basis bits.
Each two-wire gate contributes its angle to the first wire precisely when its target is one.
The list program can execute any ordered sublist, including an empty or repeated list.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram.FourierLadder

noncomputable section

variable {Store : Type*} {n : ℕ}

/-- The first wire carries the accumulated phase and the tail carries the basis word. -/
def state (x : Fin n → Fin 2) (φ : ℝ) : UnitState (tensorMemory (fun _ : Fin (n + 1) => Qubit)) :=
  (Qubit.phaseState φ).tensor (registerProductState (fun _ => Qubit)
    (fun j => UnitState.ofBasis (ZBasis 2) (x j)))

/-- The controlled phase with its first operand at the head of the register. -/
def headPhaseGate (j : Fin n) (θ : ℝ) :
    UnitaryProgram (tensorMemory (fun _ : Fin (n + 1) => Qubit)) :=
  let V := (Register.site (fun _ : Fin n => Qubit) j).liftEnd (Qubit.phaseShift θ)
  (UnitaryProgram.gateHom .whole (Qubit.controlled V.asHom) :
    UnitaryProgram (Qubit ⊗ tensorMemory (fun _ : Fin n => Qubit)))

/-- Controlled phase on a pair of register sites, with identity on coincident sites. -/
def phaseGate : {m : ℕ} → Fin m → Fin m → ℝ →
    UnitaryProgram (tensorMemory (fun _ : Fin m => Qubit))
  | 0, i, _, _ => i.elim0
  | m + 1, i, j, θ => Fin.cases
      (Fin.cases (.gate .whole 1) (fun b => headPhaseGate b θ) j)
      (fun a => Fin.cases (headPhaseGate a θ)
        (fun b => .gate (.right (.whole (H := tensorMemory (fun _ : Fin m => Qubit))))
          (phaseGate (m := m) a b θ).denoteEnd) j) i

private theorem headPhaseGate_neg {m : ℕ} (j : Fin m) (θ : ℝ) :
    (headPhaseGate j (-θ)).denoteEnd = star (headPhaseGate j θ).denoteEnd := by
  let r := Register.site (fun _ : Fin m => Qubit) j
  apply End.ext
  change Qubit.controlled (r.liftEnd (Qubit.phaseShift (-θ))).asHom =
    (Qubit.controlled (r.liftEnd (Qubit.phaseShift θ)).asHom)†
  rw [← Qubit.star_phaseShift, Register.liftEnd_star, End.star_asHom, Qubit.controlled_dagger]

/-- A negative-angle rung is the adjoint of the positive-angle rung on the same sites. -/
theorem denoteEnd_phaseGate_neg (i j : Fin n) (θ : ℝ) :
    (phaseGate i j (-θ)).denoteEnd = star (phaseGate i j θ).denoteEnd := by
  induction n with
  | zero => exact i.elim0
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (star_one (End _)).symm
      | succ j => exact headPhaseGate_neg j θ
    | succ i =>
      cases j using Fin.cases with
      | zero => exact headPhaseGate_neg i θ
      | succ j =>
        let r : Register (Qubit ⊗ tensorMemory (fun _ : Fin m => Qubit)) _ :=
          .right (.whole (H := tensorMemory (fun _ : Fin m => Qubit)))
        change r.liftEnd (phaseGate i j (-θ)).denoteEnd =
          star (r.liftEnd (phaseGate i j θ).denoteEnd)
        rw [ih, Register.liftEnd_star]

/-- The underlying morphism of a negative-angle rung is the dagger of the forward rung. -/
theorem phaseGate_neg (i j : Fin n) (θ : ℝ) :
    (phaseGate i j (-θ)).denoteHom = (phaseGate i j θ).denoteHom† :=
  congrArg End.asHom (denoteEnd_phaseGate_neg i j θ)

/-- A rung adds the phase selected by its basis target and fixes every spectator factor. -/
theorem phaseGate_productState (i j : Fin n) (hij : i < j) (θ φ : ℝ) (b : Fin 2)
    (v : Fin n → UnitState Qubit) (hi : v i = Qubit.phaseState φ)
    (hj : v j = UnitState.ofBasis (ZBasis 2) b) :
    (phaseGate i j θ).toOperator (registerProductState (fun _ => Qubit) v).val =
      (registerProductState (fun _ => Qubit) (Function.update v i
        (Qubit.phaseState (φ + if b = 0 then 0 else θ)))).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact (Fin.not_lt_zero i hij).elim
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        let V := (Register.site (fun _ : Fin n => Qubit) j).liftEnd (Qubit.phaseShift θ)
        let w := registerProductState (fun _ : Fin n => Qubit) (Fin.tail v)
        let δ : ℝ := if b = 0 then 0 else θ
        have hw : V.asHom w.val = Complex.exp (δ * Complex.I) • w.val := by
          apply Register.liftEnd_site_productState_eigen
          change (Qubit.phaseShift θ).asHom (v j.succ).val = _ • (v j.succ).val
          rw [hj]
          by_cases h : b = 0 <;> simpa [δ, h] using Qubit.phaseShift_basis θ b
        simp only [registerProductState, Function.update_self, Fin.tail_update_zero]
        change Qubit.controlledOp V.asHom.hom ((v 0).val ⊗ₜ[ℂ] w.val) =
          (Qubit.phaseState (φ + δ)).val ⊗ₜ[ℂ] w.val
        rw [hi, Qubit.controlledOp_tmul_eigen _ hw, Qubit.phaseShift_phaseState]
      | succ i =>
        simp only [registerProductState, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)),
          Fin.tail_update_succ]
        change TensorProduct.map LinearMap.id (phaseGate i j θ).toOperator
          ((v 0).val ⊗ₜ[ℂ] _) = _
        exact congrArg (fun w => (v 0).val ⊗ₜ[ℂ] w)
          (ih i j (Fin.succ_lt_succ_iff.mp hij) (Fin.tail v) hi hj)

/-- A zero control disables the phase gate for any target and spectator factors. -/
theorem phaseGate_productState_of_control_zero (i j : Fin n) (hij : i < j) (θ : ℝ)
    (v : Fin n → UnitState Qubit) (hi : v i = UnitState.ofBasis (ZBasis 2) 0) :
    (phaseGate i j θ).toOperator (registerProductState (fun _ => Qubit) v).val =
      (registerProductState (fun _ => Qubit) v).val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero => exact (Fin.not_lt_zero i hij).elim
    | succ j =>
      cases i using Fin.cases with
      | zero =>
        let V := (Register.site (fun _ : Fin n => Qubit) j).liftEnd (Qubit.phaseShift θ)
        let w := (registerProductState (fun _ => Qubit) (Fin.tail v)).val
        change Qubit.controlledOp V.asHom.hom ((v 0).val ⊗ₜ[ℂ] w) = (v 0).val ⊗ₜ[ℂ] w
        rw [hi, UnitState.coe_ofBasis, Qubit.controlledOp_basis, ite_eq_left rfl]
      | succ i =>
        change TensorProduct.map LinearMap.id (phaseGate i j θ).toOperator
          ((v 0).val ⊗ₜ[ℂ] _) = (v 0).val ⊗ₜ[ℂ] _
        exact congrArg (fun w => (v 0).val ⊗ₜ[ℂ] w)
          (ih i j (Fin.succ_lt_succ_iff.mp hij) (Fin.tail v) hi)

/-- Controlled phase between wire zero and the indicated wire of the tail. -/
def rung (j : Fin n) (θ : ℝ) : Command Store (Fin (n + 1))
    (tensorMemory (fun _ : Fin (n + 1) => Qubit)) :=
  .unitary (fun _ => ![0, j.succ]) (fun _ _ => headPhaseGate j θ)

/-- The one-rung source derivation retains any classical predicate and the entire basis word. -/
theorem sourceDeriv_rung (j : Fin n) (θ φ : ℝ) (x : Fin n → Fin 2) (P : Store → Prop) :
    SourceDerivTot (.ofEffect (Assertion.pure (state x φ)) P) (rung j θ)
      (.ofEffect (Assertion.pure (state x (φ + if x j = 0 then 0 else θ))) P) := by
  refine SourceDerivTot.unitary_pure _ _ (fun _ => state x φ) (fun _ => state x _) ?_ ?_
  · intro σ _ a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Ne.symm (Fin.succ_ne_zero j)]
  · intro σ _
    let v := Fin.cons (α := fun _ : Fin (n + 1) => UnitState Qubit)
      (Qubit.phaseState φ) (fun i => UnitState.ofBasis (ZBasis 2) (x i))
    have h := phaseGate_productState 0 j.succ (Fin.succ_pos j) θ φ (x j) v rfl rfl
    simp only [registerProductState, Function.update_self, Fin.tail_update_zero, v, Fin.tail_cons,
      Fin.cons_zero] at h
    exact h

/-- Executing a list of rungs accumulates the angles selected by its target bits. -/
theorem derivTot_ladder (θ : Fin n → ℝ) (x : Fin n → Fin 2) (l : List (Fin n)) (φ : ℝ) :
    DerivTot (Store := Store) (Assertion.pure (state x φ)) (.forList l fun j => rung j (θ j))
      (Assertion.pure (state x (φ + (l.map fun j => if x j = 0 then 0 else θ j).sum))) := by
  induction l generalizing φ with
  | nil =>
    simp only [List.map_nil, List.sum_nil, add_zero, Command.forList_nil]
    exact .skip _
  | cons j l ih =>
    have h := (sourceDeriv_rung j (θ j) φ x (fun _ : Store => True)).toDerivTot
    simp only [CQAssertion.toAssn_ofEffect_true] at h
    simpa only [List.map_cons, List.sum_cons, ← add_assoc, Command.forList_cons] using
      DerivTot.seq h (ih _)

/-- Total correctness of the full QFT phase ladder with its dyadic gate angles. -/
theorem validTot_fourierLadder (x : Fin n → Fin 2) (φ : ℝ) :
    let θ := fun j : Fin n => 2 * Real.pi / 2 ^ (j.val + 2)
    validTot (Store := Store) (Assertion.pure (state x φ))
      (.forList (List.finRange n) fun j => rung j (θ j))
      (Assertion.pure (state x (φ + ∑ j, if x j = 0 then 0 else θ j))) := by
  intro θ
  simpa only [Fin.sum_univ_def] using (derivTot_ladder (Store := Store) θ x
    (List.finRange n) φ).sound

/-- The Fourier angle of a big-endian binary fraction, including its leading bit. -/
def basisAngle {k : ℕ} (x : Fin k → Fin 2) : ℝ :=
  ∑ i, if x i = 0 then 0 else 2 * Real.pi / 2 ^ (i.val + 1)

/-- Apply Hadamard to the first bit, then the dyadic controlled phases in increasing order. -/
def stage (n : ℕ) : Command Store (Fin (n + 1)) (tensorMemory (fun _ : Fin (n + 1) => Qubit)) :=
  (.unitaryAt (D := fun _ => Qubit) 0 Qubit.H : Command Store (Fin (n + 1)) _).seq
    (.forList (List.finRange n) fun j => rung j (2 * Real.pi / 2 ^ (j.val + 2)))

/-- A complete Fourier stage converts the leading basis bit to the phase of the whole word.
The target bits keep their computational basis values. -/
theorem derivTot_stage (x : Fin (n + 1) → Fin 2) :
    DerivTot (Store := Store)
      (Assertion.pure (registerProductState (fun _ => Qubit) fun i => UnitState.ofBasis (ZBasis 2)
        (x i))) (stage n) (Assertion.pure (state (Fin.tail x) (basisAngle x))) := by
  let D := fun _ : Fin (n + 1) => Qubit
  let v := fun i => UnitState.ofBasis (ZBasis 2) (x i)
  let φ : ℝ := if x 0 = 0 then 0 else Real.pi
  have head := DerivTot.unitaryAt_productState (Store := Store) (D := D) 0 Qubit.H v
  have he : registerProductState D (Function.update v 0 (UnitState.map Qubit.H.asHom (v 0))) =
      state (Fin.tail x) φ := by
    simp only [registerProductState, Function.update_self, Fin.tail_update_zero]
    rw [show UnitState.map Qubit.H.asHom (v 0) = Qubit.phaseState φ from
      Qubit.hadamard_basis_phaseState (x 0)]
    rfl
  rw [he] at head
  apply DerivTot.seq head
  rw [basisAngle, Fin.sum_univ_succ, show 2 * Real.pi / 2 ^ ((0 : Fin (n + 1)).val + 1) =
    Real.pi by norm_num]
  rw [Fin.sum_univ_def]
  exact derivTot_ladder (fun j : Fin n => 2 * Real.pi / 2 ^ (j.val + 2)) (Fin.tail x)
    (List.finRange n) φ

/-- Total correctness of one Fourier stage for every basis word. -/
theorem validTot_stage (x : Fin (n + 1) → Fin 2) :
    validTot (Store := Store)
      (Assertion.pure (registerProductState (fun _ => Qubit) fun i => UnitState.ofBasis (ZBasis 2)
        (x i))) (stage n) (Assertion.pure (state (Fin.tail x) (basisAngle x))) :=
  (derivTot_stage x).sound

end

end QuantumProgram.FourierLadder
