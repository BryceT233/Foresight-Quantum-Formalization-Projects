/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the nested stage and phase counters.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/QFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierLadder
public import FQFP.QuantumProgram.Logic.CountedUnitary

/-!
# The two counted loops of the Fourier circuit

The first coordinate selects the Hadamard wire. The second selects successive targets
to its right, with a shorter ladder at every stage. After the stage loop each wire holds
the Fourier phase of the input suffix starting at that wire, in the original wire order.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.FourierIteration

noncomputable section

/-- Classical store containing the stage and rung counters, in that order. -/
abbrev Store := ℕ × ℕ

/-- The ordered register of qubits used by both loops. -/
abbrev Memory (n : ℕ) := tensorMemory (fun _ : Fin n => Qubit)

/-- The stage index in the first classical coordinate. -/
def stageCounter : CounterLens (ℕ × ℕ) := ⟨Prod.fst, fun σ k => (k, σ.2), fun _ _ => rfl⟩

/-- The rung index in the second classical coordinate. -/
def rungCounter : CounterLens (ℕ × ℕ) := ⟨Prod.snd, fun σ k => (σ.1, k), fun _ _ => rfl⟩

variable (n : ℕ) [NeZero n]

/-- Control wire of stage `k`. -/
def control (k : ℕ) := Fin.ofNat n k

/-- Target wire of rung `t` in stage `k`. -/
def target (k t : ℕ) := Fin.ofNat n (k + 1 + t)

/-- Controlled phase angle of the zero-indexed rung. -/
def angle (t : ℕ) : ℝ := 2 * Real.pi / 2 ^ (t + 2)

/-- Hadamard on the wire selected by the stage counter. -/
def hadamardGate (k : ℕ) : UnitaryProgram (Memory n) :=
  .gateHom (Register.site (fun _ => Qubit) (control n k)) Qubit.H.asHom

/-- Controlled phase selected by the stage and rung counters. -/
def rungGate (k t : ℕ) : UnitaryProgram (Memory n) :=
  FourierLadder.phaseGate (control n k) (target n k t) (angle t)

/-- Read the stage counter and execute the corresponding Hadamard gate. -/
def hadamard : Command Store (Fin n) (Memory n) :=
  .unitary (fun σ (_ : Fin 1) => control n σ.1)
    (fun σ _ => hadamardGate n σ.1)

/-- A controlled phase on the two wires selected by the current counter values. -/
def rung : Command Store (Fin n) (Memory n) :=
  .unitary (fun σ => ![control n σ.1, target n σ.1 σ.2])
    (fun σ _ => rungGate n σ.1 σ.2)

/-- Count through the remaining wires to the right of the current stage. -/
def ladder : Command Store (Fin n) (Memory n) :=
  .counted rungCounter (fun σ => n - 1 - σ.1) (rung n)

/-- Count through all Fourier stages in increasing wire order. -/
def iteration : Command Store (Fin n) (Memory n) :=
  .counted stageCounter (fun _ => n) ((hadamard n).seq (ladder n))

variable {n} (x : Fin n → Fin 2)

/-- Big-endian Fourier angle of the input suffix starting at wire `i`. -/
def suffixAngle (i : Fin n) : ℝ :=
  FourierLadder.basisAngle fun t : Fin (n - 1 - i.val + 1) => x (Fin.ofNat n (i.val + t.val))

/-- Phase on wire `k` after its Hadamard and first `t` rungs. -/
def partialAngle (k t : ℕ) : ℝ :=
  (if x (control n k) = 0 then 0 else Real.pi) +
    ∑ j ∈ Finset.range t, if x (target n k j) = 0 then 0 else angle j

/-- At the ladder bound the accumulated phase is the full binary suffix angle. -/
theorem partialAngle_full (k : ℕ) (hk : k < n) :
    partialAngle x k (n - 1 - k) = suffixAngle x (control n k) := by
  have hc : (control n k).val = k := Nat.mod_eq_of_lt hk
  rw [suffixAngle, hc, FourierLadder.basisAngle, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.add_zero, zero_add, pow_one, Fin.val_succ]
  rw [show 2 * Real.pi / 2 = Real.pi by ring]
  unfold partialAngle control target angle
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show k + 1 + i.val = k + (i.val + 1) by lia]

/-- Local factors before the stage with index `k`. -/
def factors (k : ℕ) (i : Fin n) : UnitState Qubit :=
  if i.val < k then Qubit.phaseState (suffixAngle x i) else UnitState.ofBasis (ZBasis 2) (x i)

/-- Local factors after the Hadamard and `t` rungs of stage `k`. -/
def mid (k t : ℕ) : Fin n → UnitState Qubit :=
  Function.update (factors x k) (control n k) (Qubit.phaseState (partialAngle x k t))

private theorem mid_full (k : ℕ) (hk : k < n) :
    mid x k (n - 1 - k) = factors x (k + 1) := by
  have hc : (control n k).val = k := Nat.mod_eq_of_lt hk
  funext i
  by_cases hi : i = control n k
  · subst i
    simp [mid, factors, hc, partialAngle_full x k hk]
  · have hne : i.val ≠ k := fun h => hi (Fin.ext (h.trans hc.symm))
    simp only [mid, Function.update_of_ne hi, factors, show i.val < k + 1 ↔ i.val < k by lia]

/-- Each active rung targets a wire strictly to the right of its control. -/
theorem control_lt_target {k t : ℕ} (ht : t < n - 1 - k) :
    control n k < target n k t := by
  change k % n < (k + 1 + t) % n
  rw [Nat.mod_eq_of_lt (by lia : k < n), Nat.mod_eq_of_lt (by lia : k + 1 + t < n)]
  lia

/-- The rung addresses different wires whenever its guard is true. -/
theorem rung_injective {σ : Store} (ht : σ.2 < n - 1 - σ.1) :
    Function.Injective ![control n σ.1, target n σ.1 σ.2] := by
  have hne := (control_lt_target ht).ne
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-- Tensor product of the qubit factors in register order. -/
abbrev product {n : ℕ} (v : Fin n → UnitState Qubit) :=
  registerProductState (fun _ => Qubit) v

/-- Iterate a family of rung effects under a predicate stable under rung-counter writes. -/
theorem count_rungs (P : Store → Prop) (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ)
    (J : ℕ → ℕ → Set.Icc (0 : Operator (Memory n)) 1)
    (step : SourceDerivTot
      (.ofEffect (fun σ => J σ.1 σ.2) fun σ => P σ ∧ σ.2 < n - 1 - σ.1) (rung n)
      (.ofEffect (fun σ => J σ.1 (σ.2 + 1)) fun σ => P σ ∧ σ.2 < n - 1 - σ.1)) :
    SourceDerivTot (.ofEffect (fun σ => J σ.1 0) P) (ladder n)
      (.ofEffect (fun σ => J σ.1 (n - 1 - σ.1)) fun σ => P σ ∧ σ.2 = n - 1 - σ.1) := by
  exact SourceDerivTot.countedGateFamily rungCounter (fun σ => n - 1 - σ.1) P hP
    (fun _ _ => rfl) (fun t σ => J σ.1 t) (fun _ _ _ => rfl) _ _
    (fun _ _ ht => rung_injective ht) step

/-- Product state after the first `k` stages. Earlier wires hold their suffix phases and
the remaining wires still hold the input basis bits. -/
def stageState (k : ℕ) : UnitState (Memory n) := product (factors x k)

/-- All sites still carry the input basis bits at the first stage. -/
theorem stageState_zero :
    stageState x 0 = product (fun i => UnitState.ofBasis (ZBasis 2) (x i)) := by
  apply congrArg product
  funext i
  simp [factors]

/-- Every site carries its suffix phase after the last stage. -/
theorem stageState_full :
    stageState x n = product (fun i => Qubit.phaseState (suffixAngle x i)) := by
  apply congrArg product
  funext i
  simp [factors]

/-- Product state at rung `t` of the stage currently selected by the first counter. -/
def ladderState (k t : ℕ) : UnitState (Memory n) := product (mid x k t)

/-- The Hadamard pass initializes the ladder vector, with its exact phase. -/
theorem hadamardGate_stageState (k : ℕ) (hk : k < n) :
    (hadamardGate n k).toOperator (stageState x k).val = (ladderState x k 0).val := by
  change ((Register.site (fun _ => Qubit) (control n k)).liftHom Qubit.H.asHom)
    (product (factors x k)).val = (product (mid x k 0)).val
  rw [Register.liftHom_site_productState]
  have hc : (control n k).val = k := Nat.mod_eq_of_lt hk
  have hv : factors x k (control n k) = UnitState.ofBasis (ZBasis 2) (x (control n k)) := by
    simp [factors, hc]
  simp [mid, hv, Qubit.hadamard_basis_phaseState, partialAngle, product]

/-- Each controlled phase advances the ladder vector by one rung. -/
theorem rungGate_ladderState (k t : ℕ) (ht : t < n - 1 - k) :
    (rungGate n k t).toOperator (ladderState x k t).val = (ladderState x k (t + 1)).val := by
  change (FourierLadder.phaseGate (control n k) (target n k t) (angle t)).toOperator
    (product (mid x k t)).val = (product (mid x k (t + 1))).val
  have hlt := control_lt_target ht
  have hj : (target n k t).val = k + 1 + t := Nat.mod_eq_of_lt (by lia)
  have hv : mid x k t (target n k t) = UnitState.ofBasis (ZBasis 2) (x (target n k t)) := by
    simp [mid, Function.update_of_ne hlt.ne', factors, hj, show ¬k + 1 + t < k by lia]
  rw [FourierLadder.phaseGate_productState _ _ hlt _ (partialAngle x k t) _ _ (by simp [mid]) hv]
  simp only [mid, Function.update_idem, partialAngle, Finset.sum_range_succ, add_assoc]

/-- The last ladder vector is the entry vector of the next stage. -/
theorem ladderState_full (k : ℕ) (hk : k < n) :
    ladderState x k (n - 1 - k) = stageState x (k + 1) :=
  congrArg product (mid_full x k hk)

/-- Starting just after the Hadamard, the counted ladder completes the selected stage
and exits with the rung counter equal to its stage-dependent bound. -/
theorem sourceDeriv_ladder (P : Store → Prop) (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ)
    (hk : ∀ σ, P σ → σ.1 < n) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (ladderState x σ.1 0) σ) P)
      (ladder n) (.ofEffect (fun σ => Assertion.pure (stageState x (σ.1 + 1)) σ)
        fun σ => P σ ∧ σ.2 = n - 1 - σ.1) := by
  apply SourceDerivTot.conseq (fun _ h => ⟨h, le_rfl⟩)
    (count_rungs P hP (fun k t => Assertion.pure (ladderState x k t) ()) _) _
  · exact SourceDerivTot.unitary_pure _ _ _ _ (fun _ h => rung_injective h.2)
      (fun σ h => rungGate_ladderState x σ.1 σ.2 h.2)
  · intro σ h
    exact ⟨h, le_of_eq (congrArg (fun v => (Assertion.pure (product v) σ).val)
      (mid_full x σ.1 (hk σ h.1)))⟩

/-- A Hadamard and its counted ladder advance the stage invariant by one. -/
theorem sourceDeriv_stage (P : ℕ → Prop) (hP : ∀ k, P k → k < n) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (stageState x σ.1) σ) fun σ => P σ.1)
      ((hadamard n).seq (ladder n))
      (.ofEffect (fun σ => Assertion.pure (stageState x (σ.1 + 1)) σ) fun σ => P σ.1) := by
  have head : SourceDerivTot
      (.ofEffect (fun σ => Assertion.pure (stageState x σ.1) σ) fun σ => P σ.1) (hadamard n)
      (.ofEffect (fun σ => Assertion.pure (ladderState x σ.1 0) σ) fun σ => P σ.1) := by
    unfold hadamard
    apply SourceDerivTot.unitary_pure (Store := Store) (k := 1) _ _
      (fun σ => stageState x σ.1) (fun σ => ladderState x σ.1 0)
      (fun _ _ => Function.injective_of_subsingleton _)
    exact fun σ h => hadamardGate_stageState x σ.1 (hP σ.1 h)
  exact .seq head (.conseq (fun _ h => ⟨h, le_rfl⟩)
    (sourceDeriv_ladder x (fun σ => P σ.1) (fun _ _ => Iff.rfl) (fun σ => hP σ.1))
    (fun _ h => ⟨h.1, le_rfl⟩))

/-- A Fourier stage preserves the identity effect on every stage-counter predicate. -/
theorem stage_identity (P : ℕ → Prop) :
    SourceDerivTot (.ofEffect Assertion.identity fun σ => P σ.1) ((hadamard n).seq (ladder n))
      (.ofEffect Assertion.identity fun σ => P σ.1) := by
  apply SourceDerivTot.seq (SourceDerivTot.unitary_identity _ _ _
    (fun _ _ => Function.injective_of_subsingleton _))
  have d := count_rungs (n := n) (fun σ => P σ.1) (fun _ _ => Iff.rfl)
    (fun _ _ => Assertion.identity ())
    (SourceDerivTot.unitary_identity _ _ _ (fun _ h => rung_injective h.2))
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ h => ⟨h.1, le_rfl⟩)

/-- Iterate a pure-state stage invariant and retain the exact exit counter. -/
theorem sourceDeriv_iteration_of_stage (v : ℕ → UnitState (Memory n))
    (step : SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) fun σ => σ.1 < n)
      ((hadamard n).seq (ladder n))
      (.ofEffect (fun σ => Assertion.pure (v (σ.1 + 1)) σ) fun σ => σ.1 < n)) :
    SourceDerivTot (.ofEffect (Assertion.pure (v 0)) fun _ => True) (iteration n)
      (.ofEffect (Assertion.pure (v n)) fun σ => σ.1 = n) := by
  have d := SourceDerivTot.countedFamily stageCounter (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun k => Assertion.pure (v k))
    (fun _ _ _ => rfl) _ (by simpa only [true_and, stageCounter] using step)
    (fun z => stage_identity (n := n) fun k => True ∧ k < n ∧ ((n - k : ℕ) : ℤ) = z)
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ h => ⟨h.2, le_rfl⟩)

/-- The outer counter selects every stage in turn and exits at the register width. -/
theorem sourceDeriv_iteration :
    SourceDerivTot (.ofEffect (Assertion.pure (stageState x 0)) fun _ => True) (iteration n)
      (.ofEffect (Assertion.pure (stageState x n)) fun σ => σ.1 = n) :=
  sourceDeriv_iteration_of_stage (stageState x) (sourceDeriv_stage x (· < n) (fun _ h => h))

/-- Total correctness on every basis word. The output has one Fourier phase for each suffix,
in wire order, and the final stage counter equals the width for every initial store. -/
theorem validTot_iteration :
    validTot (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) (iteration n)
      ((Assertion.pure (product fun i => Qubit.phaseState (suffixAngle x i))).mask
        fun σ => σ.1 = n) := by
  have d := (sourceDeriv_iteration x).sound
  rw [CQAssertion.toAssn_ofEffect_true] at d
  rw [stageState_zero, stageState_full] at d
  exact d

end

end QuantumProgram.FourierIteration
