/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for classical write-back, register checks and branch mass under measurement.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/State.lean
Qhl/Program/Step.lean
Qhl/Program/Spec.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.CQM.Qudit.Measurement.Instrument
import Mathlib.Data.List.FinRange

/-!
# A quantum measurement with classical write-back

The measurement clause of QHL⁺ ends the instruction with classical store `upd i σ`
and quantum operator `Kᵢ ρ Kᵢ†` for each outcome `i`. The trace carries the branch
weight. A repeated cell in the evaluated register blocks the instruction.

`measurementSuccessors` returns the classical–quantum states of these terminal
configurations in outcome order. Its instrument acts on the whole system. For a
local measurement, the caller supplies the operators lifted from the evaluated register.

The source clause is `Qhl.stepProg_measure` in `Qhl/Program/Step.lean`,
qedia/quantum-formal-verification, revision `3dfe80b893e2ab949a0428a2e18c06153b310bd0`.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- A classical store and a positive quantum operator whose trace carries its weight. -/
@[ext] structure CQState (Store : Type*) (H : Qudit) where
  /-- Values of the classical variables. -/
  store : Store
  /-- The unnormalized quantum state on the whole system. -/
  op : Operator H
  /-- The quantum operator is positive, also for a zero-weight branch. -/
  positive : op.IsPositive

/-- Apply a quantum channel to a weighted branch while retaining the classical store. -/
def CQState.map {Store : Type*} {H K : Qudit} (s : CQState Store H) (Φ : QuantumChannel H K) :
    CQState Store K :=
  ⟨s.store, Φ.toSuperoperator s.op, Φ.completelyPositive.isPositive _ s.positive⟩

variable {Store Cell : Type*} {H : Qudit} {m k : ℕ}

/-- The terminal state of a measurement branch, with its outcome written to the store. -/
def measurementBranch {K : Qudit} (I : Instrument H K (Fin m)) (upd : Fin m → Store → Store)
    (s : CQState Store H) (i : Fin m) : CQState Store K :=
  ⟨upd i s.store, I.branch i s.op, I.branch_positive i s.positive⟩

/-- A single Kraus operator per outcome gives precisely the conjugation in the step rule. -/
theorem measurementBranch_ofOperators (K : Fin m → Operator H)
    (hK : ∑ i, (K i).adjoint ∘ₗ K i = 1) (upd : Fin m → Store → Store)
    (s : CQState Store H) (i : Fin m) :
    measurementBranch (Instrument.ofOperators K hK) upd s i =
      ⟨upd i s.store, K i ∘ₗ s.op ∘ₗ (K i).adjoint, s.positive.conj_adjoint (K i)⟩ := rfl

variable (r : Store → Fin k → Cell)
  (measure : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
  (upd : Fin m → Store → Store) (s : CQState Store H)

/-- The ordered successors of a single measurement, after evaluating its register. -/
noncomputable def measurementSuccessors : List (CQState Store H) := by
  classical
  exact if h : Function.Injective (r s.store) then
    List.ofFn (measurementBranch (measure s.store h) upd s)
  else []

/-- A valid register yields one terminal state per outcome, in the source order. -/
theorem measurementSuccessors_of_injective (h : Function.Injective (r s.store)) :
    measurementSuccessors r measure upd s =
      (List.finRange m).map (measurementBranch (measure s.store h) upd s) := by
  rw [measurementSuccessors, dite_eq_left h, List.ofFn_eq_map]

/-- Looking up an outcome retains its classical write-back and unnormalized operator. -/
theorem getElem?_measurementSuccessors (h : Function.Injective (r s.store)) (i : Fin m) :
    (measurementSuccessors r measure upd s)[i.val]? =
      some (measurementBranch (measure s.store h) upd s i) := by
  simp [measurementSuccessors, h, i.isLt]

/-- If two positions name the same cell, the measurement has no successors. -/
theorem measurementSuccessors_of_not_injective (h : ¬ Function.Injective (r s.store)) :
    measurementSuccessors r measure upd s = [] := by
  rw [measurementSuccessors, dite_eq_right h]

/-- The traces of the actual successor list sum to the input trace for a valid register. -/
theorem sum_trace_measurementSuccessors (h : Function.Injective (r s.store)) :
    ((measurementSuccessors r measure upd s).map (fun t => t.op.trace)).sum = s.op.trace := by
  rw [measurementSuccessors, dite_eq_left h, List.map_ofFn, List.sum_ofFn]
  exact (measure s.store h).sum_trace_branch s.op

end QuantumProgram
