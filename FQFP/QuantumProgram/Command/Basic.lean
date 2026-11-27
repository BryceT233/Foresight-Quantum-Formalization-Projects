/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for command syntax, configurations and ordered one-step execution.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/Syntax.lean
Qhl/Program/State.lean
Qhl/Program/Step.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.Measurement
public import FQFP.QuantumProgram.Circuit.Unitary

/-!
# Small-step execution with classical control

The control and sequencing clauses follow `Qhl/Program/Step.lean`. Quantum instructions
receive their whole-memory actions after register evaluation. In particular a supplied
initialization channel can run as a channel instruction. Registers are checked for repeated
cells before applying a local unitary or enumerating measurement branches.

For an ordered tensor register, `Command.unitaryOnRegister` and `Command.measureOnRegister`
accept operations on its local memory. `Command.unitaryOn` and `Command.measureOn`
evaluate the register addresses in the classical store.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- Commands on a classical store and a fixed quantum memory with named cells. -/
inductive Command (Store Cell : Type*) (H : Qudit) where
  /-- Terminate successfully without modifying the state. -/
  | skip
  /-- Update the classical store. -/
  | assign (f : Store → Store)
  /-- Apply an evaluated whole-memory channel. -/
  | channel (f : Store → QuantumChannel H H)
  /-- Apply a local unitary supplied in its whole-memory representation. -/
  | unitary {k : ℕ} (r : Store → Fin k → Cell)
      (gate : ∀ σ, Function.Injective (r σ) → UnitaryProgram H)
  /-- Measure the evaluated register and write the outcome to the store. -/
  | measure {k m : ℕ} (r : Store → Fin k → Cell)
      (instrument : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
      (update : Fin m → Store → Store)
  /-- Execute the second command after the first finishes. -/
  | seq (first second : Command Store Cell H)
  /-- Select a continuation using the classical store. -/
  | ite (guard : Store → Bool) (yes no : Command Store Cell H)
  /-- Repeat the body while the classical guard holds. -/
  | whileDo (guard : Store → Bool) (body : Command Store Cell H)

/-- The remaining command (`none` at termination) and the weighted classical–quantum state. -/
structure Configuration (Store Cell : Type*) (H : Qudit) where
  /-- The command still to be executed. -/
  control : Option (Command Store Cell H)
  /-- The classical store and the positive operator at this occurrence. -/
  state : CQState Store H

variable {Store Cell : Type*} {H : Qudit}

/-- Every assignment and measurement write-back in the command preserves the given
classical parameter, including writes nested under conditionals and loops. -/
def Command.PreservesParameters {P : Type*} (p : Command Store Cell H) (read : Store → P) : Prop :=
  match p with
  | .skip | .channel _ | .unitary _ _ => True
  | .assign f => ∀ σ, read (f σ) = read σ
  | .measure _ _ upd => ∀ i σ, read (upd i σ) = read σ
  | .seq p q | .ite _ p q => p.PreservesParameters read ∧ q.PreservesParameters read
  | .whileDo _ body => body.PreservesParameters read

/-- Every command preserves a constant classical parameter. -/
theorem Command.preservesParameters_const {P : Type*} (p : Command Store Cell H) (a : P) :
    p.PreservesParameters (fun _ => a) := by
  induction p <;> simp_all [PreservesParameters]

/-- Attach a continuation to the result of a step of the first command. -/
def Configuration.seqWith (c : Configuration Store Cell H) (q : Command Store Cell H) :
    Configuration Store Cell H :=
  ⟨some (c.control.elim q (·.seq q)), c.state⟩

/-- Ordered one-step successors of a running command. -/
noncomputable def Command.step : Command Store Cell H → CQState Store H →
    List (Configuration Store Cell H)
  | .skip, s => [⟨none, s⟩]
  | .assign f, s => [⟨none, { s with store := f s.store }⟩]
  | .channel f, s => [⟨none, s.map (f s.store)⟩]
  | .unitary r gate, s => open Classical in
      if h : Function.Injective (r s.store) then [⟨none, s.map (gate s.store h).toChannel⟩] else []
  | .measure r inst upd, s => (measurementSuccessors r inst upd s).map (⟨none, ·⟩)
  | .seq p q, s => (p.step s).map (·.seqWith q)
  | .ite b p q, s => [⟨some (if b s.store then p else q), s⟩]
  | .whileDo b p, s =>
      if b s.store then [⟨some (p.seq (.whileDo b p)), s⟩] else [⟨none, s⟩]

/-- Terminal configurations have no successors. -/
noncomputable def Configuration.next (c : Configuration Store Cell H) :
    List (Configuration Store Cell H) := c.control.elim [] (·.step c.state)

/-- A conditional enters the selected branch without modifying the state. -/
theorem Configuration.next_ite (b : Store → Bool) (p q : Command Store Cell H)
    (s : CQState Store H) :
    (Configuration.mk (some (.ite b p q)) s).next =
      [⟨some (if b s.store then p else q), s⟩] := rfl

/-- A true guard hands control to the body followed by the same loop. -/
theorem next_whileDo_of_true {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = true) :
    (Configuration.mk (some (.whileDo b p)) s).next =
      [(Configuration.mk (some p) s).seqWith (.whileDo b p)] := by
  simp [Configuration.next, Command.step, Configuration.seqWith, hb]

/-- A false guard terminates the loop in the current state. -/
theorem next_whileDo_of_false {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = false) :
    (Configuration.mk (some (.whileDo b p)) s).next = [⟨none, s⟩] := by
  simp [Configuration.next, Command.step, hb]

/-- Configurations at exactly the given depth, retaining branch order and multiplicity. -/
noncomputable def Configuration.frontier (c : Configuration Store Cell H) :
    ℕ → List (Configuration Store Cell H)
  | 0 => [c]
  | n + 1 => (c.frontier n).flatMap Configuration.next

/-- Resume execution at each occurrence of an intermediate frontier, in branch order. -/
theorem Configuration.frontier_add (c : Configuration Store Cell H) (m n : ℕ) :
    c.frontier (m + n) = (c.frontier m).flatMap (·.frontier n) := by
  induction n with
  | zero => simp [frontier]
  | succ n ih =>
    rw [Nat.add_succ, frontier, ih, List.flatMap_assoc]
    rfl

/-- Partition the next depth by the first successor, retaining repeated occurrences. -/
theorem Configuration.frontier_succ (c : Configuration Store Cell H) (n : ℕ) :
    c.frontier (n + 1) = c.next.flatMap (·.frontier n) := by
  rw [Nat.add_comm, c.frontier_add]
  simp [frontier]

/-- With a single successor, the frontier one step deeper is that successor's frontier. -/
theorem Configuration.frontier_succ_of_next_eq_singleton {c d : Configuration Store Cell H}
    (h : c.next = [d]) (n : ℕ) : c.frontier (n + 1) = d.frontier n := by
  simp [frontier_succ, h]

/-- A terminated configuration has no occurrences at any positive depth. -/
theorem Configuration.frontier_succ_terminal (s : CQState Store H) (n : ℕ) :
    (Configuration.mk (Cell := Cell) none s).frontier (n + 1) = [] := by
  rw [frontier_succ]
  rfl

/-- Execution can resume at the sole configuration of an intermediate frontier. -/
theorem Configuration.frontier_add_of_singleton {c d : Configuration Store Cell H} {m : ℕ}
    (h : c.frontier m = [d]) (n : ℕ) : c.frontier (m + n) = d.frontier n := by
  simp [c.frontier_add m n, h]

end QuantumProgram
