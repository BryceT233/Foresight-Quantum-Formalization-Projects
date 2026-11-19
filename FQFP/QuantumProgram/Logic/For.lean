/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for finite sequential iteration and its derivation rules.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/For.lean
Qhl/Logic/ForRule.lean
Qhl/Logic/ForSeqRule.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Rules

/-!
# Total correctness of finite iteration

A finite loop executes its list of commands in order. A derivation can either pull a
postcondition back through the list or track an invariant indexed by the number of completed steps.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {ι Store Cell : Type*} {H : Qudit}

/-- Sequence the indexed commands from left to right, ending with skip. -/
def Command.forList (l : List ι) (body : ι → Command Store Cell H) : Command Store Cell H :=
  l.foldr (fun i rest => (body i).seq rest) .skip

/-- The empty iteration performs a skip. -/
@[simp] theorem Command.forList_nil (body : ι → Command Store Cell H) :
    forList [] body = .skip := rfl

/-- A nonempty iteration executes its head before its tail. -/
@[simp] theorem Command.forList_cons (i : ι) (l : List ι) (body : ι → Command Store Cell H) :
    forList (i :: l) body = (body i).seq (forList l body) := rfl

variable {body : ι → Command Store Cell H}

/-- Fold the certified precondition transformers back from the final assertion. -/
theorem DerivTot.forList {pre : ι → Assertion Store H → Assertion Store H}
    (h : ∀ i B, DerivTot (pre i B) (body i) B) (l : List ι) (A : Assertion Store H) :
    DerivTot (l.foldr pre A) (.forList l body) A := by
  induction l with
  | nil => exact .skip A
  | cons i l ih => exact .seq (h i _) ih

/-- Compose a chain of assertions indexed by list position, allowing repeated indices. -/
theorem DerivTot.forList_chain (l : List ι) (J : ℕ → Assertion Store H)
    (step : ∀ i : Fin l.length, DerivTot (J i.val) (body (l.get i)) (J (i.val + 1))) :
    DerivTot (J 0) (.forList l body) (J l.length) := by
  induction l generalizing J with
  | nil => exact .skip _
  | cons a l ih =>
    exact .seq (step 0) (ih (fun k => J (k + 1)) (fun i => step i.succ))

/-- Stage `i` advances the invariant from natural index `i` to `i + 1` on a finite range. -/
theorem DerivTot.forList_finRange {n : ℕ} {cmd : Fin n → Command Store Cell H}
    (J : ℕ → Assertion Store H)
    (step : ∀ i : Fin n, DerivTot (J i.val) (cmd i) (J (i.val + 1))) :
    DerivTot (J 0) (.forList (List.finRange n) cmd) (J n) := by
  have h := forList_chain (body := cmd) (List.finRange n) J (fun i => by
    simpa only [List.get_eq_getElem, List.getElem_finRange, Fin.val_cast] using
      step ((List.finRange n).get i))
  simpa only [List.length_finRange] using h

end QuantumProgram
