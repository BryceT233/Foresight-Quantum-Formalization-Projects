/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the derivation rules of finite sequential iteration.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/ForRule.lean
Qhl/Logic/ForSeqRule.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.For
public import FQFP.QuantumProgram.Logic.Rules

/-!
# Total correctness of finite iteration

A finite loop executes its list of commands in order. A derivation can either pull a
postcondition back through the list or track an invariant indexed by the number of completed steps.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {ι Store Cell : Type*} {H : Qudit} {body : ι → Command Store Cell H}

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
