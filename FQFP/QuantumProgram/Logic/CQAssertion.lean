/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for classical-quantum assertions and history judgments.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/Correctness.lean
Qhl/Logic/Soundness.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Correctness

/-!
# History judgements for classical–quantum assertions

In the judgements of `Qhl/History/Correctness.lean`, the classical precondition restricts
the inputs and the quantum postcondition is evaluated on every terminating history.
`CQAssertion.toAssn` masks an effect family for use in the QHL⁺ proof systems.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

/-- A classical predicate together with a quantum effect at every store. -/
structure CQAssertion (Store : Type*) (H : Qudit) where
  /-- Classical support of the assertion. -/
  cls : Store → Prop
  /-- Quantum observable evaluated at the current store. -/
  op : Store → Operator H
  /-- Each observable lies between zero and the identity in the Löwner order. -/
  isEffect : ∀ σ, op σ ∈ Set.Icc 0 1

variable {Store Cell : Type*} {H : Qudit}

/-- Pair a total effect family with its source classical predicate. -/
def CQAssertion.ofEffect (A : Assertion Store H) (φ : Store → Prop) : CQAssertion Store H :=
  ⟨φ, fun σ => A σ, fun σ => (A σ).property⟩

/-- Bundle the quantum component as a family of effects on all stores. -/
def CQAssertion.effect (q : CQAssertion Store H) : Assertion Store H :=
  fun σ => ⟨q.op σ, q.isEffect σ⟩

/-- Interpret a classical–quantum assertion in the proof system by masking its quantum component. -/
noncomputable def CQAssertion.toAssn (q : CQAssertion Store H) : Assertion Store H :=
  q.effect.mask q.cls

/-- Interpreting a total effect with an unconditional classical predicate recovers the effect. -/
theorem CQAssertion.toAssn_ofEffect_true (A : Assertion Store H) :
    (ofEffect A fun _ => True).toAssn = A :=
  funext fun σ => A.mask_of_pos (φ := fun _ => True) (σ := σ) trivial

/-- At an input satisfying the classical predicate, masking retains the original observable. -/
theorem CQAssertion.toAssn_op_of_cls {q : CQAssertion Store H} {σ : Store} (h : q.cls σ) :
    (q.toAssn σ : Operator H) = q.op σ :=
  congrArg Subtype.val (q.effect.mask_of_pos h)

/-- The masked assertion is bounded by the full effect family at every store. -/
theorem CQAssertion.toAssn_le (q : CQAssertion Store H) : q.toAssn ≤ q.effect := by
  intro σ
  change (q.effect.mask q.cls σ : Operator H) ≤ q.op σ
  by_cases hs : q.cls σ
  · rw [q.effect.mask_of_pos hs]
    exact le_rfl
  · rw [q.effect.mask_of_neg hs]
    exact (q.isEffect σ).1

/-- Total history correctness for inputs satisfying the classical precondition. -/
def modelsTotH (q : CQAssertion Store H) (p : Command Store Cell H) (q' : CQAssertion Store H) :
    Prop := ∀ s : CQState Store H, q.cls s.store →
      ENNReal.ofReal (s.expectation (q.op s.store)) ≤ (Configuration.mk (some p) s).PostH q'.op

/-- Partial history correctness also credits the nonterminating mass of the execution. -/
def modelsParH (q : CQAssertion Store H) (p : Command Store Cell H) (q' : CQAssertion Store H) :
    Prop := ∀ s : CQState Store H, q.cls s.store →
      ENNReal.ofReal (s.expectation (q.op s.store)) ≤ (Configuration.mk (some p) s).PostH q'.op +
        (Configuration.mk (some p) s).nonterminatingMass

/-- Total history correctness entails partial history correctness. -/
theorem modelsTotH.modelsParH {q q' : CQAssertion Store H} {p : Command Store Cell H}
    (h : modelsTotH q p q') : modelsParH q p q' := fun s hs => (h s hs).trans le_self_add

/-- A totally valid triple of masked assertions entails total history correctness. -/
theorem modelsTotH_of_validTot {q q' : CQAssertion Store H} {p : Command Store Cell H}
    (h : validTot q.toAssn p q'.toAssn) : modelsTotH q p q' := by
  intro s hs
  simpa only [CQAssertion.toAssn_op_of_cls hs, CQAssertion.effect] using
    validTot_conseq le_rfl h q'.toAssn_le s

/-- A partially valid triple of masked assertions entails partial history correctness. -/
theorem modelsParH_of_validPar {q q' : CQAssertion Store H} {p : Command Store Cell H}
    (h : validPar q.toAssn p q'.toAssn) : modelsParH q p q' := by
  intro s hs
  simpa only [CQAssertion.toAssn_op_of_cls hs, CQAssertion.effect] using
    validPar_conseq le_rfl h q'.toAssn_le s

end QuantumProgram
