/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for soundness of the two derivation systems.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Soundness.lean
Qhl/Logic/Source/RulesSoundness.lean (soundness of Kraus accumulation)

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Assertion.CQAssertion
public import FQFP.QuantumProgram.Logic.Rules
public import FQFP.QuantumProgram.Logic.Iteration.While

/-!
# Soundness of the QHL⁺ proof systems

Induction on each derivation interprets its rules in the terminal-history semantics.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Total correctness composes at a common intermediate assertion. -/
theorem validTot_seq {A B C : Assertion Store H} {p q : Command Store Cell H}
    (hp : validTot A p B) (hq : validTot B q C) : validTot A (p.seq q) C := by
  intro s
  apply (hp s).trans
  let c := Configuration.mk (some p) s
  change c.PostH _ ≤ (c.seqWith q).PostH _
  rw [Configuration.PostH_seqWith _ _ C.isPositive, c.PostH_eq_tsum_terminalWeightAt B.isPositive]
  exact tsum_le_tsum fun j => c.terminalWeightAt_mono j hq

/-- Partial correctness composes with the residual mass of both execution phases. -/
theorem validPar_seq {A B C : Assertion Store H} {p q : Command Store Cell H}
    (hp : validPar A p B) (hq : validPar B q C) : validPar A (p.seq q) C := by
  intro s
  apply (hp s).trans
  let c := Configuration.mk (some p) s
  change c.PostH _ + c.nonterminatingMass ≤ (c.seqWith q).PostH _ + (c.seqWith q).nonterminatingMass
  rw [Configuration.PostH_seqWith _ _ C.isPositive, Configuration.nonterminatingMass_seqWith,
    add_comm c.nonterminatingMass, ← add_assoc, ← tsum_add]
  refine add_le_add (tsum_le_tsum fun j => ?_) le_rfl
  rw [← c.postAtE_eq_ofReal_postAt j B.isPositive, ← c.terminalWeightAt_add]
  exact c.terminalWeightAt_mono j hq

private theorem next_ite (b : Store → Bool) (p q : Command Store Cell H) (s : CQState Store H) :
    (Configuration.mk (some (.ite b p q)) s).next =
      [Configuration.mk (some (if b s.store then p else q)) s] := rfl

/-- A conditional selects the totally valid branch at the current store. -/
theorem validTot_cond {b : Store → Bool} {A₁ A₀ B : Assertion Store H}
    {p q : Command Store Cell H} (hp : validTot A₁ p B) (hq : validTot A₀ q B) :
    validTot (Assertion.guard b A₁ A₀) (.ite b p q) B := by
  intro s
  rw [Configuration.PostH_singleton (next_ite b p q s)]
  cases hb : b s.store with
  | false => simpa [Assertion.guard, hb] using hq s
  | true => simpa [Assertion.guard, hb] using hp s

/-- A conditional credits the selected branch's post-expectation and residual trace. -/
theorem validPar_cond {b : Store → Bool} {A₁ A₀ B : Assertion Store H}
    {p q : Command Store Cell H} (hp : validPar A₁ p B) (hq : validPar A₀ q B) :
    validPar (Assertion.guard b A₁ A₀) (.ite b p q) B := by
  intro s
  simp only [Configuration.nonterminatingMass, ← Configuration.PostH_one,
    Configuration.PostH_singleton (next_ite b p q s)]
  cases hb : b s.store with
  | false => simpa [Assertion.guard, hb, Configuration.nonterminatingMass, Configuration.PostH_one]
      using hq s
  | true => simpa [Assertion.guard, hb, Configuration.nonterminatingMass, Configuration.PostH_one]
      using hp s

/-- Every derivation in the partial-correctness system is semantically valid. -/
theorem DerivPar.sound {A B : Assertion Store H} {p : Command Store Cell H} (h : DerivPar A p B) :
    validPar A p B := by
  induction h with
  | skip A => exact (validTot_skip A).validPar
  | assign f A => exact (validTot_assign f A).validPar
  | channel f A => exact (validTot_channel f A).validPar
  | unitary r U A => exact (validTot_unitary r U A).validPar
  | measure r I upd A => exact (validTot_measure r I upd A).validPar
  | seq _ _ ihp ihq => exact validPar_seq ihp ihq
  | cond _ _ ihp ihq => exact validPar_cond ihp ihq
  | whileLoop _ ih => exact validPar_while ih
  | conseq hA _ hB ih => exact validPar_conseq hA ih hB

/-- Every total-correctness derivation, including both ranking rules, is semantically valid. -/
theorem DerivTot.sound {A B : Assertion Store H} {p : Command Store Cell H} (h : DerivTot A p B) :
    validTot A p B := by
  induction h with
  | skip A => exact validTot_skip A
  | assign f A => exact validTot_assign f A
  | channel f A => exact validTot_channel f A
  | unitary r U A => exact validTot_unitary r U A
  | measure r I upd A => exact validTot_measure r I upd A
  | seq _ _ ihp ihq => exact validTot_seq ihp ihq
  | cond _ _ ihp ihq => exact validTot_cond ihp ihq
  | whileLoop t _ ih => exact validTot_while t ih
  | whileLoopSource t hbound _ _ ihInv ihRank => exact validTot_while_source t hbound ihInv ihRank
  | convex w hw _ ih => exact validTot_convex w hw ih
  | kraus K hK hp _ ih => exact validTot_kraus K hK hp ih
  | conseq hA _ hB ih => exact validTot_conseq hA ih hB

/-- A total-correctness derivation of the masked assertions proves the total history judgement. -/
theorem modelsTotH_of_derivTot {q q' : CQAssertion Store H} {p : Command Store Cell H}
    (h : DerivTot q.toAssn p q'.toAssn) : modelsTotH q p q' :=
  modelsTotH_of_validTot h.sound

/-- A partial-correctness derivation of masked assertions proves the partial history judgement. -/
theorem modelsParH_of_derivPar {q q' : CQAssertion Store H} {p : Command Store Cell H}
    (h : DerivPar q.toAssn p q'.toAssn) : modelsParH q p q' :=
  modelsParH_of_validPar h.sound

end QuantumProgram
