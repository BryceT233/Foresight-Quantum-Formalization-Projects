/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for source consequence for derivations and validity.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Consequence.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Rules
public import FQFP.QuantumProgram.Logic.SourceAssertion

/-!
# Source consequence for derivations and validity

Entailment strengthens the input and weakens the output of a triple. The two zero-effect
examples witness the information lost by interpreting a source assertion as a masked effect.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Partial derivations under source strengthening and weakening. -/
theorem DerivPar.sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : DerivPar A'.toAssn p B'.toAssn) (hB : B'.Entails B) :
    DerivPar A.toAssn p B.toAssn :=
  DerivPar.conseq hA.toAssn_le h hB.toAssn_le

/-- Total derivations under source strengthening and weakening. -/
theorem DerivTot.sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : DerivTot A'.toAssn p B'.toAssn) (hB : B'.Entails B) :
    DerivTot A.toAssn p B.toAssn :=
  DerivTot.conseq hA.toAssn_le h hB.toAssn_le

/-- Partial semantic validity under source strengthening and weakening. -/
theorem validPar_sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : validPar A'.toAssn p B'.toAssn) (hB : B'.Entails B) :
    validPar A.toAssn p B.toAssn :=
  validPar_conseq hA.toAssn_le h hB.toAssn_le

/-- Total semantic validity under source strengthening and weakening. -/
theorem validTot_sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : validTot A'.toAssn p B'.toAssn) (hB : B'.Entails B) :
    validTot A.toAssn p B.toAssn :=
  validTot_conseq hA.toAssn_le h hB.toAssn_le

/-- Zero effects can conceal a failed classical implication between two total assertions. -/
theorem masked_le_not_source_entails_classical (H : Qudit) :
    ∃ A B : SourceAssertion Unit H, A.toAssn ≤ B.toAssn ∧ ¬ A.Entails B := by
  let zero := SourceEffect.total (Assertion.zero (Store := Unit) (H := H))
  refine ⟨⟨fun _ => True, zero⟩, ⟨fun _ => False, zero⟩, ?_, fun h => h.1 () trivial⟩
  change Assertion.zero.mask _ ≤ Assertion.zero.mask _
  rw [Assertion.zero_mask, Assertion.zero_mask]

/-- With the same true classical condition, zero effects can conceal different domains. -/
theorem masked_le_not_source_entails_defined (H : Qudit) :
    ∃ A B : SourceAssertion Unit H, A.toAssn ≤ B.toAssn ∧ ¬ A.Entails B := by
  let A : SourceAssertion Unit H := ⟨fun _ => True, .total Assertion.zero⟩
  let B : SourceAssertion Unit H := ⟨fun _ => True, ⟨fun _ => False, Assertion.zero⟩⟩
  refine ⟨A, B, ?_, fun h => (h.2 () trivial).1.mp trivial⟩
  change Assertion.zero.mask _ ≤ Assertion.zero.mask _
  rw [Assertion.zero_mask, Assertion.zero_mask]

end QuantumProgram
