/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for source derivations, soundness, measurement and Kraus accumulation.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Rules.lean
Qhl/Logic/Source/RulesSoundness.lean
Qhl/Logic/Source/MeasurementSelected.lean
Qhl/Logic/Source/ConvexDerived.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Soundness
public import FQFP.QuantumProgram.Logic.Source.Consequence
public import FQFP.QuantumProgram.Logic.Source.Convex
public import FQFP.QuantumProgram.Logic.Source.Kraus

/-!
# Source correctness rules on evaluated operands

Classical support is explicit in a `CQAssertion`. Selected measurement follows from the
all-outcome rule and the rule moving a quantum mask into classical support. Kraus accumulation
combines branch derivations while retaining the domain of every operand.
-/

@[expose] public section

open Qudit
open scoped NNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

private theorem mask_le_of {A B : Assertion Store H} {φ : Store → Prop}
    (h : ∀ σ, φ σ → A σ ≤ B σ) : A.mask φ ≤ B := by
  intro σ
  by_cases hc : φ σ
  · rw [A.mask_of_pos hc]
    exact h σ hc
  · change (A.mask φ σ : Operator H) ≤ _
    rw [A.mask_of_neg hc]
    exact (B σ).2.1

private theorem mask_and (A : Assertion Store H) (φ χ : Store → Prop) :
    (A.mask φ).mask χ = A.mask fun σ => φ σ ∧ χ σ := by
  funext σ
  by_cases hp : φ σ <;> by_cases hq : χ σ <;> simp [Assertion.mask, hp, hq]

/-- Restrict the classical support to a branch of a conditional, retaining its quantum effect. -/
def CQAssertion.onBranch (A : CQAssertion Store H) (b : Store → Bool) (v : Bool) :
    CQAssertion Store H := { A with cls := fun σ => A.cls σ ∧ b σ = v }

private theorem guard_onBranch (A : CQAssertion Store H) (b : Store → Bool) :
    Assertion.guard b (A.onBranch b true).toAssn (A.onBranch b false).toAssn = A.toAssn := by
  have h (v : Bool) : (A.onBranch b v).toAssn = A.toAssn.mask (fun σ => b σ = v) :=
    (mask_and A.effect A.cls _).symm
  rw [h, h]
  funext σ
  cases hb : b σ <;> simp [Assertion.guard, hb, Assertion.mask]

/-- Source proof trees for assignments, evaluated quantum operations, sequencing and
integer-ranked loops. Every register in this fragment is defined on the classical support. -/
inductive SourceDerivTot : CQAssertion Store H → Command Store Cell H → CQAssertion Store H → Prop
  /-- Skipping preserves the entire source assertion. -/
  | skip (A : CQAssertion Store H) : SourceDerivTot A .skip A
  /-- Each branch may assume its guard value. -/
  | cond {A B : CQAssertion Store H} {p q : Command Store Cell H} (b : Store → Bool) :
      SourceDerivTot (A.onBranch b true) p B → SourceDerivTot (A.onBranch b false) q B →
      SourceDerivTot A (.ite b p q) B
  /-- Substitute into both the classical predicate and the quantum effect. -/
  | assign (f : Store → Store) (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivTot (.ofEffect (A ∘ f) (φ ∘ f)) (.assign f) (.ofEffect A φ)
  /-- Pull an effect through a store-preserving channel, including ancilla reset. -/
  | channel (f : Store → QuantumChannel H H) (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivTot (.ofEffect (A.channelPre f) φ) (.channel f) (.ofEffect A φ)
  /-- Apply the unitary rule on a defined register. -/
  | unitary {k : ℕ} (r : Store → Fin k → Cell)
      (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H)
      (φ : Store → Prop) (hr : ∀ σ, φ σ → Function.Injective (r σ)) :
      SourceDerivTot (.ofEffect (A.unitaryPre r U) φ) (.unitary r U) (.ofEffect A φ)
  /-- Sum every outcome and check the classical predicate after every write-back. -/
  | measureAll {m k : ℕ} (r : Store → Fin k → Cell)
      (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
      (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivTot (.ofEffect (A.measurePre r I upd)
        (fun σ => Function.Injective (r σ) ∧ ∀ i, φ (upd i σ))) (.measure r I upd) (.ofEffect A φ)
  /-- Transfer a quantum mask into the classical postcondition. -/
  | mask {P : CQAssertion Store H} {p : Command Store Cell H} {A : Assertion Store H}
      {φ χ : Store → Prop} :
      SourceDerivTot P p (.ofEffect (A.mask χ) φ) →
      SourceDerivTot P p (.ofEffect A fun σ => φ σ ∧ χ σ)
  /-- Compose source derivations at the intermediate source assertion. -/
  | seq {A B C : CQAssertion Store H} {p q : Command Store Cell H} :
      SourceDerivTot A p B → SourceDerivTot B q C → SourceDerivTot A (.seq p q) C
  /-- Preserve the invariant and prove strict integer decrease independently on the identity. -/
  | whileLoop {b : Store → Bool} {p : Command Store Cell H} {A : Assertion Store H}
      {φ : Store → Prop} (t : Store → ℤ) (hb : ∀ σ, φ σ → 0 ≤ t σ) :
      SourceDerivTot (.ofEffect A fun σ => φ σ ∧ b σ = true) p (.ofEffect A φ) →
      (∀ z, SourceDerivTot (.ofEffect Assertion.identity fun σ => φ σ ∧ b σ = true ∧ t σ = z)
        p (.ofEffect Assertion.identity fun σ => t σ < z)) →
      SourceDerivTot (.ofEffect A φ) (.whileDo b p) (.ofEffect A fun σ => φ σ ∧ b σ = false)
  /-- Convex1 merges mutually exclusive exits of a nonempty family at its largest weight. -/
  | convex1 {ι : Type} [Fintype ι] [Nonempty ι] (φ : Store → Prop) (χ : ι → Store → Prop)
      (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (w : ι → ℝ≥0)
      (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hx : ∀ σ i j, i ≠ j → χ i σ → ¬ χ j σ) :
      (∀ i, SourceDerivTot ((A i).under φ) p (B.under (χ i))) →
      SourceDerivTot ((SourceEffect.convex w hw A).under φ) p
        ((B.scaled (SourceEffect.maxWeight w) (SourceEffect.maxWeight_le_one w hw)).under
          fun σ => ∃ i, χ i σ)
  /-- Convex2 combines any finite family under common support. Every postoperand must be
  defined there, including those with zero weight. -/
  | convex2 {ι : Type} [Fintype ι] (φ χ : Store → Prop) (A B : ι → SourceEffect Store H)
      (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H)
      (hd : ∀ σ, χ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivTot ((A i).under φ) p ((B i).under χ)) →
      SourceDerivTot ((SourceEffect.convex w hw A).under φ) p ((SourceEffect.convex w hw B).under χ)
  /-- Accumulate a complete framed Kraus family under a common classical postcondition. -/
  | accum2 {ι : Type} [Fintype ι] (φ ψ : Store → Prop) (A B : ι → SourceEffect Store H)
      (K : Store → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1)
      (p : Command Store Cell H) (hp : ∀ i, p.KrausFrame (fun σ => K σ i))
      (hd : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivTot ((A i).under φ) p ((B i).under ψ)) →
      SourceDerivTot ((SourceEffect.kraus K (fun σ => (hK σ).le) A).under φ) p
        ((SourceEffect.kraus K (fun σ => (hK σ).le) B).under ψ)
  /-- Merge exclusive exits when a single contraction dominates each conjugated input state. -/
  | accum1 {ι : Type} [Fintype ι] (φ : Store → Prop) (ψ : ι → Store → Prop)
      (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (K : Store → ι → Operator H)
      (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1) (J : Store → Operator H)
      (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1) (p : Command Store Cell H)
      (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hd : ∀ σ i (ρ : Operator H), ρ.IsPositive →
        Superoperator.conjugate (K σ i) ρ ≤ Superoperator.conjugate (J σ) ρ) :
      (∀ i, SourceDerivTot ((A i).under φ) p (B.under (ψ i))) →
      SourceDerivTot ((SourceEffect.kraus K (fun σ => (hK σ).le) A).under φ) p
        ((SourceEffect.krausOne J hJ B).under fun σ => ∃ i, ψ i σ)
  /-- Strengthen and weaken using domain-aware source entailments before evaluation. -/
  | sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H} :
      A.Entails A' → SourceDerivTot A'.toCQAssertion p B'.toCQAssertion → B'.Entails B →
      SourceDerivTot A.toCQAssertion p B.toCQAssertion

/-- Consequence specialized to everywhere-defined operands. -/
theorem SourceDerivTot.conseq {A A' B B' : CQAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : SourceDerivTot A' p B') (hB : B'.Entails B) :
    SourceDerivTot A p B := by
  rw [← A.toCQAssertion_toSourceAssertion, ← B.toCQAssertion_toSourceAssertion]
  apply SourceDerivTot.sourceConseq ((A.toSourceAssertion_entails_iff A').mpr hA) _
    ((B'.toSourceAssertion_entails_iff B).mpr hB)
  simpa only [CQAssertion.toCQAssertion_toSourceAssertion] using h

/-- Interpret a source proof tree in the local total-correctness calculus. -/
theorem SourceDerivTot.toDerivTot {P Q : CQAssertion Store H} {p : Command Store Cell H}
    (h : SourceDerivTot P p Q) : DerivTot P.toAssn p Q.toAssn := by
  induction h with
  | skip A => exact .skip A.toAssn
  | cond b _ _ ih₁ ih₀ => simpa only [guard_onBranch] using DerivTot.cond (b := b) ih₁ ih₀
  | assign f A φ =>
    exact .assign f (A.mask φ)
  | channel f A φ =>
    apply DerivTot.conseq _ (.channel f (A.mask φ)) le_rfl
    apply mask_le_of (A := A.channelPre f) (φ := φ)
    intro σ hs
    simp [Assertion.channelPre, A.mask_of_pos hs]
  | unitary r U A φ hr =>
    apply DerivTot.conseq _ (.unitary r U (A.mask φ)) le_rfl
    apply mask_le_of (A := A.unitaryPre r U) (φ := φ)
    intro σ hs
    simp [Assertion.unitaryPre, hr σ hs, A.mask_of_pos hs]
  | measureAll r I upd A φ =>
    apply DerivTot.conseq _ (.measure r I upd (A.mask φ)) le_rfl
    apply mask_le_of
    intro σ ⟨hr, hc⟩
    change A.measurePre r I upd σ ≤ (A.mask φ).measurePre r I upd σ
    simp only [Assertion.measurePre, hr, dite_true]
    exact le_of_eq (congrArg (instrumentEffect (I σ hr))
      (funext fun i => (A.mask_of_pos (hc i)).symm))
  | @mask _ _ A φ χ _ ih =>
    change DerivTot _ _ (A.mask fun σ => φ σ ∧ χ σ)
    change DerivTot _ _ ((A.mask χ).mask φ) at ih
    simpa only [mask_and, and_comm] using ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | @whileLoop b p A φ t hb _ _ ihInv ihRank =>
    have hi : DerivTot ((A.mask φ).mand b) p (A.mask φ) := by
      rw [Assertion.mand, mask_and]
      exact ihInv
    have hl := DerivTot.whileLoopSource t hb hi (fun z => ihRank z)
    change DerivTot (A.mask φ) _ (A.mask fun σ => φ σ ∧ b σ = false)
    simpa only [Assertion.mandNot, mask_and] using hl
  | convex1 φ χ A B w hw p hx _ ih =>
    exact .conseq (SourceEffect.convex_pre_le w hw A φ) (.convex w hw ih)
      (SourceEffect.convex1_post_le w hw B χ hx)
  | convex2 φ χ A B w hw p hd _ ih =>
    rw [SourceEffect.convex_post_eq w hw B χ hd]
    exact .conseq (SourceEffect.convex_pre_le w hw A φ) (.convex w hw ih) le_rfl
  | accum2 φ ψ A B K hK p hp hd _ ih =>
    rw [SourceEffect.kraus_post_eq K _ B ψ (fun σ h i j => iff_of_true (hd σ h i) (hd σ h j))]
    exact .conseq (SourceEffect.kraus_pre_le K _ A φ) (.kraus K _ hp ih) le_rfl
  | accum1 φ ψ A B K hK J hJ p hp hx hd _ ih =>
    exact .conseq (SourceEffect.kraus_pre_le K _ A φ) (.kraus K _ hp ih)
      (SourceEffect.krausOne_post_le K _ B ψ J hJ hx hd)
  | sourceConseq h₁ _ h₂ ih => exact DerivTot.sourceConseq h₁ ih h₂

/-- Empty Convex2 gives the zero effect on both sides under arbitrary classical predicates. -/
theorem SourceDerivTot.convex2Empty (φ χ : Store → Prop) (p : Command Store Cell H) :
    SourceDerivTot (.ofEffect Assertion.zero φ) p (.ofEffect Assertion.zero χ) := by
  let A : Fin 0 → SourceEffect Store H := Fin.elim0
  let w : Fin 0 → ℝ≥0 := Fin.elim0
  have hw : ∑ i, w i ≤ 1 := by simp
  have h := SourceDerivTot.convex2 φ χ A A w hw p (fun _ _ i => i.elim0) (fun i => i.elim0)
  rwa [SourceEffect.convex_empty w hw A, SourceEffect.total_under, SourceEffect.total_under] at h

/-- Empty Convex2 can choose false classical support at exit. Consequence then permits
any postcondition for the zero input effect. -/
theorem SourceDerivTot.zeroPre (φ : Store → Prop) (p : Command Store Cell H)
    (B : CQAssertion Store H) : SourceDerivTot (.ofEffect Assertion.zero φ) p B :=
  .conseq (fun _ hs => ⟨hs, le_rfl⟩) (.convex2Empty φ (fun _ => False) p) (fun _ hs => hs.elim)

/-- Source proofs are sound for the masked classical–quantum assertions. -/
theorem SourceDerivTot.sound {P Q : CQAssertion Store H} {p : Command Store Cell H}
    (h : SourceDerivTot P p Q) : validTot P.toAssn p Q.toAssn := h.toDerivTot.sound

/-- Select outcomes by testing the store written by the measurement. The unselected
operands are masked to zero in the complete Born sum. -/
theorem SourceDerivTot.measureSelected {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
    (A : Assertion Store H) (φ keep : Store → Prop) :
    SourceDerivTot (.ofEffect ((A.mask keep).measurePre r I upd)
      (fun σ => Function.Injective (r σ) ∧ ∀ i, keep (upd i σ) → φ (upd i σ)))
      (.measure r I upd) (.ofEffect A φ) := by
  apply SourceDerivTot.conseq (fun _ h => ⟨h, le_rfl⟩)
    (.mask (.measureAll r I upd (A.mask keep) (fun σ => keep σ → φ σ)))
  exact fun _ h => ⟨h.1 h.2, le_rfl⟩

/-- Partial source proofs on evaluated operands, with an unranked loop and finite convex rules. -/
inductive SourceDerivPar : CQAssertion Store H → Command Store Cell H → CQAssertion Store H → Prop
  /-- Skipping preserves the entire source assertion. -/
  | skip (A : CQAssertion Store H) : SourceDerivPar A .skip A
  /-- Each branch may assume its guard value. -/
  | cond {A B : CQAssertion Store H} {p q : Command Store Cell H} (b : Store → Bool) :
      SourceDerivPar (A.onBranch b true) p B → SourceDerivPar (A.onBranch b false) q B →
      SourceDerivPar A (.ite b p q) B
  /-- Substitute into both the classical predicate and the quantum effect. -/
  | assign (f : Store → Store) (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivPar (.ofEffect (A ∘ f) (φ ∘ f)) (.assign f) (.ofEffect A φ)
  /-- Pull an effect through a store-preserving channel, including ancilla reset. -/
  | channel (f : Store → QuantumChannel H H) (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivPar (.ofEffect (A.channelPre f) φ) (.channel f) (.ofEffect A φ)
  /-- Apply the unitary rule on a defined register. -/
  | unitary {k : ℕ} (r : Store → Fin k → Cell)
      (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H)
      (φ : Store → Prop) (hr : ∀ σ, φ σ → Function.Injective (r σ)) :
      SourceDerivPar (.ofEffect (A.unitaryPre r U) φ) (.unitary r U) (.ofEffect A φ)
  /-- Sum every outcome and check the classical predicate after every write-back. -/
  | measureAll {m k : ℕ} (r : Store → Fin k → Cell)
      (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
      (A : Assertion Store H) (φ : Store → Prop) :
      SourceDerivPar (.ofEffect (A.measurePre r I upd)
        (fun σ => Function.Injective (r σ) ∧ ∀ i, φ (upd i σ))) (.measure r I upd) (.ofEffect A φ)
  /-- Transfer a quantum mask into the classical postcondition. -/
  | mask {P : CQAssertion Store H} {p : Command Store Cell H} {A : Assertion Store H}
      {φ χ : Store → Prop} :
      SourceDerivPar P p (.ofEffect (A.mask χ) φ) →
      SourceDerivPar P p (.ofEffect A fun σ => φ σ ∧ χ σ)
  /-- Compose source derivations at the intermediate source assertion. -/
  | seq {A B C : CQAssertion Store H} {p q : Command Store Cell H} :
      SourceDerivPar A p B → SourceDerivPar B q C → SourceDerivPar A (.seq p q) C
  /-- A guarded invariant suffices for the partial-correctness loop rule. -/
  | whileLoop {b : Store → Bool} {p : Command Store Cell H} {A : Assertion Store H}
      {φ : Store → Prop} :
      SourceDerivPar (.ofEffect A fun σ => φ σ ∧ b σ = true) p (.ofEffect A φ) →
      SourceDerivPar (.ofEffect A φ) (.whileDo b p) (.ofEffect A fun σ => φ σ ∧ b σ = false)
  /-- Convex1 merges mutually exclusive exits of a nonempty family at its largest weight. -/
  | convex1 {ι : Type} [Fintype ι] [Nonempty ι] (φ : Store → Prop) (χ : ι → Store → Prop)
      (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (w : ι → ℝ≥0)
      (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hx : ∀ σ i j, i ≠ j → χ i σ → ¬ χ j σ) :
      (∀ i, SourceDerivPar ((A i).under φ) p (B.under (χ i))) →
      SourceDerivPar ((SourceEffect.convex w hw A).under φ) p
        ((B.scaled (SourceEffect.maxWeight w) (SourceEffect.maxWeight_le_one w hw)).under
          fun σ => ∃ i, χ i σ)
  /-- Convex2 combines any finite family under common support. Every postoperand must be
  defined there, including those with zero weight. -/
  | convex2 {ι : Type} [Fintype ι] (φ χ : Store → Prop) (A B : ι → SourceEffect Store H)
      (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H)
      (hd : ∀ σ, χ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivPar ((A i).under φ) p ((B i).under χ)) →
      SourceDerivPar ((SourceEffect.convex w hw A).under φ) p ((SourceEffect.convex w hw B).under χ)
  /-- Accumulate a complete framed Kraus family under a common classical postcondition. -/
  | accum2 {ι : Type} [Fintype ι] (φ ψ : Store → Prop) (A B : ι → SourceEffect Store H)
      (K : Store → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1)
      (p : Command Store Cell H) (hp : ∀ i, p.KrausFrame (fun σ => K σ i))
      (hd : ∀ σ, ψ σ → ∀ i, (B i).defined σ) :
      (∀ i, SourceDerivPar ((A i).under φ) p ((B i).under ψ)) →
      SourceDerivPar ((SourceEffect.kraus K (fun σ => (hK σ).le) A).under φ) p
        ((SourceEffect.kraus K (fun σ => (hK σ).le) B).under ψ)
  /-- Merge exclusive exits when a single contraction dominates each conjugated input state. -/
  | accum1 {ι : Type} [Fintype ι] (φ : Store → Prop) (ψ : ι → Store → Prop)
      (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (K : Store → ι → Operator H)
      (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1) (J : Store → Operator H)
      (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1) (p : Command Store Cell H)
      (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
      (hd : ∀ σ i (ρ : Operator H), ρ.IsPositive →
        Superoperator.conjugate (K σ i) ρ ≤ Superoperator.conjugate (J σ) ρ) :
      (∀ i, SourceDerivPar ((A i).under φ) p (B.under (ψ i))) →
      SourceDerivPar ((SourceEffect.kraus K (fun σ => (hK σ).le) A).under φ) p
        ((SourceEffect.krausOne J hJ B).under fun σ => ∃ i, ψ i σ)
  /-- Strengthen and weaken using domain-aware source entailments before evaluation. -/
  | sourceConseq {A A' B' B : SourceAssertion Store H} {p : Command Store Cell H} :
      A.Entails A' → SourceDerivPar A'.toCQAssertion p B'.toCQAssertion → B'.Entails B →
      SourceDerivPar A.toCQAssertion p B.toCQAssertion

/-- Consequence specialized to everywhere-defined operands. -/
theorem SourceDerivPar.conseq {A A' B B' : CQAssertion Store H} {p : Command Store Cell H}
    (hA : A.Entails A') (h : SourceDerivPar A' p B') (hB : B'.Entails B) :
    SourceDerivPar A p B := by
  rw [← A.toCQAssertion_toSourceAssertion, ← B.toCQAssertion_toSourceAssertion]
  apply SourceDerivPar.sourceConseq ((A.toSourceAssertion_entails_iff A').mpr hA) _
    ((B'.toSourceAssertion_entails_iff B).mpr hB)
  simpa only [CQAssertion.toCQAssertion_toSourceAssertion] using h

/-- A total source proof supplies a partial source proof with the same assertions.
At a loop the partial proof uses the invariant premise. -/
theorem SourceDerivTot.toSourceDerivPar {A B : CQAssertion Store H} {p : Command Store Cell H}
    (d : SourceDerivTot A p B) : SourceDerivPar A p B := by
  induction d with
  | skip A => exact .skip A
  | cond b _ _ ih₁ ih₀ => exact .cond b ih₁ ih₀
  | assign f A φ => exact .assign f A φ
  | channel f A φ => exact .channel f A φ
  | unitary r U A φ hr => exact .unitary r U A φ hr
  | measureAll r I upd A φ => exact .measureAll r I upd A φ
  | mask _ ih => exact .mask ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | whileLoop _ _ _ _ ihInv _ => exact .whileLoop ihInv
  | convex1 φ χ A B w hw p hx _ ih => exact .convex1 φ χ A B w hw p hx ih
  | convex2 φ χ A B w hw p hd _ ih => exact .convex2 φ χ A B w hw p hd ih
  | accum2 φ ψ A B K hK p hp hd _ ih => exact .accum2 φ ψ A B K hK p hp hd ih
  | accum1 φ ψ A B K hK J hJ p hp hx hd _ ih => exact .accum1 φ ψ A B K hK J hJ p hp hx hd ih
  | sourceConseq hA _ hB ih => exact .sourceConseq hA ih hB

/-- Partial source proofs are sound for the masked assertions. The atomic rules have
the same preconditions as their total counterparts. -/
theorem SourceDerivPar.sound {P Q : CQAssertion Store H} {p : Command Store Cell H}
    (h : SourceDerivPar P p Q) : validPar P.toAssn p Q.toAssn := by
  induction h with
  | skip A => exact (validTot_skip A.toAssn).validPar
  | cond b _ _ ih₁ ih₀ => simpa only [guard_onBranch] using validPar_cond (b := b) ih₁ ih₀
  | assign f A φ => exact (SourceDerivTot.assign f A φ).sound.validPar
  | channel f A φ => exact (SourceDerivTot.channel f A φ).sound.validPar
  | unitary r U A φ hr => exact (SourceDerivTot.unitary r U A φ hr).sound.validPar
  | measureAll r I upd A φ => exact (SourceDerivTot.measureAll r I upd A φ).sound.validPar
  | @mask _ _ A φ χ _ ih =>
    change validPar _ _ (A.mask fun σ => φ σ ∧ χ σ)
    change validPar _ _ ((A.mask χ).mask φ) at ih
    simpa only [mask_and, and_comm] using ih
  | seq _ _ ih₁ ih₂ => exact validPar_seq ih₁ ih₂
  | @whileLoop b p A φ _ ih =>
    have hi : validPar ((A.mask φ).mand b) p (A.mask φ) := by
      rw [Assertion.mand, mask_and]
      exact ih
    change validPar (A.mask φ) _ (A.mask fun σ => φ σ ∧ b σ = false)
    simpa only [Assertion.mandNot, mask_and] using validPar_while hi
  | convex1 φ χ A B w hw p hx _ ih =>
    exact SourceEffect.validPar_convex1 φ χ A B w hw p hx ih
  | convex2 φ χ A B w hw p hd _ ih =>
    exact SourceEffect.validPar_convex2 φ χ A B w hw p hd ih
  | accum2 φ ψ A B K hK p hp hd _ ih =>
    exact SourceEffect.validPar_accum2 K A φ hK B ψ hp
      (fun σ h i j => iff_of_true (hd σ h i) (hd σ h j)) ih
  | accum1 φ ψ A B K hK J hJ p hp hx hd _ ih =>
    exact SourceEffect.validPar_accum1 K A φ hK B ψ hp J hJ hx hd ih
  | sourceConseq h₁ _ h₂ ih => exact validPar_sourceConseq h₁ ih h₂

/-- Empty Convex2 gives the zero effect on both sides under arbitrary classical predicates. -/
theorem SourceDerivPar.convex2Empty (φ χ : Store → Prop) (p : Command Store Cell H) :
    SourceDerivPar (.ofEffect Assertion.zero φ) p (.ofEffect Assertion.zero χ) := by
  let A : Fin 0 → SourceEffect Store H := Fin.elim0
  let w : Fin 0 → ℝ≥0 := Fin.elim0
  have hw : ∑ i, w i ≤ 1 := by simp
  have h := SourceDerivPar.convex2 φ χ A A w hw p (fun _ _ i => i.elim0) (fun i => i.elim0)
  rwa [SourceEffect.convex_empty w hw A, SourceEffect.total_under, SourceEffect.total_under] at h

/-- The empty combination also gives arbitrary postconditions in partial source logic. -/
theorem SourceDerivPar.zeroPre (φ : Store → Prop) (p : Command Store Cell H)
    (B : CQAssertion Store H) : SourceDerivPar (.ofEffect Assertion.zero φ) p B :=
  .conseq (fun _ hs => ⟨hs, le_rfl⟩) (.convex2Empty φ (fun _ => False) p) (fun _ hs => hs.elim)

end QuantumProgram
