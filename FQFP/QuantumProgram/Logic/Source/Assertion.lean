/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for source assertion domains, interpretation and entailment.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Assertion.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Assertion.CQAssertion

/-!
# Source assertions with explicit quantum definedness

A source assertion pairs its classical formula with a quantum operand. Source entailment
compares the two domains under the classical premise, before masking the effects for evaluation.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- A source quantum effect together with the stores where it is defined. -/
structure SourceEffect (Store : Type*) (H : Qudit) where
  /-- Definedness of the quantum predicate. -/
  defined : Store → Prop
  /-- The quantum observable, used on its domain. -/
  effect : Assertion Store H

namespace SourceEffect

variable {Store : Type*} {H : Qudit}

/-- An evaluated effect is defined at every store. -/
def total (A : Assertion Store H) : SourceEffect Store H := ⟨fun _ => True, A⟩

/-- Evaluate a source predicate on its domain under the indicated classical condition. -/
def under (A : SourceEffect Store H) (φ : Store → Prop) : CQAssertion Store H :=
  .ofEffect A.effect fun σ => φ σ ∧ A.defined σ

/-- Total operands recover the evaluated source assertion. -/
theorem total_under (A : Assertion Store H) (φ : Store → Prop) :
    (total A).under φ = .ofEffect A φ := by simp [under, total]

/-- Under the classical premise the domains agree, and the effects are ordered on that domain. -/
def QuantumEntails (φ : Store → Prop) (A B : SourceEffect Store H) : Prop :=
  ∀ σ, φ σ → (A.defined σ ↔ B.defined σ) ∧ (A.defined σ → A.effect σ ≤ B.effect σ)

end SourceEffect

/-- A classical formula paired with its domain-bearing quantum predicate. -/
structure SourceAssertion (Store : Type*) (H : Qudit) where
  /-- Classical premise, including at stores where the quantum operand is undefined. -/
  classical : Store → Prop
  /-- Quantum operand with its own domain of definition. -/
  quantum : SourceEffect Store H

variable {Store : Type*} {H : Qudit}

namespace SourceAssertion

/-- Evaluate the assertion on the intersection of its classical support and quantum domain. -/
def toCQAssertion (A : SourceAssertion Store H) : CQAssertion Store H :=
  A.quantum.under A.classical

/-- Mask the quantum effect for the operational semantics. -/
noncomputable def toAssn (A : SourceAssertion Store H) : Assertion Store H := A.toCQAssertion.toAssn

/-- Classical implication and quantum entailment under the antecedent's classical formula. -/
def Entails (A B : SourceAssertion Store H) : Prop :=
  (∀ σ, A.classical σ → B.classical σ) ∧ SourceEffect.QuantumEntails A.classical A.quantum B.quantum

/-- Every source assertion entails itself. -/
theorem Entails.refl (A : SourceAssertion Store H) : A.Entails A :=
  ⟨fun _ h => h, fun _ _ => ⟨Iff.rfl, fun _ => le_rfl⟩⟩

/-- Chain the domain equivalences and compare effects on the common domain. -/
theorem Entails.trans {A B C : SourceAssertion Store H} (h : A.Entails B) (h' : B.Entails C) :
    A.Entails C := by
  refine ⟨fun σ hA => h'.1 σ (h.1 σ hA), ?_⟩
  intro σ hA
  obtain ⟨hd, hq⟩ := h.2 σ hA
  obtain ⟨hd', hq'⟩ := h'.2 σ (h.1 σ hA)
  exact ⟨hd.trans hd', fun ha => (hq ha).trans (hq' (hd.mp ha))⟩

/-- Interpreting source entailment gives pointwise Löwner order of masked assertions. -/
theorem Entails.toAssn_le {A B : SourceAssertion Store H} (h : A.Entails B) :
    A.toAssn ≤ B.toAssn := by
  apply Assertion.mask_mono_on
  · intro σ ⟨hA, hd⟩
    exact ⟨h.1 σ hA, (h.2 σ hA).1.mp hd⟩
  · intro σ ⟨hA, hd⟩
    exact (h.2 σ hA).2 hd

/-- Substitute a store transformation into the formula, domain and effect together. -/
def subst (A : SourceAssertion Store H) (f : Store → Store) : SourceAssertion Store H :=
  ⟨A.classical ∘ f, ⟨A.quantum.defined ∘ f, A.quantum.effect ∘ f⟩⟩

/-- Substitution preserves source entailment. -/
theorem Entails.subst {A B : SourceAssertion Store H} (h : A.Entails B) (f : Store → Store) :
    (A.subst f).Entails (B.subst f) := ⟨fun σ => h.1 (f σ), fun σ => h.2 (f σ)⟩

/-- Evaluating a substituted assertion commutes with the store transformation. -/
theorem toAssn_subst (A : SourceAssertion Store H) (f : Store → Store) :
    (A.subst f).toAssn = A.toAssn ∘ f := rfl

/-- Equivalence of source assertions is mutual entailment. -/
def Eqv (A B : SourceAssertion Store H) : Prop := A.Entails B ∧ B.Entails A

/-- Equivalent assertions have equivalent classical conditions and agree on the common domain. -/
theorem eqv_iff (A B : SourceAssertion Store H) : A.Eqv B ↔
    (∀ σ, A.classical σ ↔ B.classical σ) ∧
      (∀ σ, A.classical σ → (A.quantum.defined σ ↔ B.quantum.defined σ) ∧
        (A.quantum.defined σ → A.quantum.effect σ = B.quantum.effect σ)) := by
  constructor
  · rintro ⟨hab, hba⟩
    refine ⟨fun σ => ⟨hab.1 σ, hba.1 σ⟩, ?_⟩
    intro σ hA
    obtain ⟨hd, hle⟩ := hab.2 σ hA
    exact ⟨hd, fun ha => le_antisymm (hle ha) ((hba.2 σ (hab.1 σ hA)).2 (hd.mp ha))⟩
  · rintro ⟨hc, hq⟩
    refine ⟨⟨fun σ => (hc σ).mp, ?_⟩, ⟨fun σ => (hc σ).mpr, ?_⟩⟩
    · intro σ hA
      obtain ⟨hd, he⟩ := hq σ hA
      exact ⟨hd, fun ha => (he ha).le⟩
    · intro σ hB
      obtain ⟨hd, he⟩ := hq σ ((hc σ).mpr hB)
      exact ⟨hd.symm, fun hb => (he (hd.mpr hb)).ge⟩

end SourceAssertion

/-- Regard an evaluated classical–quantum assertion as having an everywhere-defined operand. -/
def CQAssertion.toSourceAssertion (A : CQAssertion Store H) : SourceAssertion Store H :=
  ⟨A.cls, .total A.effect⟩

/-- Evaluating the total embedding recovers the original assertion. -/
theorem CQAssertion.toCQAssertion_toSourceAssertion (A : CQAssertion Store H) :
    A.toSourceAssertion.toCQAssertion = A := by
  rw [toSourceAssertion, SourceAssertion.toCQAssertion, SourceEffect.total_under]
  rfl

/-- Source consequence compares effects on the precondition's classical support. -/
def CQAssertion.Entails (A B : CQAssertion Store H) : Prop :=
  ∀ σ, A.cls σ → B.cls σ ∧ A.op σ ≤ B.op σ

/-- On total operands source entailment is precisely the evaluated entailment. -/
theorem CQAssertion.toSourceAssertion_entails_iff (A B : CQAssertion Store H) :
    A.toSourceAssertion.Entails B.toSourceAssertion ↔ A.Entails B := by
  constructor
  · intro h σ hA
    exact ⟨h.1 σ hA, (h.2 σ hA).2 trivial⟩
  · intro h
    exact ⟨fun σ hA => (h σ hA).1, fun σ hA => ⟨Iff.rfl, fun _ => (h σ hA).2⟩⟩

/-- Total source entailment gives pointwise order on evaluated assertions. -/
theorem CQAssertion.Entails.toAssn_le {A B : CQAssertion Store H} (h : A.Entails B) :
    A.toAssn ≤ B.toAssn := by
  simpa only [SourceAssertion.toAssn, toCQAssertion_toSourceAssertion] using
    ((A.toSourceAssertion_entails_iff B).mpr h).toAssn_le

end QuantumProgram
