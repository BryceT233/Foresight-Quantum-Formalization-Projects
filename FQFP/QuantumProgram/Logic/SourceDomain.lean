/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for accumulation on a preserved domain.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/AccumulationDomain.lean (restricting total and partial validity)
Qhl/Logic/Source/Rules.lean (Accum1 and Accum2 with preserved operand domains)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.SourceRules

/-!
# Restriction to a preserved operand domain

Split the identity Kraus family according to a classical predicate. The active branch carries the
given triple and the complementary branch carries zero on both sides. This gives the domain
variants of both accumulation rules by restriction of their conclusions.
-/

@[expose] public section

open Qudit Finset

namespace QuantumProgram

variable {S Cell : Type*} {H : Qudit}

/-- Restrict definedness while retaining the operand's effect and the separate classical formula. -/
def SourceEffect.onDomain (A : SourceEffect S H) (d : S → Prop) : SourceEffect S H :=
  ⟨fun σ => A.defined σ ∧ d σ, A.effect⟩

/-- A source domain restriction masks the already interpreted classical–quantum assertion. -/
theorem SourceEffect.toAssn_under_onDomain (A : SourceEffect S H) (φ d : S → Prop) :
    ((A.onDomain d).under φ).toAssn = (A.under φ).toAssn.mask d := by
  funext σ
  change A.effect.mask (fun τ => φ τ ∧ A.defined τ ∧ d τ) σ =
    ((A.effect.mask fun τ => φ τ ∧ A.defined τ).mask d) σ
  simp only [Assertion.mask]
  split_ifs <;> grind

private noncomputable def selector (d : S → Prop) (σ : S) (b : Bool) : Operator H :=
  open Classical in if decide (d σ) = b then 1 else 0

private theorem selector_complete (d : S → Prop) (σ : S) :
    ∑ b, (selector (H := H) d σ b).adjoint ∘ₗ selector d σ b = 1 := by
  by_cases h : d σ <;> simp [selector, h, Module.End.one_eq_id]

private theorem selector_commutes (d : S → Prop) (σ : S) (b : Bool) (F : Superoperator H H) :
    Function.Commute F (Superoperator.conjugate (selector d σ b)) := by
  intro ρ
  classical
  by_cases h : decide (d σ) = b <;>
    simp [selector, h, Superoperator.conjugate_apply, Module.End.one_eq_id]

private theorem selector_frame (d : S → Prop) {p : Command S Cell H} (hp : p.PreservesParameters d)
    (b : Bool) : p.KrausFrame (fun σ => selector d σ b) := by
  induction p with
  | skip => trivial
  | assign f => exact fun σ => congrArg (fun v : Prop => selector id v b) (hp σ)
  | channel f => exact fun σ => selector_commutes d σ b _
  | unitary r U => exact fun σ _ => selector_commutes d σ b _
  | measure r I upd =>
    exact ⟨fun σ _ _ => selector_commutes d σ b _,
      fun i σ => congrArg (fun v : Prop => selector id v b) (hp i σ)⟩
  | seq _ _ ih₁ ih₂ | ite _ _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
  | whileDo _ _ ih => exact ih hp

private def active (A : Assertion S H) (b : Bool) : Assertion S H :=
  if b then A else Assertion.zero

private theorem selector_mask (A : Assertion S H) (d : S → Prop) :
    Assertion.kraus (selector d) (fun σ => (selector_complete d σ).le) (active A) = A.mask d := by
  funext σ
  apply Subtype.ext
  by_cases h : d σ <;>
    simp [Assertion.kraus, active, selector, h, Assertion.mask, Assertion.zero,
      Superoperator.conjugate_apply, Module.End.one_eq_id]

/-- Restrict a total triple to a predicate preserved by every classical write. -/
theorem validTot.mask_of_preserves {A B : Assertion S H} {p : Command S Cell H}
    (h : validTot A p B) (d : S → Prop) (hp : p.PreservesParameters d) :
    validTot (A.mask d) p (B.mask d) := by
  rw [← selector_mask A, ← selector_mask B]
  apply validTot_kraus _ _ (selector_frame d hp)
  intro b
  cases b with
  | false => exact (DerivTot.zeroPre p Assertion.zero).sound
  | true => exact h

/-- Partial correctness on a preserved domain shares residual mass with the inactive branch. -/
theorem validPar.mask_of_preserves {A B : Assertion S H} {p : Command S Cell H}
    (h : validPar A p B) (d : S → Prop) (hp : p.PreservesParameters d) :
    validPar (A.mask d) p (B.mask d) := by
  rw [← selector_mask A, ← selector_mask B]
  apply validPar_kraus _ (selector_complete d) (selector_frame d hp)
  intro b
  cases b with
  | false => exact (DerivTot.zeroPre p Assertion.zero).sound.validPar
  | true => exact h

private theorem selector_under (A : Assertion S H) (φ d : S → Prop) :
    ((SourceEffect.kraus (selector d) (fun σ => (selector_complete d σ).le)
      (fun b => SourceEffect.total (active A b))).under φ) = .ofEffect (A.mask d) φ := by
  simp [SourceEffect.kraus, SourceEffect.under, SourceEffect.total, selector_mask]

private theorem restrict_pre (A : SourceEffect S H) (φ d : S → Prop) :
    ((A.onDomain d).under φ).Entails (.ofEffect (A.effect.mask d) ((A.under φ).cls)) := by
  intro σ h
  exact ⟨⟨h.1, h.2.1⟩, le_of_eq (congrArg Subtype.val (A.effect.mask_of_pos h.2.2)).symm⟩

private theorem restrict_post (B : SourceEffect S H) (ψ d : S → Prop) :
    (CQAssertion.ofEffect B.effect (fun σ => (B.under ψ).cls σ ∧ d σ)).Entails
      ((B.onDomain d).under ψ) :=
  fun _ h => ⟨⟨h.1.1, h.1.2, h.2⟩, le_rfl⟩

/-- Restrict a total source proof, including either accumulation rule, to a preserved domain. -/
theorem SourceDerivTot.onDomain {A B : SourceEffect S H} {φ ψ : S → Prop} {p : Command S Cell H}
    (h : SourceDerivTot (A.under φ) p (B.under ψ)) (d : S → Prop) (hp : p.PreservesParameters d) :
    SourceDerivTot ((A.onDomain d).under φ) p ((B.onDomain d).under ψ) := by
  let pre := (A.under φ).cls
  let post := (B.under ψ).cls
  have hf := accum2 pre post (fun b => SourceEffect.total (active A.effect b))
    (fun b => SourceEffect.total (active B.effect b)) (selector d) (selector_complete d) p
    (selector_frame d hp) (fun _ _ _ => trivial)
  have hm : SourceDerivTot (.ofEffect (A.effect.mask d) pre) p
      (.ofEffect (B.effect.mask d) post) := by
    rw [← selector_under A.effect pre, ← selector_under B.effect post]
    apply hf
    intro b
    rw [SourceEffect.total_under, SourceEffect.total_under]
    cases b with
    | false => exact zeroPre pre p _
    | true => exact h
  exact conseq (restrict_pre A φ d) (mask hm) (restrict_post B ψ d)

/-- Restrict a partial source proof, including either accumulation rule, to a preserved domain. -/
theorem SourceDerivPar.onDomain {A B : SourceEffect S H} {φ ψ : S → Prop} {p : Command S Cell H}
    (h : SourceDerivPar (A.under φ) p (B.under ψ)) (d : S → Prop) (hp : p.PreservesParameters d) :
    SourceDerivPar ((A.onDomain d).under φ) p ((B.onDomain d).under ψ) := by
  let pre := (A.under φ).cls
  let post := (B.under ψ).cls
  have hf := accum2 pre post (fun b => SourceEffect.total (active A.effect b))
    (fun b => SourceEffect.total (active B.effect b)) (selector d) (selector_complete d) p
    (selector_frame d hp) (fun _ _ _ => trivial)
  have hm : SourceDerivPar (.ofEffect (A.effect.mask d) pre) p
      (.ofEffect (B.effect.mask d) post) := by
    rw [← selector_under A.effect pre, ← selector_under B.effect post]
    apply hf
    intro b
    rw [SourceEffect.total_under, SourceEffect.total_under]
    cases b with
    | false => exact zeroPre pre p _
    | true => exact h
  exact conseq (restrict_pre A φ d) (mask hm) (restrict_post B ψ d)

end QuantumProgram
