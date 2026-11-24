/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for strict Kraus domains and common-condition accumulation.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Kraus.lean (definedness of a Kraus combination)
Qhl/Logic/Source/KrausDomain.lean (mask bounds and equality on common domains)
Qhl/Logic/Source/Accumulation.lean (total and partial Accum2 validity)
Qhl/Logic/Source/AccumulationOneOrder.lean (exclusive exits and state-side domination)
Qhl/Logic/Source/AccumulationOne.lean (total and partial Accum1 validity)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Kraus
public import FQFP.QuantumProgram.Logic.SourceAssertion

/-!
# Kraus combinations of source predicates

Every operand contributes its domain, including one with a zero Kraus operator. At the
postcondition, agreement of the domains on classical support permits masking each branch before
summing its pulled-back effect.
-/

@[expose] public section

open Qudit Finset
open scoped ComplexOrder

namespace QuantumProgram.SourceEffect

variable {S Cell ι : Type*} {H : Qudit} [Fintype ι]

/-- A finite Kraus combination on the intersection of all operand domains. -/
noncomputable def kraus (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) (A : ι → SourceEffect S H) : SourceEffect S H :=
  ⟨fun σ => ∀ i, (A i).defined σ, Assertion.kraus K hK fun i => (A i).effect⟩

variable (K : S → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1)
    (A : ι → SourceEffect S H) (φ : S → Prop)

private theorem kraus_eq_at (σ : S) (h : φ σ ∧ ∀ i, (A i).defined σ) :
    (((kraus K hK A).under φ).toAssn σ).val =
      (Assertion.kraus K hK (fun i => ((A i).under φ).toAssn) σ).val := by
  rw [CQAssertion.toAssn_op_of_cls (q := (kraus K hK A).under φ) h]
  apply sum_congr rfl
  intro i _
  exact congrArg (Superoperator.conjugate (K σ i).adjoint)
    (CQAssertion.toAssn_op_of_cls (q := (A i).under φ) ⟨h.1, h.2 i⟩).symm

/-- A strict source precondition is bounded by the combination of individually masked effects. -/
theorem kraus_pre_le : ((kraus K hK A).under φ).toAssn ≤
    Assertion.kraus K hK (fun i => ((A i).under φ).toAssn) := by
  intro σ
  by_cases h : φ σ ∧ ∀ i, (A i).defined σ
  · exact (kraus_eq_at K hK A φ σ h).le
  · change (_ : Operator H) ≤ _
    rw [CQAssertion.toAssn, Assertion.mask_of_neg _ (φ := ((kraus K hK A).under φ).cls) h]
    exact (Assertion.kraus K hK _ σ).2.1

/-- On common support, pairwise domain agreement permits independent masking of the children. -/
theorem kraus_post_eq (hd : ∀ σ, φ σ → ∀ i j, (A i).defined σ ↔ (A j).defined σ) :
    ((kraus K hK A).under φ).toAssn =
      Assertion.kraus K hK (fun i => ((A i).under φ).toAssn) := by
  funext σ
  apply Subtype.ext
  by_cases h : φ σ ∧ ∀ i, (A i).defined σ
  · exact kraus_eq_at K hK A φ σ h
  · have hi (i : ι) : ¬ (φ σ ∧ (A i).defined σ) :=
      fun hx => h ⟨hx.1, fun j => (hd σ hx.1 i j).mp hx.2⟩
    rw [CQAssertion.toAssn, Assertion.mask_of_neg _ (φ := ((kraus K hK A).under φ).cls) h]
    simp [Assertion.kraus, CQAssertion.toAssn, under, CQAssertion.ofEffect, Assertion.mask, hi]

/-- Total correctness of Kraus accumulation under a common classical postcondition. -/
theorem validTot_accum2 (B : ι → SourceEffect S H) (ψ : S → Prop) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i))
    (hd : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (h : ∀ i, validTot ((A i).under φ).toAssn p ((B i).under ψ).toAssn) :
    validTot ((kraus K hK A).under φ).toAssn p ((kraus K hK B).under ψ).toAssn := by
  rw [kraus_post_eq K hK B ψ hd]
  exact validTot_conseq (kraus_pre_le K hK A φ) (validTot_kraus K hK hp h) le_rfl

variable (hN : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1)

/-- Partial correctness of normalized Kraus accumulation, with strict source domains. -/
theorem validPar_accum2 (B : ι → SourceEffect S H) (ψ : S → Prop) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i))
    (hd : ∀ σ, ψ σ → ∀ i j, (B i).defined σ ↔ (B j).defined σ)
    (h : ∀ i, validPar ((A i).under φ).toAssn p ((B i).under ψ).toAssn) :
    validPar ((kraus K (fun σ => (hN σ).le) A).under φ).toAssn p
      ((kraus K (fun σ => (hN σ).le) B).under ψ).toAssn := by
  rw [kraus_post_eq K _ B ψ hd]
  exact validPar_conseq (kraus_pre_le K _ A φ) (validPar_kraus K hN hp h) le_rfl

/-- The single output operator of an exclusive accumulation retains the operand's domain. -/
noncomputable def krausOne (J : S → Operator H) (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1)
    (B : SourceEffect S H) : SourceEffect S H :=
  ⟨B.defined, Assertion.kraus (fun σ (_ : Unit) => J σ) (fun σ => by simpa using hJ σ)
    (fun _ => B.effect)⟩

private theorem adjoint_conjugate_le {k j B : Operator H} (hB : B.IsPositive)
    (h : ∀ ρ : Operator H, ρ.IsPositive →
      Superoperator.conjugate k ρ ≤ Superoperator.conjugate j ρ) :
    Superoperator.conjugate k.adjoint B ≤ Superoperator.conjugate j.adjoint B := by
  have hs (f : Operator H) :=
    ((Superoperator.isCompletelyPositive_conjugate f.adjoint).isPositive B hB).isSymmetric
  apply LinearMap.le_def.mpr
  refine (LinearMap.isPositive_iff _).mpr ⟨(hs j).sub (hs k), fun x => ?_⟩
  have ht := hB.trace_mul_nonneg (LinearMap.le_def.mp (h (Operator.outer x x)
    (Operator.isPositive_outer x)))
  rw [mul_sub, map_sub, sub_nonneg] at ht
  change (B * Superoperator.conjugate k (Operator.outer x x)).trace ≤
    (B * Superoperator.conjugate j (Operator.outer x x)).trace at ht
  rw [← Superoperator.trace_conjugate_adjoint,
    ← Superoperator.trace_conjugate_adjoint, Operator.trace_mul_outer, Operator.trace_mul_outer,
    ← hs k x x, ← hs j x x] at ht
  simpa only [LinearMap.sub_apply, inner_sub_left, sub_nonneg] using ht

/-- At an exclusive exit, state-side domination bounds the pulled-back common effect by
the singleton output. The dominating operator need not frame the program. -/
theorem krausOne_post_le (B : SourceEffect S H) (ψ : ι → S → Prop)
    (J : S → Operator H) (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1)
    (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hd : ∀ σ i (ρ : Operator H), ρ.IsPositive →
      Superoperator.conjugate (K σ i) ρ ≤ Superoperator.conjugate (J σ) ρ) :
    Assertion.kraus K hK (fun i => (B.under (ψ i)).toAssn) ≤
      ((krausOne J hJ B).under fun σ => ∃ i, ψ i σ).toAssn := by
  intro σ
  change (∑ i, Superoperator.conjugate (K σ i).adjoint ((B.under (ψ i)).toAssn σ)) ≤
    (_ : Operator H)
  by_cases ha : ∃ i, ψ i σ ∧ B.defined σ
  · obtain ⟨j, hj, hb⟩ := ha
    rw [sum_eq_single j]
    · simp only [CQAssertion.toAssn_op_of_cls (q := B.under (ψ j)) ⟨hj, hb⟩,
        CQAssertion.toAssn_op_of_cls (q := (krausOne J hJ B).under (fun τ => ∃ i, ψ i τ))
          (σ := σ) ⟨⟨j, hj⟩, hb⟩]
      simpa only [under, CQAssertion.ofEffect, krausOne, Assertion.kraus, Fintype.sum_unique] using
        adjoint_conjugate_le (B.effect.isPositive σ) (hd σ j)
    · intro i _ hij
      simp [CQAssertion.toAssn, under, CQAssertion.ofEffect, Assertion.mask, hx σ j i hij.symm hj]
    · simp
  · have hz (i : ι) : ¬ (ψ i σ ∧ B.defined σ) := fun h => ha ⟨i, h⟩
    have hzero (i : ι) : ((B.under (ψ i)).toAssn σ : Operator H) = 0 :=
      Assertion.mask_of_neg _ (φ := (B.under (ψ i)).cls) (hz i)
    simpa only [hzero, map_zero, sum_const_zero] using
      (((krausOne J hJ B).under fun τ => ∃ i, ψ i τ).toAssn σ).2.1

/-- Total Accum1 under the state-side domination condition and exclusive exit predicates. -/
theorem validTot_accum1 (B : SourceEffect S H) (ψ : ι → S → Prop) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) (J : S → Operator H)
    (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1) (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hd : ∀ σ i (ρ : Operator H), ρ.IsPositive →
      Superoperator.conjugate (K σ i) ρ ≤ Superoperator.conjugate (J σ) ρ)
    (h : ∀ i, validTot ((A i).under φ).toAssn p (B.under (ψ i)).toAssn) :
    validTot ((kraus K hK A).under φ).toAssn p
      ((krausOne J hJ B).under fun σ => ∃ i, ψ i σ).toAssn :=
  validTot_conseq (kraus_pre_le K hK A φ) (validTot_kraus K hK hp h)
    (krausOne_post_le K hK B ψ J hJ hx hd)

/-- Partial Accum1 uses completeness to share the residual mass among all child triples. -/
theorem validPar_accum1 (B : SourceEffect S H) (ψ : ι → S → Prop) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) (J : S → Operator H)
    (hJ : ∀ σ, (J σ).adjoint ∘ₗ J σ ≤ 1) (hx : ∀ σ i j, i ≠ j → ψ i σ → ¬ ψ j σ)
    (hd : ∀ σ i (ρ : Operator H), ρ.IsPositive →
      Superoperator.conjugate (K σ i) ρ ≤ Superoperator.conjugate (J σ) ρ)
    (h : ∀ i, validPar ((A i).under φ).toAssn p (B.under (ψ i)).toAssn) :
    validPar ((kraus K (fun σ => (hN σ).le) A).under φ).toAssn p
      ((krausOne J hJ B).under fun σ => ∃ i, ψ i σ).toAssn :=
  validPar_conseq (kraus_pre_le K _ A φ) (validPar_kraus K hN hp h)
    (krausOne_post_le K _ B ψ J hJ hx hd)

end QuantumProgram.SourceEffect
