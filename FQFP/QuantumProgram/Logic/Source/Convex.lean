/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for convex source rules and their derived forms.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Convex.lean
Qhl/Logic/Source/ConvexDerived.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Source.Assertion
public import FQFP.QuantumProgram.Logic.Assertion.Convex

/-!
# Finite convex combinations of source predicates

A source quantum operand carries its definedness predicate separately from its effect.
The classical predicate is supplied by the rule. Evaluating the pair in the local calculus
restricts support to stores satisfying both predicates, as in the upstream masked interpretation.
-/

@[expose] public section

open Qudit Finset
open scoped NNReal ComplexOrder

namespace QuantumProgram

namespace SourceEffect

variable {Store Cell ι : Type*} {H : Qudit} [Fintype ι]

/-- Strict source combination. Even a zero-weight child contributes its domain. -/
noncomputable def convex (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (A : ι → SourceEffect Store H) :
    SourceEffect Store H :=
  ⟨fun σ => ∀ i, (A i).defined σ, Assertion.convex w hw fun i => (A i).effect⟩

/-- Scaling preserves the domain of the common postpredicate. -/
noncomputable def scaled (B : SourceEffect Store H) (r : ℝ≥0) (hr : r ≤ 1) :
    SourceEffect Store H :=
  ⟨B.defined, B.effect.scaled r hr⟩

/-- Largest branch weight, with value zero on the empty index type. -/
noncomputable def maxWeight (w : ι → ℝ≥0) : ℝ≥0 := univ.sup w

/-- Every branch weight is bounded by the maximum. -/
theorem le_maxWeight (w : ι → ℝ≥0) (i : ι) : w i ≤ maxWeight w := le_sup (mem_univ i)

/-- With at least one branch, the maximum is attained. -/
theorem maxWeight_attained [Nonempty ι] (w : ι → ℝ≥0) : ∃ i, w i = maxWeight w := by
  obtain ⟨i, _, hi⟩ := exists_mem_eq_sup univ univ_nonempty w
  exact ⟨i, hi.symm⟩

/-- A subprobability family's maximum is at most one. -/
theorem maxWeight_le_one (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) : maxWeight w ≤ 1 :=
  Finset.sup_le fun i _ =>
    (single_le_sum (fun j _ => (show 0 ≤ w j from bot_le)) (mem_univ i)).trans hw

/-- On strict common support, masking before or after summation agrees. -/
private theorem convex_eq_at (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1)
    (A : ι → SourceEffect Store H) (φ : Store → Prop) (σ : Store)
    (h : φ σ ∧ ∀ i, (A i).defined σ) :
    (((convex w hw A).under φ).toAssn σ).val =
      (Assertion.convex w hw (fun i => ((A i).under φ).toAssn) σ).val := by
  rw [CQAssertion.toAssn_op_of_cls (q := (convex w hw A).under φ) h]
  change (∑ i, ((w i : ℝ) : ℂ) • ((A i).effect σ).val) = ∑ i, _
  exact sum_congr rfl fun i _ => congrArg (((w i : ℝ) : ℂ) • ·)
    (CQAssertion.toAssn_op_of_cls (q := (A i).under φ) ⟨h.1, h.2 i⟩).symm

/-- The strict input mask can discard stores even when a missing operand has weight zero. -/
theorem convex_pre_le (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (A : ι → SourceEffect Store H)
    (φ : Store → Prop) : ((convex w hw A).under φ).toAssn ≤
      Assertion.convex w hw (fun i => ((A i).under φ).toAssn) := by
  intro σ
  by_cases h : φ σ ∧ ∀ i, (A i).defined σ
  · exact (convex_eq_at w hw A φ σ h).le
  · change (_ : Operator H) ≤ _
    rw [CQAssertion.toAssn, Assertion.mask_of_neg _ (φ := ((convex w hw A).under φ).cls) h]
    exact (Assertion.convex w hw _ σ).2.1

/-- Convex2's post-domain premise restores equality of the two masked effects. -/
theorem convex_post_eq (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (B : ι → SourceEffect Store H)
    (χ : Store → Prop) (hd : ∀ σ, χ σ → ∀ i, (B i).defined σ) :
    ((convex w hw B).under χ).toAssn = Assertion.convex w hw (fun i => ((B i).under χ).toAssn) := by
  funext σ
  apply Subtype.ext
  by_cases h : χ σ
  · exact convex_eq_at w hw B χ σ ⟨h, hd σ h⟩
  · simp [CQAssertion.toAssn, CQAssertion.ofEffect, under, Assertion.mask,
      Assertion.convex, h]

/-- Convex1 bounds exclusive classical exits by the supremum of their weights, zero for
an empty family. -/
theorem convex1_post_le (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) (B : SourceEffect Store H)
    (χ : ι → Store → Prop) (hx : ∀ σ i j, i ≠ j → χ i σ → ¬ χ j σ) :
    Assertion.convex w hw (fun i => (B.under (χ i)).toAssn) ≤
      ((B.scaled (maxWeight w) (maxWeight_le_one w hw)).under (fun σ => ∃ i, χ i σ)).toAssn := by
  intro σ
  change (∑ i, ((w i : ℝ) : ℂ) • ((B.under (χ i)).toAssn σ).val) ≤ (_ : Operator H)
  by_cases hd : B.defined σ
  · by_cases he : ∃ i, χ i σ
    · obtain ⟨j, hj⟩ := he
      rw [sum_eq_single j]
      · simp [CQAssertion.toAssn, CQAssertion.ofEffect, CQAssertion.effect, under, Assertion.mask,
          scaled, Assertion.scaled_apply, hd, hj, show ∃ i, χ i σ from ⟨j, hj⟩]
        simpa using smul_le_smul_of_nonneg_right
          (Complex.real_le_real.mpr (show (w j : ℝ) ≤ maxWeight w from le_maxWeight w j))
          (B.effect σ).2.1
      · intro i _ hij
        simp [CQAssertion.toAssn, CQAssertion.ofEffect, under, Assertion.mask, hx σ j i hij.symm hj]
      · simp
    · have hn : ∀ i, ¬ χ i σ := fun i hi => he ⟨i, hi⟩
      simp [CQAssertion.toAssn, CQAssertion.ofEffect, under, Assertion.mask, hn]
  · simp [CQAssertion.toAssn, CQAssertion.ofEffect, under, Assertion.mask, scaled, hd]

/-- A convex combination indexed by the empty type is the total zero effect. -/
theorem convex_empty [IsEmpty ι] (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1)
    (A : ι → SourceEffect Store H) : convex w hw A = total Assertion.zero := by
  unfold convex total
  congr 1
  · funext σ
    simp
  · exact Assertion.convex_empty w hw _

/-- Convex1 for total validity with mutually exclusive classical exits. -/
theorem validTot_convex1 (φ : Store → Prop) (χ : ι → Store → Prop)
    (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hx : ∀ σ i j, i ≠ j → χ i σ → ¬ χ j σ)
    (h : ∀ i, validTot ((A i).under φ).toAssn p (B.under (χ i)).toAssn) :
    validTot ((convex w hw A).under φ).toAssn p
      ((B.scaled (maxWeight w) (maxWeight_le_one w hw)).under (fun σ => ∃ i, χ i σ)).toAssn :=
  validTot_conseq (convex_pre_le w hw A φ) (validTot_convex w hw h) (convex1_post_le w hw B χ hx)

/-- Convex2 for total validity, including the empty family. -/
theorem validTot_convex2 (φ χ : Store → Prop) (A B : ι → SourceEffect Store H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hd : ∀ σ, χ σ → ∀ i, (B i).defined σ)
    (h : ∀ i, validTot ((A i).under φ).toAssn p ((B i).under χ).toAssn) :
    validTot ((convex w hw A).under φ).toAssn p ((convex w hw B).under χ).toAssn := by
  rw [convex_post_eq w hw B χ hd]
  exact validTot_conseq (convex_pre_le w hw A φ) (validTot_convex w hw h) le_rfl

/-- Convex1 for partial validity with mutually exclusive classical exits. -/
theorem validPar_convex1 (φ : Store → Prop) (χ : ι → Store → Prop)
    (A : ι → SourceEffect Store H) (B : SourceEffect Store H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hx : ∀ σ i j, i ≠ j → χ i σ → ¬ χ j σ)
    (h : ∀ i, validPar ((A i).under φ).toAssn p (B.under (χ i)).toAssn) :
    validPar ((convex w hw A).under φ).toAssn p
      ((B.scaled (maxWeight w) (maxWeight_le_one w hw)).under (fun σ => ∃ i, χ i σ)).toAssn :=
  validPar_conseq (convex_pre_le w hw A φ) (validPar_convex w hw h) (convex1_post_le w hw B χ hx)

/-- Convex2 for partial validity, including the empty family. -/
theorem validPar_convex2 (φ χ : Store → Prop) (A B : ι → SourceEffect Store H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (p : Command Store Cell H) (hd : ∀ σ, χ σ → ∀ i, (B i).defined σ)
    (h : ∀ i, validPar ((A i).under φ).toAssn p ((B i).under χ).toAssn) :
    validPar ((convex w hw A).under φ).toAssn p ((convex w hw B).under χ).toAssn := by
  rw [convex_post_eq w hw B χ hd]
  exact validPar_conseq (convex_pre_le w hw A φ) (validPar_convex w hw h) le_rfl

end SourceEffect

end QuantumProgram
