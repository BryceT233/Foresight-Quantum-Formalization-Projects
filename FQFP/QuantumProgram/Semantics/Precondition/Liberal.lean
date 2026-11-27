/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Assertion.lean: validPar credits the residual mass.
Qhl/Logic/AlmostSure.lean: PostH_add_PostH_compl partitions the terminating mass.
Here these identities give an operator-valued weakest liberal precondition.

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Assertion.ExactExpectation
public import FQFP.QuantumProgram.Semantics.Precondition.While

/-!
# Weakest liberal preconditions

The liberal precondition credits every run except the part of the terminating output
measured by the complementary effect. It therefore includes both divergence and blocked
register operations in the partial-correctness yield.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Weakest precondition for partial correctness on weighted inputs. -/
noncomputable def wlp (p : Command Store Cell H) (B : Assertion Store H) : Assertion Store H :=
  (wp p B.compl).compl

/-- The liberal pre-expectation is the terminal post-expectation plus all residual mass. -/
theorem expectation_wlp (p : Command Store Cell H) (B : Assertion Store H) (s : CQState Store H) :
    ENNReal.ofReal (s.expectation (wlp p B s.store)) =
      (Configuration.mk (some p) s).PostH (fun σ => B σ) +
        (Configuration.mk (some p) s).nonterminatingMass := by
  let c := Configuration.mk (some p) s
  apply (ENNReal.add_right_inj (ENNReal.ofReal_ne_top
    (r := s.expectation (wp p B.compl s.store)))).mp
  rw [wlp, s.ofReal_expectation_add_compl, expectation_wp, ← add_assoc, add_comm (c.PostH _),
    c.PostH_add_PostH_compl B, c.terminatingMass_add_nonterminatingMass]

/-- A triple is partially valid exactly when its precondition lies below the liberal one. -/
theorem validPar_iff_le_wlp {A B : Assertion Store H} {p : Command Store Cell H} :
    validPar A p B ↔ A ≤ wlp p B := by
  simp only [validPar, ← expectation_wlp, Assertion.le_iff_expectation,
    ENNReal.ofReal_le_ofReal_iff (CQState.expectation_nonneg _ ((wlp p B).isPositive _))]

/-- Liberal preconditions preserve the order of postconditions. -/
theorem wlp_mono (p : Command Store Cell H) : Monotone (wlp p) :=
  fun _ _ h => Assertion.antitone_compl (wp_mono p (Assertion.antitone_compl h))

/-- The total precondition lies below the partial precondition on every input. -/
theorem wp_le_wlp (p : Command Store Cell H) (B : Assertion Store H) : wp p B ≤ wlp p B :=
  validPar_iff_le_wlp.mp (validTot_iff_le_wp.mpr le_rfl).validPar

/-- The identity postcondition credits every input, including when the command diverges. -/
@[simp] theorem wlp_identity (p : Command Store Cell H) :
    wlp p Assertion.identity = Assertion.identity :=
  le_antisymm (fun σ => (wlp p Assertion.identity σ).2.2)
    (validPar_iff_le_wlp.mp (validPar_identity p))

/-- Sequential composition pulls liberal preconditions back in reverse order. -/
@[simp] theorem wlp_seq (p q : Command Store Cell H) (B : Assertion Store H) :
    wlp (p.seq q) B = wlp p (wlp q B) := by simp [wlp]

/-- Skipping preserves the liberal postcondition. -/
@[simp] theorem wlp_skip (B : Assertion Store H) : wlp (.skip : Command Store Cell H) B = B := by
  simp [wlp]

/-- The liberal precondition of a finite iteration folds the body preconditions over the list. -/
theorem wlp_forList {ι : Type*} (l : List ι) (body : ι → Command Store Cell H)
    (B : Assertion Store H) : wlp (.forList l body) B = l.foldr (fun i => wlp (body i)) B := by
  induction l with
  | nil => exact wlp_skip B
  | cons i l ih => simp only [Command.forList_cons, wlp_seq, List.foldr_cons, ih]

/-- Assignment substitutes the new classical store. -/
@[simp] theorem wlp_assign (f : Store → Store) (B : Assertion Store H) :
    wlp (.assign f : Command Store Cell H) B = B ∘ f := by
  funext σ
  simp [wlp, Assertion.compl]

/-- A trace-preserving channel pulls liberal preconditions back through its dual. -/
@[simp] theorem wlp_channel (f : Store → QuantumChannel H H) (B : Assertion Store H) :
    wlp (.channel f : Command Store Cell H) B = B.channelPre f := by
  simp [wlp, Assertion.channelPre_compl]

/-- A unitary pulls back the postcondition on valid addresses and credits blocked inputs fully. -/
@[simp] theorem wlp_unitary {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (B : Assertion Store H) (σ : Store) :
    wlp (.unitary r U) B σ = open Classical in
      if h : Function.Injective (r σ) then channelEffect (U σ h).toChannel (B σ)
      else Assertion.identity σ := by
  classical
  apply Subtype.ext
  by_cases h : Function.Injective (r σ) <;>
    simp [wlp, Assertion.compl, Assertion.unitaryPre, h, channelEffect,
      QuantumChannel.pullbackEffect, QuantumChannel.dual_one, Assertion.identity]

/-- Valid measurements sum the outcome-dependent pullbacks. Blocked measurements get full credit. -/
@[simp] theorem wlp_measure {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) (B : Assertion Store H) (σ : Store) :
    wlp (.measure r I upd) B σ = open Classical in
      if h : Function.Injective (r σ) then instrumentEffect (I σ h) (fun i => B (upd i σ))
      else Assertion.identity σ := by
  classical
  apply Subtype.ext
  by_cases h : Function.Injective (r σ)
  · simp only [wlp, wp_measure, Assertion.compl, Assertion.measurePre, dite_eq_left h,
      instrumentEffect, map_sub, Finset.sum_sub_distrib]
    rw [show (∑ i, ((I σ h).branchCPMap i).dual.toSuperoperator 1) = 1 from (I σ h).toPOVM.sum_op,
      sub_sub_cancel]
  · simp [wlp, Assertion.compl, Assertion.measurePre, h, Assertion.identity]

/-- A conditional selects the branch at the input store. -/
@[simp] theorem wlp_ite (b : Store → Bool) (p q : Command Store Cell H) (B : Assertion Store H)
    (σ : Store) : wlp (.ite b p q) B σ = if b σ then wlp p B σ else wlp q B σ := by
  cases hb : b σ <;> simp [wlp, Assertion.compl, wp_ite, hb]

/-- Unfold a liberal loop precondition at the current guard. -/
theorem wlp_whileDo (b : Store → Bool) (p : Command Store Cell H) (B : Assertion Store H)
    (σ : Store) :
    wlp (.whileDo b p) B σ = if b σ then wlp p (wlp (.whileDo b p) B) σ else B σ := by
  simp only [wlp, Assertion.compl_compl]
  cases hb : b σ <;> simp [Assertion.compl, wp_whileDo b p B.compl σ, hb]

/-- The liberal loop precondition is the greatest assertion preserved by one guard test. -/
theorem isGreatest_whileWlp (b : Store → Bool) (p : Command Store Cell H) (B : Assertion Store H) :
    IsGreatest {X : Assertion Store H | X ≤ fun σ => if b σ then wlp p X σ else B σ}
      (wlp (.whileDo b p) B) := by
  refine ⟨fun σ => (wlp_whileDo b p B σ).le, fun X hX => ?_⟩
  have h : whileWpStep b p B.compl X.compl ≤ X.compl := by
    intro σ
    have hx := sub_le_sub_left (show (X σ : Operator H) ≤ _ from hX σ) 1
    change (whileWpStep b p B.compl X.compl σ : Operator H) ≤ 1 - (X σ : Operator H)
    cases hb : b σ <;> simpa [whileWpStep, wlp, Assertion.compl, hb] using hx
  change X ≤ (wp (.whileDo b p) B.compl).compl
  simpa only [Assertion.compl_compl] using
    Assertion.antitone_compl ((isLeast_whileWpStep b p B.compl).2 h)

end QuantumProgram
