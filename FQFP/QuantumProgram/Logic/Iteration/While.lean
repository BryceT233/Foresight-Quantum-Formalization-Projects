/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for masked assertions and the loop soundness rules.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Assertion.lean
Qhl/Logic/Soundness.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.SeqDecomp

/-!
# Partial and total correctness of a guarded loop

An invariant preserved by the body on guarded inputs holds on loop exit with the guard false.
Partial correctness follows by induction on the execution horizon. Total correctness
uses a natural-valued rank and the post-expectation at each handover from the body.
The source rule combines invariant preservation with a separate integer-rank decrease test.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- A true guard hands control to the body followed by the same loop. -/
theorem next_whileDo_of_true {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = true) :
    (Configuration.mk (some (.whileDo b p)) s).next =
      [(Configuration.mk (some p) s).seqWith (.whileDo b p)] := by
  simp [Configuration.next, Command.step, Configuration.seqWith, hb]

/-- A false guard terminates the loop in the current state. -/
theorem next_whileDo_of_false {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = false) :
    (Configuration.mk (some (.whileDo b p)) s).next = [⟨none, s⟩] := by
  simp [Configuration.next, Command.step, hb]

/-- With a false guard, the loop evaluates the post-observable in the current state. -/
theorem Configuration.PostH_whileDo_of_false {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = false) (A : Store → Operator H) :
    (Configuration.mk (some (.whileDo b p)) s).PostH A =
      ENNReal.ofReal (s.expectation (A s.store)) :=
  PostH_of_step_terminal (next_whileDo_of_false p hb) A

/-- With a true guard, each terminal occurrence of the body contributes the remaining loop's
post-expectation. -/
theorem Configuration.PostH_whileDo_of_true {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = true) {A : Store → Operator H}
    (hA : ∀ σ, (A σ).IsPositive) :
    (Configuration.mk (some (.whileDo b p)) s).PostH A =
      ∑' j, (Configuration.mk (some p) s).terminalWeightAt j
        (fun t => (Configuration.mk (some (.whileDo b p)) t).PostH A) := by
  rw [PostH_singleton (next_whileDo_of_true p hb), PostH_seqWith _ _ hA]

/-- A loop preserves its invariant until the guard fails (QHL⁺ partial-correctness loop rule). -/
theorem validPar_while {b : Store → Bool} {J : Assertion Store H} {p : Command Store Cell H}
    (h : validPar (J.mand b) p J) : validPar J (.whileDo b p) (J.mandNot b) := by
  rw [validPar_iff_forall_le_Val] at h ⊢
  have bound (s : CQState Store H) : ENNReal.ofReal (s.expectation (J s.store)) ≤ s.mass :=
    (ENNReal.ofReal_le_ofReal ((s.expectation_mono (J s.store).2.2).trans_eq
      s.expectation_one)).trans_eq ENNReal.ofReal_coe_nnreal
  intro s N
  induction N using Nat.strong_induction_on generalizing s with
  | _ N ih =>
    cases N with
    | zero => rw [Configuration.Val_zero]; exact bound s
    | succ n =>
      cases hb : b s.store with
      | false =>
        rw [Configuration.Val_succ_singleton (next_whileDo_of_false p hb) rfl]
        cases n with
        | zero => rw [Configuration.Val_zero]; exact bound s
        | succ n =>
          rw [Configuration.Val_succ_terminal, J.mandNot_of_false hb]
      | true =>
        let c := Configuration.mk (some p) s
        rw [Configuration.Val_succ_singleton (next_whileDo_of_true p hb) rfl,
          Configuration.Val_seqWith]
        have prem := h s n
        rw [J.mand_of_true hb] at prem
        apply prem.trans
        refine add_le_add ?_ le_rfl
        apply Finset.sum_le_sum
        intro j _
        exact c.terminalWeightAt_mono j (fun t => ih (n - j) (by lia) t)

/-- Total correctness of a loop whose body establishes the invariant masked to strictly smaller
ranks from guarded inputs of each rank. -/
theorem validTot_while {b : Store → Bool} {J : Assertion Store H} {p : Command Store Cell H}
    (t : Store → ℕ) (h : ∀ n, validTot ((J.mand b).mask fun σ => t σ = n) p
      (J.mask fun σ => t σ < n)) : validTot J (.whileDo b p) (J.mandNot b) := by
  intro s
  induction hn : t s.store using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    cases hb : b s.store with
    | false =>
      rw [Configuration.PostH_whileDo_of_false p hb, J.mandNot_of_false hb]
    | true =>
      rw [Configuration.PostH_whileDo_of_true p hb (J.mandNot b).isPositive]
      have prem := h n s
      rw [(J.mand b).mask_of_pos (φ := fun σ => t σ = n) hn, J.mand_of_true hb] at prem
      apply prem.trans
      let c := Configuration.mk (some p) s
      rw [c.PostH_eq_tsum_terminalWeightAt (J.mask fun σ => t σ < n).isPositive]
      refine tsum_le_tsum fun j => c.terminalWeightAt_mono j fun u => ?_
      by_cases hu : t u.store < n
      · simpa only [J.mask_of_pos (φ := fun σ => t σ < n) hu] using ih (t u.store) hu u rfl
      · simp [J.mask_of_neg (φ := fun σ => t σ < n) hu, CQState.expectation_zero]

/-- The source total-correctness loop rule with an integer rank bounded below by zero on the
invariant's classical support. The body preserves the invariant, and its identity-effect triple
accounts for the entire input trace on outputs of strictly smaller rank. -/
theorem validTot_while_source {b : Store → Bool} {A : Assertion Store H} {φ : Store → Prop}
    {p : Command Store Cell H} (t : Store → ℤ) (hbound : ∀ σ, φ σ → 0 ≤ t σ)
    (hInv : validTot ((A.mask φ).mand b) p (A.mask φ))
    (hRank : ∀ z : ℤ, validTot (Assertion.identity.mask fun σ => φ σ ∧ b σ = true ∧ t σ = z)
      p (Assertion.identity.mask fun σ => t σ < z)) :
    validTot (A.mask φ) (.whileDo b p) ((A.mask φ).mandNot b) := by
  apply validTot_while (fun σ => (t σ).toNat)
  intro n s
  let J := A.mask φ
  by_cases hn : (t s.store).toNat = n
  case neg =>
    simp [Assertion.mask_of_neg _ (φ := fun σ => (t σ).toNat = n) hn, CQState.expectation_zero]
  rw [(J.mand b).mask_of_pos (φ := fun σ => (t σ).toNat = n) hn]
  cases hb : b s.store with
  | false => simp [J.mand_of_false hb, CQState.expectation_zero]
  | true =>
    rw [J.mand_of_true hb]
    by_cases hs : φ s.store
    case neg => simp [J, A.mask_of_neg hs, CQState.expectation_zero]
    let c := Configuration.mk (some p) s
    have hr := hRank (t s.store) s
    rw [Assertion.mask_of_pos _ (φ := fun σ => φ σ ∧ b σ = true ∧ t σ = t s.store)
      ⟨hs, hb, rfl⟩] at hr
    change ENNReal.ofReal (s.expectation 1) ≤ _ at hr
    rw [CQState.expectation_one, ENNReal.ofReal_coe_nnreal] at hr
    have hi := hInv s
    rw [J.mand_of_true hb, ← c.PostH_mask_eq_of_mass_le J hr] at hi
    apply hi.trans
    apply c.PostH_mono
    intro σ
    by_cases hd : t σ < t s.store
    case neg =>
      simpa only [J.mask_of_neg (φ := fun τ => t τ < t s.store) hd] using
        ((J.mask fun τ => (t τ).toNat < n) σ).2.1
    simp only [J.mask_of_pos (φ := fun τ => t τ < t s.store) hd]
    by_cases hp : φ σ
    · have hnat : (t σ).toNat < n := by
        have := hbound σ hp
        lia
      rw [J.mask_of_pos (φ := fun τ => (t τ).toNat < n) hnat]
    · simpa only [J, A.mask_of_neg hp] using ((J.mask fun τ => (t τ).toNat < n) σ).2.1

end QuantumProgram
