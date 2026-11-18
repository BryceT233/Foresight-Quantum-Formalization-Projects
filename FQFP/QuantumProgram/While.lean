/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.SeqDecomp

/-!
# Partial and total correctness of a guarded loop

An invariant preserved by the body on guarded inputs holds on loop exit with the guard false.
Partial correctness follows by induction on the execution horizon. Total correctness
uses a natural-valued rank and the post-expectation at each handover from the body.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

private theorem next_whileDo_of_true {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = true) :
    (Configuration.mk (some (.whileDo b p)) s).next =
      [(Configuration.mk (some p) s).seqWith (.whileDo b p)] := by
  simp [Configuration.next, Command.step, Configuration.seqWith, hb]

private theorem next_whileDo_of_false {b : Store → Bool} (p : Command Store Cell H)
    {s : CQState Store H} (hb : b s.store = false) :
    (Configuration.mk (some (.whileDo b p)) s).next = [⟨none, s⟩] := by
  simp [Configuration.next, Command.step, hb]

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
      have hf : (Configuration.mk (some (.whileDo b p)) s).frontier 1 = [⟨none, s⟩] := by
        simpa [Configuration.frontier] using next_whileDo_of_false p hb
      simpa only [J.mandNot_of_false hb] using
        Configuration.ofReal_expectation_le_PostH_of_frontier hf (fun σ => J.mandNot b σ)
    | true =>
      rw [Configuration.PostH_singleton (next_whileDo_of_true p hb),
        Configuration.PostH_seqWith _ _ (J.mandNot b).isPositive]
      have prem := h n s
      rw [(J.mand b).mask_of_pos (φ := fun σ => t σ = n) hn, J.mand_of_true hb] at prem
      apply prem.trans
      apply ENNReal.tsum_le_tsum
      intro j
      let c := Configuration.mk (some p) s
      rw [← c.postAtE_eq_ofReal_postAt j (J.mask fun σ => t σ < n).isPositive]
      apply c.terminalWeightAt_mono
      intro u
      by_cases hu : t u.store < n
      · simpa only [J.mask_of_pos (φ := fun σ => t σ < n) hu] using ih (t u.store) hu u rfl
      · simp [J.mask_of_neg (φ := fun σ => t σ < n) hu, CQState.expectation, Operator.trace]

end QuantumProgram
