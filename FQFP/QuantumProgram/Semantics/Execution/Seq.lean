/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for decomposition at the handover in a sequential command.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/SeqDecomp.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Approximation
import FQFP.Algebra.BigOperators.Group.List.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Terminal histories of a sequential composition

A terminal history of `p.seq q` of length `n` hands over at exactly one depth `j ≤ n`.
The remaining `n - j` steps start from the state produced by that occurrence of `p`.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram.Configuration

variable {Store Cell : Type*} {H : Qudit}

variable (c : Configuration Store Cell H) (q : Command Store Cell H)

/-- A running command's post-expectation is the sum over its one-step successors. -/
theorem PostH_eq_sum_next {p : Command Store Cell H} (s : CQState Store H)
    {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    (Configuration.mk (some p) s).PostH A =
      ((Configuration.mk (some p) s).next.map (fun d => d.PostH A)).sum := by
  rw [← terminalWeight_expectation _ hA, terminalWeight_eq_zero_add_sum_next]
  simp [terminalWeightAt_zero, terminalWeight_expectation _ hA]

/-- At depth `n`, split a sequential execution at every possible handover depth. -/
theorem terminalWeightAt_seqWith (n : ℕ) (w : CQState Store H → ℝ≥0∞) :
    (c.seqWith q).terminalWeightAt n w =
      ∑ j ∈ Finset.range (n + 1),
        c.terminalWeightAt j (fun t =>
          (Configuration.mk (some q) t).terminalWeightAt (n - j) w) := by
  induction n generalizing c with
  | zero => simp [terminalWeightAt_zero, seqWith]
  | succ n ih =>
    obtain ⟨_ | p, s⟩ := c
    · rw [Finset.sum_range_succ']
      have hz (j : ℕ) (v : CQState Store H → ℝ≥0∞) :
          (Configuration.mk (Cell := Cell) none s).terminalWeightAt (j + 1) v = 0 := by
        simp [terminalWeightAt_succ, next]
      simp only [hz, Finset.sum_const_zero, zero_add, Nat.sub_zero]
      simp [terminalWeightAt_zero, seqWith]
    · let c := Configuration.mk (some p) s
      change (c.seqWith q).terminalWeightAt (n + 1) w = _
      have step : (c.seqWith q).next = c.next.map (·.seqWith q) := rfl
      rw [terminalWeightAt_succ, step, List.map_map, Finset.sum_range_succ']
      have hz (v : CQState Store H → ℝ≥0∞) : c.terminalWeightAt 0 v = 0 := by
        simp [terminalWeightAt_zero, c]
      rw [hz, add_zero]
      simp only [Function.comp_def, ih, TrotterError.List.sum_map_sum, Nat.succ_sub_succ,
        terminalWeightAt_succ]
      rfl

/-- Post-expectation at an exact depth, disintegrated over the first command's exits. -/
theorem postAtE_seqWith (n : ℕ) (A : Store → Operator H) :
    (c.seqWith q).postAtE n A = ∑ j ∈ Finset.range (n + 1),
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).postAtE (n - j) A) :=
  c.terminalWeightAt_seqWith q n _

/-- Terminating trace at an exact depth, disintegrated over the first command's exits. -/
theorem terminalMassAt_seqWith (n : ℕ) :
    ((c.seqWith q).terminalMassAt n : ℝ≥0∞) = ∑ j ∈ Finset.range (n + 1),
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminalMassAt (n - j)) := by
  simp only [← terminalWeightAt_mass, terminalWeightAt_seqWith]

private theorem sum_terminalWeightAt_seqWith (n : ℕ) (w : CQState Store H → ℝ≥0∞) :
    ∑ d ∈ Finset.range n, (c.seqWith q).terminalWeightAt d w =
      ∑ j ∈ Finset.range n, c.terminalWeightAt j (fun t =>
        ∑ i ∈ Finset.range (n - j), (Configuration.mk (some q) t).terminalWeightAt i w) := by
  simp only [terminalWeightAt_seqWith, c.terminalWeightAt_finsetSum]
  exact Finset.sum_range_diag_flip n (fun j i =>
    c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminalWeightAt i w))

/-- Post-expectation before the horizon, with the remaining depth passed to the continuation. -/
theorem postUpTo_seqWith (n : ℕ) (A : Store → Operator H) :
    (c.seqWith q).postUpTo n A = ∑ j ∈ Finset.range n,
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).postUpTo (n - j) A) :=
  c.sum_terminalWeightAt_seqWith q n _

/-- Terminating trace before the horizon, with the remaining depth passed to the continuation. -/
theorem terminalMassUpTo_seqWith (n : ℕ) :
    (c.seqWith q).terminalMassUpTo n = ∑ j ∈ Finset.range n,
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminalMassUpTo (n - j)) := by
  simpa only [terminalMassUpTo, ← terminalWeightAt_mass] using
    c.sum_terminalWeightAt_seqWith q n (fun t => t.mass)

/-- The bounded value of a sequence credits outstanding first-phase mass and gives each
handover state the continuation's value at the remaining horizon. -/
theorem Val_seqWith (n : ℕ) (A : Store → Operator H) :
    (c.seqWith q).Val n A = (∑ j ∈ Finset.range n,
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).Val (n - j) A)) +
        ((c.state.mass : ℝ≥0∞) - c.terminalMassUpTo n) := by
  let rem (j : ℕ) (t : CQState Store H) :=
    (t.mass : ℝ≥0∞) - (Configuration.mk (some q) t).terminalMassUpTo (n - j)
  have split : (∑ j ∈ Finset.range n, c.terminalWeightAt j (rem j)) +
      (c.seqWith q).terminalMassUpTo n = c.terminalMassUpTo n := by
    rw [terminalMassUpTo_seqWith, ← Finset.sum_add_distrib]
    unfold terminalMassUpTo
    apply Finset.sum_congr rfl
    intro j _
    rw [← terminalWeightAt_add, ← terminalWeightAt_mass]
    exact congrArg (c.terminalWeightAt j) (funext fun t =>
      tsub_add_cancel_of_le ((Configuration.mk (some q) t).terminalMassUpTo_le_mass (n - j)))
  have hterm := (c.seqWith q).terminalMassUpTo_le_mass n
  apply (ENNReal.add_left_inj (hterm.trans_lt ENNReal.coe_lt_top).ne).mp
  simp only [Val, terminalWeightAt_add, Finset.sum_add_distrib]
  rw [add_assoc, tsub_add_cancel_of_le hterm, postUpTo_seqWith]
  change _ = (_ + ∑ j ∈ Finset.range n, c.terminalWeightAt j (rem j)) + _ + _
  rw [add_assoc _ _ ((c.seqWith q).terminalMassUpTo n), add_assoc,
    add_comm (_ - _) ((c.seqWith q).terminalMassUpTo n),
    ← add_assoc (∑ j ∈ Finset.range n, c.terminalWeightAt j (rem j)), split,
    add_tsub_cancel_of_le (c.terminalMassUpTo_le_mass n)]
  rfl

private theorem tsum_triangle (f : ℕ → ℕ → ℝ≥0∞) :
    ∑' d, ∑ j ∈ Finset.range (d + 1), f j (d - j) = ∑' j, ∑' i, f j i := by
  have diag (d : ℕ) : ∑ j ∈ Finset.range (d + 1), f j (d - j) =
      ∑' p : (Finset.antidiagonal d : Finset (ℕ × ℕ)), f p.val.1 p.val.2 := by
    rw [Finset.tsum_subtype _ fun p : ℕ × ℕ => f p.1 p.2]
    exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p => f p.1 p.2) d).symm
  rw [tsum_congr diag, ← tsum_sigma'
    (fun p : (Σ d : ℕ, (Finset.antidiagonal d : Finset (ℕ × ℕ))) => f p.2.val.1 p.2.val.2),
    ← tsum_prod (f := f)]
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq fun p : ℕ × ℕ => f p.1 p.2

/-- Sum a continuation weight by summing the outputs of the second command at each handover. -/
theorem terminalWeight_seqWith (w : CQState Store H → ℝ≥0∞) :
    (c.seqWith q).terminalWeight w =
      c.terminalWeight (fun t => (Configuration.mk (some q) t).terminalWeight w) := by
  simp only [terminalWeight, terminalWeightAt_seqWith, c.terminalWeightAt_tsum]
  exact tsum_triangle (fun j i =>
    c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminalWeightAt i w))

/-- Over all depths, each first-phase exit contributes the continuation's post-expectation. -/
theorem PostH_seqWith {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    (c.seqWith q).PostH A = ∑' j,
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).PostH A) := by
  change (c.seqWith q).PostH A =
    c.terminalWeight (fun t => (Configuration.mk (some q) t).PostH A)
  rw [← terminalWeight_expectation _ hA, terminalWeight_seqWith]
  simp only [terminalWeight_expectation _ hA]

/-- Total terminating trace is the sum of the continuation's terminating traces at handover. -/
theorem terminatingMass_seqWith : (c.seqWith q).terminatingMass = ∑' j,
    c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminatingMass) := by
  change (c.seqWith q).terminatingMass =
    c.terminalWeight (fun t => (Configuration.mk (some q) t).terminatingMass)
  rw [← (c.seqWith q).terminalWeight_mass, terminalWeight_seqWith]
  simp only [terminalWeight_mass]

/-- If the continuation returns all trace at every handover, the sequence returns the first
phase's terminating trace. -/
theorem terminatingMass_seqWith_eq_of_mem_frontier
    (h : ∀ n t, ⟨none, t⟩ ∈ c.frontier n →
      (Configuration.mk (some q) t).terminatingMass = t.mass) :
    (c.seqWith q).terminatingMass = c.terminatingMass :=
  (c.terminatingMass_seqWith q).trans
    ((c.terminalWeight_congr_of_mem_frontier h).trans c.terminalWeight_mass)

/-- Residual trace of a sequence is lost either before handover or in a continuation. -/
theorem nonterminatingMass_seqWith : (c.seqWith q).nonterminatingMass = c.nonterminatingMass +
    ∑' j, c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).nonterminatingMass) := by
  let remaining (t : CQState Store H) := (Configuration.mk (some q) t).nonterminatingMass
  change (c.seqWith q).nonterminatingMass = c.nonterminatingMass + c.terminalWeight remaining
  have split : (c.seqWith q).terminatingMass + c.terminalWeight remaining = c.terminatingMass := by
    rw [← (c.seqWith q).terminalWeight_mass, terminalWeight_seqWith]
    simp only [terminalWeight_mass]
    rw [← c.terminalWeight_add, ← c.terminalWeight_mass]
    exact congrArg c.terminalWeight (funext fun t =>
      (Configuration.mk (some q) t).terminatingMass_add_nonterminatingMass)
  apply (ENNReal.add_right_inj ((c.seqWith q).terminatingMass_le.trans_lt ENNReal.coe_lt_top).ne).mp
  rw [terminatingMass_add_nonterminatingMass, add_left_comm _ c.nonterminatingMass,
    split, add_comm, terminatingMass_add_nonterminatingMass]
  rfl

end QuantumProgram.Configuration

namespace QuantumProgram.Command

variable {Store Cell : Type*} {H : Qudit} (p : Command Store Cell H)

/-- Sum a continuation weight over all terminal occurrences of a command on the given input. -/
noncomputable def outputWeight (w : CQState Store H → ℝ≥0∞) (s : CQState Store H) : ℝ≥0∞ :=
  (Configuration.mk (some p) s).terminalWeight w

/-- Compare continuations only at terminal states reachable from this input. -/
theorem outputWeight_le_of_mem_frontier {v w : CQState Store H → ℝ≥0∞} {s : CQState Store H}
    (h : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n → v t ≤ w t) :
    p.outputWeight v s ≤ p.outputWeight w s :=
  (Configuration.mk (some p) s).terminalWeight_le_of_mem_frontier h

/-- Agreement at the reachable terminal states suffices for equality of output weights. -/
theorem outputWeight_congr_of_mem_frontier {v w : CQState Store H → ℝ≥0∞} {s : CQState Store H}
    (h : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n → v t = w t) :
    p.outputWeight v s = p.outputWeight w s :=
  (Configuration.mk (some p) s).terminalWeight_congr_of_mem_frontier h

/-- Increasing a continuation weight increases its sum over the output histories. -/
theorem outputWeight_mono : Monotone p.outputWeight :=
  fun _ _ h s => (Configuration.mk (some p) s).terminalWeight_mono h

/-- Two charges at the same terminal occurrence contribute additively. -/
theorem outputWeight_add (v w : CQState Store H → ℝ≥0∞) (s : CQState Store H) :
    p.outputWeight (fun t => v t + w t) s = p.outputWeight v s + p.outputWeight w s :=
  (Configuration.mk (some p) s).terminalWeight_add v w

/-- A constant price per unit of output weight factors out of the history sum. -/
theorem outputWeight_const_mul (a : ℝ≥0∞) (w : CQState Store H → ℝ≥0∞) (s : CQState Store H) :
    p.outputWeight (fun t => a * w t) s = a * p.outputWeight w s :=
  (Configuration.mk (some p) s).terminalWeight_const_mul a w

/-- Nonnegative series of continuation weights can be summed before or after execution. -/
theorem outputWeight_tsum {ι : Type*} (w : ι → CQState Store H → ℝ≥0∞) (s : CQState Store H) :
    p.outputWeight (fun t => ∑' i, w i t) s = ∑' i, p.outputWeight (w i) s :=
  (Configuration.mk (some p) s).terminalWeight_tsum w

/-- Weighting every output by its trace gives the terminating mass of the command. -/
theorem outputWeight_mass (s : CQState Store H) :
    p.outputWeight (fun t => t.mass) s = (Configuration.mk (some p) s).terminatingMass :=
  (Configuration.mk (some p) s).terminalWeight_mass

/-- A fixed price per unit of output trace charges that price times the terminating mass. -/
theorem outputWeight_const_mul_mass (a : ℝ≥0∞) (s : CQState Store H) :
    p.outputWeight (fun t => a * t.mass) s = a * (Configuration.mk (some p) s).terminatingMass := by
  rw [p.outputWeight_const_mul, p.outputWeight_mass]

/-- Summing the output expectations of a positive observable gives the post-expectation. -/
theorem outputWeight_expectation (s : CQState Store H) {A : Store → Operator H}
    (hA : ∀ σ, (A σ).IsPositive) :
    p.outputWeight (fun t => ENNReal.ofReal (t.expectation (A t.store))) s =
      (Configuration.mk (some p) s).PostH A :=
  (Configuration.mk (some p) s).terminalWeight_expectation hA

/-- A continuation on a sequence can be pulled back one command at a time. -/
theorem outputWeight_seq (q : Command Store Cell H) (w : CQState Store H → ℝ≥0∞) :
    (p.seq q).outputWeight w = p.outputWeight (q.outputWeight w) :=
  funext fun s => (Configuration.mk (some p) s).terminalWeight_seqWith q w

/-- Only the branch selected at the input store contributes output weight. -/
theorem outputWeight_ite (b : Store → Bool) (q : Command Store Cell H)
    (w : CQState Store H → ℝ≥0∞) (s : CQState Store H) :
    (Command.ite b p q).outputWeight w s = (if b s.store then p else q).outputWeight w s :=
  Configuration.terminalWeight_singleton (Configuration.next_ite b p q s) w

end QuantumProgram.Command
