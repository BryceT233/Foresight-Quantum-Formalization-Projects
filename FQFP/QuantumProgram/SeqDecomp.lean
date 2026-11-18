/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Approximation

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

private theorem sum_map_sum {α ι M : Type*} [AddCommMonoid M] (l : List α) (u : Finset ι)
    (f : ι → α → M) :
    (l.map fun a => ∑ i ∈ u, f i a).sum = ∑ i ∈ u, (l.map (f i)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem sum_triangle {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∑ d ∈ Finset.range n, ∑ j ∈ Finset.range (d + 1), f j (d - j) =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range (n - j), f j i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have split (j) (hj : j ∈ Finset.range n) :
        ∑ i ∈ Finset.range (n + 1 - j), f j i = (∑ i ∈ Finset.range (n - j), f j i) +
          f j (n - j) := by
      rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 by lia, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (f := fun j => ∑ i ∈ Finset.range (n + 1 - j), f j i),
      Finset.sum_congr rfl split, Finset.sum_add_distrib, show n + 1 - n = 1 by lia,
      Finset.sum_range_one, Finset.sum_range_succ (f := fun j => f j (n - j)),
      Nat.sub_self, add_assoc]

variable (c : Configuration Store Cell H) (q : Command Store Cell H)

/-- Partition the next depth by the first successor, retaining repeated occurrences. -/
theorem frontier_succ (n : ℕ) : c.frontier (n + 1) = c.next.flatMap (·.frontier n) := by
  induction n with
  | zero => simp [frontier]
  | succ n ih => rw [frontier, ih, List.flatMap_assoc]; rfl

/-- Exact-depth terminal weights after one step sum over all one-step successors. -/
theorem terminalWeightAt_succ (n : ℕ) (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt (n + 1) w = (c.next.map (·.terminalWeightAt n w)).sum := by
  unfold terminalWeightAt
  rw [frontier_succ]
  induction c.next with
  | nil => simp
  | cons d l ih => simp only [List.flatMap_cons, List.filter_append, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons, ih]

/-- At depth `n`, split a sequential execution at every possible handover depth. -/
theorem terminalWeightAt_seqWith (n : ℕ) (w : CQState Store H → ℝ≥0∞) :
    (c.seqWith q).terminalWeightAt n w =
      ∑ j ∈ Finset.range (n + 1),
        c.terminalWeightAt j (fun t =>
          (Configuration.mk (some q) t).terminalWeightAt (n - j) w) := by
  induction n generalizing c with
  | zero => simp [terminalWeightAt, frontier, seqWith]
  | succ n ih =>
    obtain ⟨_ | p, s⟩ := c
    · rw [Finset.sum_range_succ']
      have hz (j : ℕ) (v : CQState Store H → ℝ≥0∞) :
          (Configuration.mk (Cell := Cell) none s).terminalWeightAt (j + 1) v = 0 := by
        simp [terminalWeightAt_succ, next]
      simp only [hz, Finset.sum_const_zero, zero_add, Nat.sub_zero]
      simp [terminalWeightAt, frontier, seqWith]
    · let c := Configuration.mk (some p) s
      change (c.seqWith q).terminalWeightAt (n + 1) w = _
      have step : (c.seqWith q).next = c.next.map (·.seqWith q) := rfl
      rw [terminalWeightAt_succ, step, List.map_map, Finset.sum_range_succ']
      have hz (v : CQState Store H → ℝ≥0∞) : c.terminalWeightAt 0 v = 0 := by
        simp [terminalWeightAt, frontier, c]
      rw [hz, add_zero]
      simp only [Function.comp_def, ih, sum_map_sum, Nat.succ_sub_succ, terminalWeightAt_succ]
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
  simp only [terminalWeightAt_seqWith]
  rw [sum_triangle (fun j i => c.terminalWeightAt j
    (fun t => (Configuration.mk (some q) t).terminalWeightAt i w))]
  simp only [terminalWeightAt, sum_map_sum]

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
  rw [tsum_congr diag, ← ENNReal.tsum_sigma'
    (fun p : (Σ d : ℕ, (Finset.antidiagonal d : Finset (ℕ × ℕ))) => f p.2.val.1 p.2.val.2),
    ← ENNReal.tsum_prod (f := f)]
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq fun p : ℕ × ℕ => f p.1 p.2

private theorem tsum_terminalWeightAt_seqWith (w : CQState Store H → ℝ≥0∞) :
    ∑' d, (c.seqWith q).terminalWeightAt d w =
      ∑' j, c.terminalWeightAt j (fun t =>
        ∑' i, (Configuration.mk (some q) t).terminalWeightAt i w) := by
  simp only [terminalWeightAt_seqWith]
  rw [tsum_triangle (fun j i => c.terminalWeightAt j
    (fun t => (Configuration.mk (some q) t).terminalWeightAt i w))]
  apply tsum_congr
  intro j
  simp only [terminalWeightAt, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- Over all depths, each first-phase exit contributes the continuation's post-expectation. -/
theorem PostH_seqWith {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    (c.seqWith q).PostH A = ∑' j,
      c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).PostH A) := by
  simpa only [PostH, ← postAtE_eq_ofReal_postAt _ _ hA, postAtE] using
    c.tsum_terminalWeightAt_seqWith q (fun t => ENNReal.ofReal (t.expectation (A t.store)))

/-- Total terminating trace is the sum of the continuation's terminating traces at handover. -/
theorem terminatingMass_seqWith : (c.seqWith q).terminatingMass = ∑' j,
    c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).terminatingMass) := by
  simpa only [terminatingMass, ← terminalWeightAt_mass] using
    c.tsum_terminalWeightAt_seqWith q (fun t => t.mass)

/-- Residual trace of a sequence is lost either before handover or in a continuation. -/
theorem nonterminatingMass_seqWith : (c.seqWith q).nonterminatingMass = c.nonterminatingMass +
    ∑' j, c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).nonterminatingMass) := by
  have split : (c.seqWith q).terminatingMass +
      ∑' j, c.terminalWeightAt j (fun t => (Configuration.mk (some q) t).nonterminatingMass) =
        c.terminatingMass := by
    rw [terminatingMass_seqWith, ← ENNReal.tsum_add]
    apply tsum_congr
    intro j
    rw [← terminalWeightAt_add, ← terminalWeightAt_mass]
    exact congrArg (c.terminalWeightAt j) (funext fun t =>
      (Configuration.mk (some q) t).terminatingMass_add_nonterminatingMass)
  apply (ENNReal.add_right_inj ((c.seqWith q).terminatingMass_le.trans_lt ENNReal.coe_lt_top).ne).mp
  rw [terminatingMass_add_nonterminatingMass, add_left_comm _ c.nonterminatingMass,
    split, add_comm, terminatingMass_add_nonterminatingMass]
  rfl

end QuantumProgram.Configuration
