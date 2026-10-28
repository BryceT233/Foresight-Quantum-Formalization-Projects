/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Tactic.Linarith

/-!
# Subset sums grouped by cardinality

Cardinality grouping allows any sufficiently large cutoff.

## Main results

* `Finset.sum_powerset_eq_sum_powersetCard_of_card_le`: grouping below a cardinality bound.
-/

@[expose] public section

/-- Sum subsets by cardinality up to any upper bound for the size of the ambient set. -/
theorem _root_.Finset.sum_powerset_eq_sum_powersetCard_of_card_le
    {α β : Type*} [AddCommMonoid β] {s : Finset α} {n : ℕ} (h : s.card ≤ n)
    (f : Finset α → β) :
    ∑ t ∈ s.powerset, f t = ∑ k ∈ Finset.range (n + 1), ∑ t ∈ s.powersetCard k, f t := by
  rw [Finset.sum_powerset]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
  intro k hk hnot
  have hsk : s.card < k := by
    simp only [Finset.mem_range] at hk hnot
    lia
  rw [Finset.powersetCard_eq_empty.mpr hsk, Finset.sum_empty]
