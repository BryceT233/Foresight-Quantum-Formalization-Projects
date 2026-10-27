/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Algebra.WordTaylor

/-!
# Taylor expansion of the septic BCH polynomial

The existing septic coefficient table supplies every Taylor component. Subsets of the
first-argument positions record the perturbations without changing multiplication order.
The linear component has one perturbation factor; the second-order remainder sums the
components with two through six perturbation factors.

## Main definitions

* `bchSepticSubsetPiece`: a component with a prescribed perturbation degree.
* `bchSepticTermLinDiff`: the first-argument directional derivative.
* `bchSepticTermTaylor2Remainder`: the components of perturbation degree at least two.

## Main results

* `bchSepticTerm_add_eq_sum_pieces`: the complete finite Taylor expansion.
* `bchSepticTermTaylor2Decomp`: exact second-order Taylor matching.
-/

@[expose] public noncomputable section

open Finset FQFP.WordTable

namespace FQFP.BCH

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The septic component with exactly `k` first-argument perturbation positions. -/
def bchSepticSubsetPiece (k : ℕ) (x V y : A) : A :=
  taylorPiece coefficientScale bchSepticTermTable 0 ![x, y] V k

/-- The first-order directional difference of the septic polynomial in its first argument. -/
def bchSepticTermLinDiff (x V y : A) : A := bchSepticSubsetPiece 1 x V y

/-- The second-order Taylor remainder, with two through six perturbation factors. -/
def bchSepticTermTaylor2Remainder (x V y : A) : A :=
  ∑ k ∈ range 5, bchSepticSubsetPiece (k + 2) x V y

/-- Every septic BCH word has at most six positions in its first argument. -/
lemma card_wordPositions_bchSepticTermTable :
    ∀ p ∈ bchSepticTermTable, (wordPositions p.1.get 0).card ≤ 6 := by
  have hall : bchSepticTermTable.all (fun p ↦ decide (p.1.count 0 ≤ 6)) = true := by
    decide +kernel
  intro p hp
  simpa only [card_wordPositions_get, decide_eq_true_eq] using List.all_eq_true.mp hall p hp

/-- The septic component with no perturbation factors is the original polynomial. -/
lemma bchSepticSubsetPiece_zero (x V y : A) :
    bchSepticSubsetPiece 0 x V y = bchSepticTerm x y :=
  taylorPiece_zero _ _ _ _ _

/-- A septic component above every possible perturbation degree vanishes. -/
lemma bchSepticSubsetPiece_eq_zero_of_six_lt (k : ℕ) (x V y : A) (hk : 6 < k) :
    bchSepticSubsetPiece k x V y = 0 := by
  apply taylorPiece_eq_zero_of_card_lt
  intro p hp
  exact lt_of_le_of_lt (card_wordPositions_bchSepticTermTable p hp) hk

/-- A positive-degree septic component vanishes in the zero direction. -/
lemma bchSepticSubsetPiece_zero_direction (x y : A) {k : ℕ} (hk : 0 < k) :
    bchSepticSubsetPiece k x 0 y = 0 :=
  taylorPiece_zero_direction _ _ _ _ hk

/-- The linear septic component is additive in its perturbation. -/
lemma bchSepticTermLinDiff_add (x V W y : A) :
    bchSepticTermLinDiff x (V + W) y =
      bchSepticTermLinDiff x V y + bchSepticTermLinDiff x W y :=
  taylorPiece_one_add _ _ _ _ _ _

/-- The linear septic component respects rational scalar multiplication. -/
lemma bchSepticTermLinDiff_smul (x V y : A) (c : ℚ) :
    bchSepticTermLinDiff x (c • V) y = c • bchSepticTermLinDiff x V y :=
  taylorPiece_one_smul _ _ _ _ _ _

/-- The linear septic component vanishes at zero perturbation. -/
@[simp]
lemma bchSepticTermLinDiff_zero (x y : A) : bchSepticTermLinDiff x 0 y = 0 :=
  bchSepticSubsetPiece_zero_direction x y (by decide)

/-- The septic Taylor remainder vanishes at zero perturbation. -/
@[simp]
lemma bchSepticTermTaylor2Remainder_zero (x y : A) :
    bchSepticTermTaylor2Remainder x 0 y = 0 := by
  apply sum_eq_zero
  intro k _
  exact bchSepticSubsetPiece_zero_direction x y (by lia)

/-- The septic polynomial at a perturbed input is the sum of its Taylor components. -/
theorem bchSepticTerm_add_eq_sum_pieces (x V y : A) :
    bchSepticTerm (x + V) y = ∑ k ∈ range 7, bchSepticSubsetPiece k x V y := by
  have hu : Function.update (![x, y] : Fin 2 → A) 0 (x + V) = ![x + V, y] := by
    ext i
    fin_cases i <;> simp
  simpa only [Matrix.cons_val_zero, hu, bchSepticTerm, bchSepticSubsetPiece] using
    eval_update_add_eq_sum_taylorPiece coefficientScale bchSepticTermTable 0 ![x, y] V 6
      card_wordPositions_bchSepticTermTable

end FQFP.BCH

namespace FQFP.BCH

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- **Second-order Taylor matching** for the septic BCH polynomial. -/
theorem bchSepticTermTaylor2Decomp (x V y : A) :
    bchSepticTerm (x + V) y - bchSepticTerm x y =
      bchSepticTermLinDiff x V y + bchSepticTermTaylor2Remainder x V y := by
  rw [bchSepticTerm_add_eq_sum_pieces]
  simp only [sum_range_succ, sum_range_zero, zero_add, bchSepticSubsetPiece_zero,
    bchSepticTermLinDiff, bchSepticTermTaylor2Remainder, Nat.reduceAdd]
  abel

end FQFP.BCH
