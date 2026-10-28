/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.QuinticTaylor

/-!
# Mixed Taylor pieces of the quintic BCH polynomial

A total substitution set `s` marks the positions receiving either perturbation. A subset `t`
of `s` marks the positions receiving `V`; the other positions of `s` receive `W`. This uses
the same word groups and substitution sets as the one-perturbation Taylor expansion.

## Main definitions

* `bchQuinticMixedGroupSubsets`, `bchQuinticMixedSubsetPiece`: pieces with prescribed counts.
* `bchQuinticTermBilinDiff`: exactly one occurrence of each perturbation.
* `bchQuinticTermMixed2Remainder`: both perturbations occur, with total degree at least three.

## Main results

* `bchQuinticSubsetPiece_add_eq_sum_mixed`: split a single perturbation into two colors.
* `bchQuinticTermBilinDecomp`: the mixed second-difference matching identity.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

variable {A : Type*}

/-- A word group with `k` perturbation positions, exactly `p` of them marked `V`.
All other perturbed positions carry `W`, and the original word order is preserved. -/
def bchQuinticMixedGroupSubsets [Semiring A] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k p : ℕ) (x V W y : A) : A :=
  ∑ i, ∑ s ∈ (wordPositions (words i) 0).powersetCard k, ∑ t ∈ s.powersetCard p,
    (List.ofFn (t.piecewise (fun _ ↦ V)
      (s.piecewise (fun _ ↦ W) (fun j ↦ ![x, y] (words i j))))).prod

/-- The mixed piece at total perturbation degree `k` and `V`-degree `p`, with the
same four signed word-group coefficients as the quintic BCH polynomial. -/
def bchQuinticMixedSubsetPiece [Ring A] [Algebra ℚ A] (k p : ℕ) (x V W y : A) : A :=
  (720 : ℚ)⁻¹ • bchQuinticBracket
    (bchQuinticMixedGroupSubsets bchQuinticGroup1Words k p x V W y)
    (bchQuinticMixedGroupSubsets bchQuinticGroup4Words k p x V W y)
    (bchQuinticMixedGroupSubsets bchQuinticGroup6Words k p x V W y)
    (bchQuinticMixedGroupSubsets bchQuinticGroup24Words k p x V W y)

/-- The bilinear mixed difference: exactly one `V` and exactly one `W`. -/
def bchQuinticTermBilinDiff [Ring A] [Algebra ℚ A] (x V W y : A) : A :=
  bchQuinticMixedSubsetPiece 2 1 x V W y

/-- The higher mixed terms, containing both perturbations and at least three perturbation
positions. Quintic BCH words have at most four positions in their first argument. -/
def bchQuinticTermMixed2Remainder [Ring A] [Algebra ℚ A] (x V W y : A) : A :=
  bchQuinticMixedSubsetPiece 3 1 x V W y + bchQuinticMixedSubsetPiece 3 2 x V W y +
    bchQuinticMixedSubsetPiece 4 1 x V W y + bchQuinticMixedSubsetPiece 4 2 x V W y +
    bchQuinticMixedSubsetPiece 4 3 x V W y

/-- Splitting a perturbation into two colors refines each one-color word-group piece. -/
lemma bchQuinticGroupSubsets_add_eq_sum_mixed [Semiring A] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k : ℕ) (x V W y : A) :
    bchQuinticGroupSubsets words k x (V + W) y =
      ∑ p ∈ range (k + 1), bchQuinticMixedGroupSubsets words k p x V W y := by
  unfold bchQuinticGroupSubsets bchQuinticMixedGroupSubsets
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  have hsk : s.card = k := (mem_powersetCard.mp hs).2
  rw [← hsk, ← Finset.sum_powerset]
  exact prod_piecewise_add_eq_sum (fun _ ↦ V) (fun _ ↦ W) (fun j ↦ ![x, y] (words i j)) s

/-- With zero `V` positions, a mixed piece is the original single-`W` piece. -/
lemma bchQuinticMixedGroupSubsets_zero [Semiring A] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k : ℕ) (x V W y : A) :
    bchQuinticMixedGroupSubsets words k 0 x V W y = bchQuinticGroupSubsets words k x W y := by
  simp only [bchQuinticMixedGroupSubsets, powersetCard_zero, sum_singleton,
    piecewise_empty, bchQuinticGroupSubsets]

/-- When every perturbed position carries `V`, a mixed piece is the single-`V` piece. -/
lemma bchQuinticMixedGroupSubsets_self [Semiring A] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k : ℕ) (x V W y : A) :
    bchQuinticMixedGroupSubsets words k k x V W y = bchQuinticGroupSubsets words k x V y := by
  unfold bchQuinticMixedGroupSubsets bchQuinticGroupSubsets
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro s hs
  rw [← (mem_powersetCard.mp hs).2, powersetCard_self, sum_singleton]
  congr 2
  funext j
  by_cases hj : j ∈ s <;> simp [piecewise, hj]

/-- The all-`W` endpoint of a mixed quintic piece. -/
lemma bchQuinticMixedSubsetPiece_zero [Ring A] [Algebra ℚ A] (k : ℕ) (x V W y : A) :
    bchQuinticMixedSubsetPiece k 0 x V W y = bchQuinticSubsetPiece k x W y := by
  simp only [bchQuinticMixedSubsetPiece, bchQuinticMixedGroupSubsets_zero, bchQuinticSubsetPiece]

/-- The all-`V` endpoint of a mixed quintic piece. -/
lemma bchQuinticMixedSubsetPiece_self [Ring A] [Algebra ℚ A] (k : ℕ) (x V W y : A) :
    bchQuinticMixedSubsetPiece k k x V W y = bchQuinticSubsetPiece k x V y := by
  simp only [bchQuinticMixedSubsetPiece, bchQuinticMixedGroupSubsets_self, bchQuinticSubsetPiece]

/-- Splitting a perturbation refines a quintic subset piece into its mixed pieces. -/
lemma bchQuinticSubsetPiece_add_eq_sum_mixed [Ring A] [Algebra ℚ A]
    (k : ℕ) (x V W y : A) :
    bchQuinticSubsetPiece k x (V + W) y =
      ∑ p ∈ range (k + 1), bchQuinticMixedSubsetPiece k p x V W y := by
  simp only [bchQuinticSubsetPiece, bchQuinticGroupSubsets_add_eq_sum_mixed,
    bchQuinticMixedSubsetPiece, bchQuinticBracket, Finset.smul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- **Mixed second-difference matching identity** for the quintic BCH polynomial.
The bilinear term has exactly one occurrence of each perturbation; every remaining term
has both perturbations and at least three substituted positions. -/
theorem bchQuinticTermBilinDecomp [Ring A] [Algebra ℚ A] (x V W y : A) :
    bchQuinticTerm (x + V + W) y - bchQuinticTerm (x + V) y -
      bchQuinticTerm (x + W) y + bchQuinticTerm x y =
      bchQuinticTermBilinDiff x V W y + bchQuinticTermMixed2Remainder x V W y := by
  rw [show x + V + W = x + (V + W) by abel,
    bchQuinticTerm_add_eq_sum_pieces x (V + W) y,
    bchQuinticTerm_add_eq_sum_pieces x V y, bchQuinticTerm_add_eq_sum_pieces x W y]
  simp only [sum_range_succ, sum_range_zero, zero_add, bchQuinticSubsetPiece_zero]
  rw [bchQuinticSubsetPiece_add_eq_sum_mixed 1 x V W y,
    bchQuinticSubsetPiece_add_eq_sum_mixed 2 x V W y,
    bchQuinticSubsetPiece_add_eq_sum_mixed 3 x V W y,
    bchQuinticSubsetPiece_add_eq_sum_mixed 4 x V W y]
  simp only [sum_range_succ, sum_range_zero, zero_add,
    bchQuinticMixedSubsetPiece_zero, bchQuinticMixedSubsetPiece_self,
    bchQuinticTermBilinDiff, bchQuinticTermMixed2Remainder]
  abel

end FQFP.BCH
