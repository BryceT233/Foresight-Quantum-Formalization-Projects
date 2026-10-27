/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Algebra.WordTaylor

/-!
# Taylor expansions of the sextic BCH polynomial

The existing sextic coefficient table supplies every Taylor coefficient. Substitution subsets
separate the linear perturbation from the terms with two, three, or four perturbation factors.
Shifting the base of the linear term also gives the mixed second-difference decomposition.

## Main definitions

* `bchSexticSubsetPiece`: the component of a specified perturbation degree.
* `bchSexticTermLinDiff`, `bchSexticTermTaylor2Remainder`: the first-order Taylor split.
* `bchSexticTermLinDiffShift`: the change of the directional derivative at a shifted base.

## Main results

* `bchSexticTermTaylor2Decomp`: exact single-perturbation Taylor matching.
* `bchSexticTermLinDiffShiftDecomp`: exact matching of the shifted directional derivative.
* `bchSexticTermMixedDecomp`: exact mixed second-difference matching.
-/

@[expose] public noncomputable section

open Finset FQFP.WordTable

namespace FQFP.BCH

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The sextic component with exactly `k` first-argument perturbation positions. -/
def bchSexticSubsetPiece (k : ℕ) (x V y : A) : A :=
  taylorPiece coefficientScale bchSexticTermTable 0 ![x, y] V k

/-- The first-order directional difference of the sextic polynomial in its first argument. -/
def bchSexticTermLinDiff (x V y : A) : A := bchSexticSubsetPiece 1 x V y

/-- The part of the sextic Taylor remainder containing exactly two perturbation factors. -/
def bchSexticTermTaylor2Remainder2V (x V y : A) : A := bchSexticSubsetPiece 2 x V y

/-- The part of the sextic Taylor remainder containing exactly three perturbation factors. -/
def bchSexticTermTaylor2Remainder3V (x V y : A) : A := bchSexticSubsetPiece 3 x V y

/-- The part of the sextic Taylor remainder containing exactly four perturbation factors. -/
def bchSexticTermTaylor2Remainder4V (x V y : A) : A := bchSexticSubsetPiece 4 x V y

/-- The second-order Taylor remainder: every term of perturbation degree at least two. -/
def bchSexticTermTaylor2Remainder (x V y : A) : A :=
  bchSexticTermTaylor2Remainder2V x V y + bchSexticTermTaylor2Remainder3V x V y +
    bchSexticTermTaylor2Remainder4V x V y

/-- The change of the sextic directional derivative: exactly one `W` and at least one `V`. -/
def bchSexticTermLinDiffShift (x V W y : A) : A :=
  linDiffShift coefficientScale bchSexticTermTable 0 ![x, y] V W

/-- Every sextic BCH word contains at most four positions in its first argument. -/
lemma card_wordPositions_bchSexticTermTable :
    ∀ p ∈ bchSexticTermTable, (wordPositions p.1.get 0).card ≤ 4 := by decide

/-- The sextic component with no perturbation factors is the original polynomial. -/
lemma bchSexticSubsetPiece_zero (x V y : A) :
    bchSexticSubsetPiece 0 x V y = bchSexticTerm x y :=
  taylorPiece_zero _ _ _ _ _

/-- The linear sextic term is additive in its perturbation. -/
lemma bchSexticTermLinDiff_add (x V W y : A) :
    bchSexticTermLinDiff x (V + W) y =
      bchSexticTermLinDiff x V y + bchSexticTermLinDiff x W y :=
  taylorPiece_one_add _ _ _ _ _ _

/-- The linear sextic term respects rational scalar multiplication. -/
lemma bchSexticTermLinDiff_smul (x V y : A) (c : ℚ) :
    bchSexticTermLinDiff x (c • V) y = c • bchSexticTermLinDiff x V y :=
  taylorPiece_one_smul _ _ _ _ _ _

/-- The sextic polynomial at a perturbed input is the sum of all its Taylor components. -/
theorem bchSexticTerm_add_eq_sum_pieces (x V y : A) :
    bchSexticTerm (x + V) y = ∑ k ∈ range 5, bchSexticSubsetPiece k x V y := by
  have hu : Function.update (![x, y] : Fin 2 → A) 0 (x + V) = ![x + V, y] := by
    ext i
    fin_cases i <;> simp
  simpa only [Matrix.cons_val_zero, hu, bchSexticTerm, bchSexticSubsetPiece] using
    eval_update_add_eq_sum_taylorPiece coefficientScale bchSexticTermTable 0 ![x, y] V 4
      card_wordPositions_bchSexticTermTable

end FQFP.BCH

namespace FQFP.BCH

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- **Second-order Taylor matching** for the sextic BCH polynomial. -/
theorem bchSexticTermTaylor2Decomp (x V y : A) :
    bchSexticTerm (x + V) y - bchSexticTerm x y =
      bchSexticTermLinDiff x V y + bchSexticTermTaylor2Remainder x V y := by
  rw [bchSexticTerm_add_eq_sum_pieces]
  simp only [sum_range_succ, sum_range_zero, zero_add, bchSexticSubsetPiece_zero,
    bchSexticTermLinDiff, bchSexticTermTaylor2Remainder, bchSexticTermTaylor2Remainder2V,
    bchSexticTermTaylor2Remainder3V, bchSexticTermTaylor2Remainder4V]
  abel

/-- **Shifted directional derivative matching** for the sextic BCH polynomial. -/
theorem bchSexticTermLinDiffShiftDecomp (x V W y : A) :
    bchSexticTermLinDiff (x + V) W y - bchSexticTermLinDiff x W y =
      bchSexticTermLinDiffShift x V W y := by
  have hu : Function.update (![x, y] : Fin 2 → A) 0 (x + V) = ![x + V, y] := by
    ext i
    fin_cases i <;> simp
  have h := taylorPiece_one_update_add coefficientScale bchSexticTermTable 0 ![x, y] V W
  simp only [Matrix.cons_val_zero, hu] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

/-- **Mixed second-difference matching** through the sextic Taylor remainder. -/
theorem bchSexticTermMixedDecomp (x V W y : A) :
    bchSexticTerm (x + V + W) y - bchSexticTerm (x + V) y -
      bchSexticTerm (x + W) y + bchSexticTerm x y =
      bchSexticTermLinDiffShift x V W y + bchSexticTermTaylor2Remainder (x + V) W y -
        bchSexticTermTaylor2Remainder x W y := by
  have hV := bchSexticTermTaylor2Decomp (x + V) W y
  have h0 := bchSexticTermTaylor2Decomp x W y
  rw [← bchSexticTermLinDiffShiftDecomp]
  calc
    _ = (bchSexticTerm (x + V + W) y - bchSexticTerm (x + V) y) -
        (bchSexticTerm (x + W) y - bchSexticTerm x y) := by abel
    _ = _ := by
      rw [hV, h0]
      abel

end FQFP.BCH
