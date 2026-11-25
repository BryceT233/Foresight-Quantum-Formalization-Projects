/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.SexticTaylor
public import FQFP.Analysis.Normed.Algebra.WordTaylor

/-!
# Taylor and mixed difference bounds for the sextic BCH polynomial

The existing sextic table supplies both the Taylor components and their weighted norm budgets.
The second-order remainder retains the source coefficient `3312/1440`; changing the base of
the directional derivative retains `8352/1440`. Independent perturbation bounds may exceed
the common scale on the actual inputs. No completeness or identity norm condition is needed.

## Main results

* `norm_bchSexticTermTaylor2Remainder_le_of_le`: an independent perturbation bound.
* `norm_bchSexticTermTaylor2Remainder_le`: the source second-order Taylor bound.
* `norm_bchSexticTermLinDiffShift_le`: the source derivative-shift bound.
* `norm_bchSexticTermMixedDiff_le`: the mixed difference through its Taylor constituents.
* `norm_bchSexticTerm_diff_le`: the first-argument Lipschitz bound with coefficient `1`.
-/

@[expose] public noncomputable section

open Finset FQFP.WordTable

namespace FQFP.BCH

variable {A : Type*} [NormedRing A]

private lemma sextic_length : ∀ p ∈ bchSexticTermTable, p.1.length = 6 := by decide

variable [NormedAlgebra ℚ A]

private lemma sextic_taylor_weight (k : Fin 5) :
    taylorWeight coefficientScale bchSexticTermTable 0 k =
      (![164, 492, 522, 224, 30] k : ℝ) / 1440 := by
  simp only [taylorWeight, card_wordPositions_get]
  rw [List.sum_map_norm_mul_natCast]
  have h : (bchSexticTermTable.map fun p ↦
      |(p.2 : ℚ) / coefficientScale ^ p.1.length| * (p.1.count 0).choose k).sum =
      (![164, 492, 522, 224, 30] k : ℚ) / 1440 := by
    fin_cases k <;> decide +kernel
  convert congrArg (fun q : ℚ ↦ (q : ℝ)) h using 1
  fin_cases k <;> norm_num

private lemma sextic_shift_weight :
    linDiffShiftWeight coefficientScale bchSexticTermTable 0 = (1836 / 1440 : ℝ) := by
  simp only [linDiffShiftWeight, card_wordPositions_get]
  rw [List.sum_map_norm_mul_natCast]
  have h : (bchSexticTermTable.map fun p ↦
      |(p.2 : ℚ) / coefficientScale ^ p.1.length| *
        (p.1.count 0 * (2 ^ (p.1.count 0 - 1) - 1))).sum = (1836 / 1440 : ℚ) := by
    decide +kernel
  convert congrArg (fun q : ℚ ↦ (q : ℝ)) h using 1 <;> norm_num

private lemma norm_sextic_piece_le (k : Fin 5) (r : ℕ) (hrk : r ≤ k) (C : ℝ)
    (hC : (![164, 492, 522, 224, 30] k : ℝ) / 1440 ≤ C)
    (x V y : A) {M Vn : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M)
    (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSexticSubsetPiece k x V y‖ ≤
      C * (Vn ^ r * M ^ (6 - r)) := by
  have hVn : 0 ≤ Vn := (norm_nonneg V).trans hV
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  apply (norm_taylorPiece_le_of_le coefficientScale bchSexticTermTable 0 ![x, y] V k 6 r
    (by decide) hrk (by
      have := k.isLt
      lia) sextic_length
    (fun p _ i ↦ norm_pair_le x y hx hy (p.1.get i)) hVM hV).trans
  rw [sextic_taylor_weight k]
  exact mul_le_mul_of_nonneg_right hC (by positivity)

/-- **The two-perturbation component bound**, with the source coefficient `2208/1440`. -/
theorem norm_bchSexticTermTaylor2Remainder2V_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSexticTermTaylor2Remainder2V x V y‖ ≤ (2208 / 1440 : ℝ) * Vn ^ 2 * M ^ 4 := by
  simpa [bchSexticTermTaylor2Remainder2V, mul_assoc] using
    norm_sextic_piece_le 2 2 (by decide) (2208 / 1440)
    (by norm_num) x V y hx hy hVM hV

/-- **The three-perturbation component bound**, with the source coefficient `1056/1440`. -/
theorem norm_bchSexticTermTaylor2Remainder3V_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSexticTermTaylor2Remainder3V x V y‖ ≤ (1056 / 1440 : ℝ) * Vn ^ 2 * M ^ 4 := by
  simpa [bchSexticTermTaylor2Remainder3V, mul_assoc] using
    norm_sextic_piece_le 3 2 (by decide) (1056 / 1440)
    (by norm_num) x V y hx hy hVM hV

/-- **The four-perturbation component bound**, with the source coefficient `48/1440`. -/
theorem norm_bchSexticTermTaylor2Remainder4V_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSexticTermTaylor2Remainder4V x V y‖ ≤ (48 / 1440 : ℝ) * Vn ^ 2 * M ^ 4 := by
  simpa [bchSexticTermTaylor2Remainder4V, mul_assoc] using
    norm_sextic_piece_le 4 2 (by decide) (48 / 1440)
    (by norm_num) x V y hx hy hVM hV

/-- **Second-order Taylor remainder bound** at an independent perturbation bound.
Only the actual perturbation norm, not `Vn`, must be at most `M`. -/
theorem norm_bchSexticTermTaylor2Remainder_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSexticTermTaylor2Remainder x V y‖ ≤ (3312 / 1440 : ℝ) * M ^ 4 * Vn ^ 2 := by
  have hweights := sum_taylorWeight_le_of_rat coefficientScale bchSexticTermTable 0
    (range 3) (fun i ↦ i + 2) (3312 / 1440) (by decide +kernel)
  simpa [sum_range_succ, bchSexticTermTaylor2Remainder, bchSexticTermTaylor2Remainder2V,
    bchSexticTermTaylor2Remainder3V, bchSexticTermTaylor2Remainder4V, bchSexticSubsetPiece] using
    norm_sum_taylorPiece_pair_le coefficientScale bchSexticTermTable x V y 4 2
      (by decide) (by decide) sextic_length hx hy hVM hV hweights

/-- **Second-order Taylor remainder bound** with the source coefficient `3312/1440`. -/
theorem norm_bchSexticTermTaylor2Remainder_le (x V y : A) :
    ‖bchSexticTermTaylor2Remainder x V y‖ ≤
      (3312 / 1440 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 4 * ‖V‖ ^ 2 := by
  apply norm_bchSexticTermTaylor2Remainder_le_of_le
  all_goals linarith only [norm_nonneg x, norm_nonneg V, norm_nonneg y]

/-- **Derivative-shift bound** with independent perturbation bounds.
The direction `W` is unrestricted by `M` because it occurs exactly once in each word. -/
theorem norm_bchSexticTermLinDiffShift_le_of_le (x V W y : A) (M Vn Wn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖bchSexticTermLinDiffShift x V W y‖ ≤
      (8352 / 1440 : ℝ) * (Vn * Wn * M ^ 4) := by
  have hVn : 0 ≤ Vn := (norm_nonneg V).trans hV
  have hWn : 0 ≤ Wn := (norm_nonneg W).trans hW
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  have h := norm_linDiffShift_le coefficientScale bchSexticTermTable 0 ![x, y] V W 6
    (by decide) sextic_length (fun p _ i ↦ norm_pair_le x y hx hy (p.1.get i)) hVM hV hW
  rw [sextic_shift_weight] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))

/-- **Derivative-shift bound** with the source coefficient `8352/1440`. -/
theorem norm_bchSexticTermLinDiffShift_le (x V W y : A) :
    ‖bchSexticTermLinDiffShift x V W y‖ ≤
      (8352 / 1440 : ℝ) *
        (‖V‖ * ‖W‖ * (‖x‖ + ‖V‖ + ‖W‖ + ‖y‖) ^ 4) := by
  apply norm_bchSexticTermLinDiffShift_le_of_le
  all_goals linarith only [norm_nonneg x, norm_nonneg V, norm_nonneg W, norm_nonneg y]

/-- **Mixed second-difference norm interface** through the Taylor constituents. -/
theorem norm_bchSexticTermMixedDiff_le (x V W y : A) :
    ‖bchSexticTerm (x + V + W) y - bchSexticTerm (x + V) y -
      bchSexticTerm (x + W) y + bchSexticTerm x y‖ ≤
      ‖bchSexticTermLinDiffShift x V W y‖ +
      ‖bchSexticTermTaylor2Remainder (x + V) W y‖ +
      ‖bchSexticTermTaylor2Remainder x W y‖ := by
  rw [bchSexticTermMixedDecomp]
  exact norm_sub_le_of_le (norm_add_le _ _) le_rfl

/-- **Lipschitz bound** for the sextic polynomial in its first argument. -/
theorem norm_bchSexticTerm_diff_le (z x y : A) :
    ‖bchSexticTerm z y - bchSexticTerm x y‖ ≤
      (‖z‖ + ‖x‖ + ‖y‖) ^ 5 * ‖z - x‖ := by
  have hweights := sum_taylorWeight_le_of_rat coefficientScale bchSexticTermTable 0
    (range 4) (fun i ↦ i + 1) (1) (by decide +kernel)
  simpa only [bchSexticTerm, Rat.cast_one, one_mul] using
    norm_eval_pair_sub_eval_pair_le coefficientScale bchSexticTermTable z x y 4
      (by decide) (by decide) sextic_length card_wordPositions_bchSexticTermTable hweights

end FQFP.BCH
