/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.SepticTaylor
public import FQFP.BCH.Analysis.WordTaylor

/-!
# Taylor bounds for the septic BCH polynomial

The existing septic coefficient table supplies the same substitution pieces used in its
algebraic expansion. Their absolute coefficient budgets control the second-order remainder
and the first-argument Lipschitz estimate. The bounds retain the source coefficients
`125352/30240` and `7`, respectively.

## Main results

* `norm_bchSepticTermTaylor2Remainder_le_of_le`: an independent perturbation bound.
* `norm_bchSepticTermTaylor2Remainder_le`: the source second-order Taylor bound.
* `norm_bchSepticTerm_diff_le`: the source first-argument Lipschitz bound.

The independent perturbation bound need not lie below the common scale on actual input norms.
No completeness, identity norm, or smallness condition is required.
-/

@[expose] public noncomputable section

open Finset FQFP.WordTable

namespace FQFP.BCH

private lemma septic_length : ∀ p ∈ bchSepticTermTable, p.1.length = 7 := by
  have hall : bchSepticTermTable.all (fun p ↦ decide (p.1.length = 7)) = true := by
    decide +kernel
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp hall p hp)

private lemma septic_taylor_weight (k : Fin 7) :
    taylorWeight coefficientScale bchSepticTermTable 0 k =
      (![2976, 10416, 14568, 10380, 3968, 780, 64] k : ℝ) / 30240 := by
  simp only [taylorWeight, card_wordPositions_get]
  rw [List.sum_map_norm_mul_natCast]
  have h : (bchSepticTermTable.map fun p ↦
      |(p.2 : ℚ) / coefficientScale ^ p.1.length| * (p.1.count 0).choose k).sum =
      (![2976, 10416, 14568, 10380, 3968, 780, 64] k : ℚ) / 30240 := by
    fin_cases k <;> decide +kernel
  convert congrArg (fun q : ℚ ↦ (q : ℝ)) h using 1
  fin_cases k <;> norm_num

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- **Second-order Taylor remainder bound** at an independent perturbation bound.
Only the actual perturbation norm, not `Vn`, must be at most `M`. -/
theorem norm_bchSepticTermTaylor2Remainder_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSepticTermTaylor2Remainder x V y‖ ≤
      (125352 / 30240 : ℝ) * M ^ 5 * Vn ^ 2 := by
  have hweights : ∑ i ∈ range 5,
      taylorWeight coefficientScale bchSepticTermTable 0 (i + 2) ≤
        (125352 / 30240 : ℝ) := by
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [septic_taylor_weight ⟨2, by decide⟩, septic_taylor_weight ⟨3, by decide⟩,
      septic_taylor_weight ⟨4, by decide⟩, septic_taylor_weight ⟨5, by decide⟩,
      septic_taylor_weight ⟨6, by decide⟩]
    norm_num
  have h := norm_sum_taylorPiece_le_of_le coefficientScale bchSepticTermTable 0 ![x, y]
    V (range 5) (fun i ↦ i + 2) 7 2 (by decide)
    (by
      intro i _
      lia) (by
      intro i hi
      simp only [mem_range] at hi
      lia) septic_length
    (fun p _ i ↦ norm_pair_le x y hx hy (p.1.get i)) hVM hV hweights
  simpa [bchSepticTermTaylor2Remainder, bchSepticSubsetPiece,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- **Second-order Taylor remainder bound** with the source coefficient `125352/30240`. -/
theorem norm_bchSepticTermTaylor2Remainder_le (x V y : A) :
    ‖bchSepticTermTaylor2Remainder x V y‖ ≤
      (125352 / 30240 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 5 * ‖V‖ ^ 2 := by
  apply norm_bchSepticTermTaylor2Remainder_le_of_le
  all_goals linarith only [norm_nonneg x, norm_nonneg V, norm_nonneg y]

/-- **Lipschitz bound** for the septic polynomial in its first argument. -/
theorem norm_bchSepticTerm_diff_le (z x y : A) :
    ‖bchSepticTerm z y - bchSepticTerm x y‖ ≤
      7 * (‖z‖ + ‖x‖ + ‖y‖) ^ 6 * ‖z - x‖ := by
  let M := ‖z‖ + ‖x‖ + ‖y‖
  have hx : ‖x‖ ≤ M := by
    dsimp only [M]
    linarith only [norm_nonneg z, norm_nonneg y]
  have hy : ‖y‖ ≤ M := by
    dsimp only [M]
    linarith only [norm_nonneg z, norm_nonneg x]
  have hVM : ‖z - x‖ ≤ M :=
    (norm_sub_le z x).trans (le_add_of_nonneg_right (norm_nonneg y))
  have hweights : ∑ i ∈ range 6,
      taylorWeight coefficientScale bchSepticTermTable 0 (i + 1) ≤ (7 : ℝ) := by
    simp only [sum_range_succ, sum_range_zero, zero_add]
    rw [septic_taylor_weight ⟨1, by decide⟩, septic_taylor_weight ⟨2, by decide⟩,
      septic_taylor_weight ⟨3, by decide⟩, septic_taylor_weight ⟨4, by decide⟩,
      septic_taylor_weight ⟨5, by decide⟩, septic_taylor_weight ⟨6, by decide⟩]
    norm_num
  have hdecomp : bchSepticTerm z y - bchSepticTerm x y =
      ∑ i ∈ range 6, bchSepticSubsetPiece (i + 1) x (z - x) y := by
    have hexp := bchSepticTerm_add_eq_sum_pieces x (z - x) y
    rw [show x + (z - x) = z by abel] at hexp
    rw [hexp, sum_range_succ', bchSepticSubsetPiece_zero, add_sub_cancel_right]
  rw [hdecomp]
  have h := norm_sum_taylorPiece_le_of_le coefficientScale bchSepticTermTable 0 ![x, y]
    (z - x) (range 6) (fun i ↦ i + 1) 7 1 (by decide)
    (by
      intro i _
      lia) (by
      intro i hi
      simp only [mem_range] at hi
      lia) septic_length
    (fun p _ i ↦ norm_pair_le x y hx hy (p.1.get i)) hVM le_rfl hweights
  simpa [M, bchSepticSubsetPiece, mul_comm, mul_left_comm, mul_assoc] using h

end FQFP.BCH
