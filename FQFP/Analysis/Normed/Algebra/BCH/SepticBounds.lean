/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.SepticTaylor
public import FQFP.Analysis.Normed.Algebra.WordTaylor

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

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]

/-- **Second-order Taylor remainder bound** at an independent perturbation bound.
Only the actual perturbation norm, not `Vn`, must be at most `M`. -/
theorem norm_bchSepticTermTaylor2Remainder_le_of_le (x V y : A) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖bchSepticTermTaylor2Remainder x V y‖ ≤
      (125352 / 30240 : ℝ) * M ^ 5 * Vn ^ 2 := by
  have hweights := sum_taylorWeight_le_of_rat coefficientScale bchSepticTermTable 0
    (range 5) (fun i ↦ i + 2) (125352 / 30240) (by decide +kernel)
  simpa [bchSepticTermTaylor2Remainder, bchSepticSubsetPiece] using
    norm_sum_taylorPiece_pair_le coefficientScale bchSepticTermTable x V y 6 2
      (by decide) (by decide) septic_length hx hy hVM hV hweights

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
  have hweights := sum_taylorWeight_le_of_rat coefficientScale bchSepticTermTable 0
    (range 6) (fun i ↦ i + 1) (7) (by decide +kernel)
  exact norm_eval_pair_sub_eval_pair_le coefficientScale bchSepticTermTable z x y 6
    (by decide) (by decide) septic_length card_wordPositions_bchSepticTermTable hweights

end FQFP.BCH
