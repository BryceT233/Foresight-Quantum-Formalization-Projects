/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.QuinticTaylor
public import FQFP.Analysis.Normed.Algebra.WordTaylor
public import FQFP.Analysis.Normed.Algebra.BinaryWord

/-!
# Difference and Taylor bounds for the quintic BCH term

This file estimates changes in the homogeneous quintic BCH polynomial. The first-order
Lipschitz estimates count occurrences in the four binary word groups. The Taylor remainder
uses the weighted substitution counts of the quintic coefficient table. Its decomposition is in
`FQFP.Algebra.Lie.BCH.Associative.QuinticTaylor`.

## Main results

* `norm_bchQuinticGroup1_diff_le` and the other three group estimates.
* `norm_bchQuinticTerm_diff_le`: Lipschitz bound with constant `1`.
* `norm_bchQuinticTermTaylor2Remainder2V_le` and its `3V` and `4V` counterparts.
* `norm_bchQuinticTermTaylor2Remainder_le`: the bound `(2430/720) M³ ‖V‖²`.

The norm estimates use positive-length products and require no normalization of the norm
of the identity. The Taylor estimates retain the source constants `1680/720`, `720/720`
and `30/720`, though the word counts give the sharper constants `384/720`, `136/720`
and `16/720`.
-/

@[expose] public noncomputable section

open Finset FQFP.WordTable

namespace FQFP.BCH

/-- **The bracket bound**: the four groups at their coefficients `-1`, `4`, `-6`, `24`. -/
lemma norm_bchQuinticBracket_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (v1 v4 v6 v24 : 𝔸) :
    ‖bchQuinticBracket v1 v4 v6 v24‖ ≤ ‖v1‖ + 4 * ‖v4‖ + 6 * ‖v6‖ + 24 * ‖v24‖ := by
  have h := norm_add_le_of_le
    (norm_sub_le_of_le (norm_add_le (-v1) ((4 : ℚ) • v4)) (le_refl ‖(6 : ℚ) • v6‖))
    (le_refl ‖(24 : ℚ) • v24‖)
  simpa only [bchQuinticBracket, norm_neg, norm_smul, ← Rat.norm_cast_real, Rat.cast_ofNat,
    Real.norm_ofNat] using h

/-- Combine the four group estimates at their BCH coefficients, including the factor `1/720`. -/
lemma norm_inv_smul_bchQuinticBracket_le_of_le {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    {v1 v4 v6 v24 : A} {n1 n4 n6 n24 R : ℝ}
    (h1 : ‖v1‖ ≤ n1 * R) (h4 : ‖v4‖ ≤ n4 * R) (h6 : ‖v6‖ ≤ n6 * R)
    (h24 : ‖v24‖ ≤ n24 * R) :
    ‖(720 : ℚ)⁻¹ • bchQuinticBracket v1 v4 v6 v24‖ ≤
      ((n1 + 4 * n4 + 6 * n6 + 24 * n24) / 720) * R := by
  have h := norm_bchQuinticBracket_le v1 v4 v6 v24
  rw [norm_smul, norm_inv, ← Rat.norm_cast_real]
  norm_num only [Rat.cast_ofNat, Real.norm_ofNat]
  linarith only [h, h1, h4, h6, h24]

/-- The Lipschitz constant of a quintic word group counts its `a`-positions. -/
private lemma norm_quintic_group_diff_le {𝔸 : Type*} [NormedRing 𝔸] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (N : ℕ)
    (hN : (∑ i, (Finset.univ.filter fun j ↦ words i j = 0).card) = N)
    (z x y : 𝔸) :
    ‖∑ i, ((List.ofFn (words i)).map ![z, y]).prod -
      ∑ i, ((List.ofFn (words i)).map ![x, y]).prod‖ ≤
      N * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have hz : ‖z‖ ≤ ‖z‖ + ‖x‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg y]
  have hx : ‖x‖ ≤ ‖z‖ + ‖x‖ + ‖y‖ := by
    linarith [norm_nonneg z, norm_nonneg y]
  have hy : ‖y‖ ≤ ‖z‖ + ‖x‖ + ‖y‖ := by
    linarith [norm_nonneg z, norm_nonneg x]
  simpa only [List.map_ofFn, Function.comp_def, ← Nat.cast_sum, hN] using
    norm_sum_binWord_diff_le words z x y hz hx hy (by positivity)

section Groups

variable {𝔸 : Type*} [NormedRing 𝔸]

/-! ### The four groups -/

/-- **Lipschitz bound for `bchQuinticGroup1` in its first argument**:
`‖G₁(z,y) - G₁(x,y)‖ ≤ 10 M⁴ ‖z - x‖` with `M = ‖z‖ + ‖x‖ + ‖y‖`. -/
theorem norm_bchQuinticGroup1_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup1 z y - bchQuinticGroup1 x y‖ ≤ 10 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
  norm_quintic_group_diff_le bchQuinticGroup1Words 10
    (by decide) z x y

/-- **Lipschitz bound for `bchQuinticGroup4` in its first argument**: `≤ 25 M⁴ ‖z - x‖`. -/
theorem norm_bchQuinticGroup4_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup4 z y - bchQuinticGroup4 x y‖ ≤ 25 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
  norm_quintic_group_diff_le bchQuinticGroup4Words 25
    (by decide) z x y

/-- **Lipschitz bound for `bchQuinticGroup6` in its first argument**: `≤ 35 M⁴ ‖z - x‖`. -/
theorem norm_bchQuinticGroup6_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup6 z y - bchQuinticGroup6 x y‖ ≤ 35 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
  norm_quintic_group_diff_le bchQuinticGroup6Words 35
    (by decide) z x y

/-- **Lipschitz bound for `bchQuinticGroup24` in its first argument**: `≤ 5 M⁴ ‖z - x‖`. -/
theorem norm_bchQuinticGroup24_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup24 z y - bchQuinticGroup24 x y‖ ≤ 5 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
  norm_quintic_group_diff_le bchQuinticGroup24Words 5
    (by decide) z x y

end Groups

section Term

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- **Lipschitz bound for `bchQuinticTerm`**: `‖C₅(z,y) - C₅(x,y)‖ ≤ M⁴ ‖z - x‖` with
`M = ‖z‖ + ‖x‖ + ‖y‖`.

The four group constants enter with the weights of `bchQuinticTerm`:
`(1/720)·(1·10 + 4·25 + 6·35 + 24·5) = 440/720 ≤ 1`, which is why the constant of the assembled term
is `1` while the group constants are larger. -/
theorem norm_bchQuinticTerm_diff_le (z x y : 𝔸) :
    ‖bchQuinticTerm z y - bchQuinticTerm x y‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  let R := (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖
  have htel : bchQuinticTerm z y - bchQuinticTerm x y = (720 : ℚ)⁻¹ •
      bchQuinticBracket (bchQuinticGroup1 z y - bchQuinticGroup1 x y)
        (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
        (bchQuinticGroup6 z y - bchQuinticGroup6 x y)
        (bchQuinticGroup24 z y - bchQuinticGroup24 x y) := by
    unfold bchQuinticTerm bchQuinticBracket
    module
  rw [htel]
  apply (norm_inv_smul_bchQuinticBracket_le_of_le (R := R) (n1 := 10) (n4 := 25)
    (n6 := 35) (n24 := 5) ?_ ?_ ?_ ?_).trans (mul_le_of_le_one_left (by positivity) (by norm_num))
  · simpa only [R, mul_assoc] using norm_bchQuinticGroup1_diff_le z x y
  · simpa only [R, mul_assoc] using norm_bchQuinticGroup4_diff_le z x y
  · simpa only [R, mul_assoc] using norm_bchQuinticGroup6_diff_le z x y
  · simpa only [R, mul_assoc] using norm_bchQuinticGroup24_diff_le z x y

end Term

/-! ### Taylor component bounds -/

/-- Numerators of the bounds for the components with two, three and four perturbations. -/
private def quinticRemainderNumerator : Fin 3 → ℕ := ![1680, 720, 30]

private lemma quintic_taylorWeight_le (i : Fin 3) :
    taylorWeight coefficientScale bchQuinticTermTable 0 (i + 2 : ℕ) ≤
      (quinticRemainderNumerator i : ℝ) / 720 := by
  simp only [taylorWeight, card_wordPositions_get, List.sum_map_norm_mul_natCast]
  have h : (bchQuinticTermTable.map fun p ↦
      |(p.2 : ℚ) / coefficientScale ^ p.1.length| * (p.1.count 0).choose (i + 2 : ℕ)).sum ≤
      (quinticRemainderNumerator i : ℚ) / 720 := by
    fin_cases i <;> decide +kernel
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 h

private lemma norm_quinticSubsetPiece_le_of_le {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    (i : Fin 3) (x V y : A) {M Vn : ℝ}
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticSubsetPiece (i + 2 : ℕ) x V y‖ ≤
      (quinticRemainderNumerator i : ℝ) / 720 * Vn ^ 2 * M ^ 3 := by
  have hM := (norm_nonneg V).trans hVM
  rw [bchQuinticSubsetPiece_eq_taylorPiece, mul_assoc]
  apply (norm_taylorPiece_le_of_le coefficientScale bchQuinticTermTable 0 ![x, y] V
    (i + 2) 5 2 (by decide) (by lia) (by have := i.isLt; lia) (by decide +kernel)
    (fun p _ j ↦ norm_pair_le x y hx hy (p.1.get j)) hVM hV).trans
  exact mul_le_mul_of_nonneg_right (quintic_taylorWeight_le i) (by positivity)

private lemma norm_quinticSubsetPiece_le {A : Type*} [NormedRing A] [NormedAlgebra ℚ A]
    (i : Fin 3) (x V y : A) :
    ‖bchQuinticSubsetPiece (i + 2 : ℕ) x V y‖ ≤
      (quinticRemainderNumerator i : ℝ) / 720 * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  rw [mul_comm (_ ^ 3), ← mul_assoc]
  apply norm_quinticSubsetPiece_le_of_le
  all_goals linarith only [norm_nonneg x, norm_nonneg V, norm_nonneg y]

/-- Bound for the `2V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder2V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder2V x V y‖ ≤ (1680 / 720 : ℝ) * Vn ^ 2 * M ^ 3 :=
  norm_quinticSubsetPiece_le_of_le 0 x V y hx hV hy hVM

/-- The `2V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder2V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder2V x V y‖
      ≤ (1680 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_quinticSubsetPiece_le 0 x V y

/-- Bound for the `3V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder3V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder3V x V y‖ ≤ (720 / 720 : ℝ) * Vn ^ 2 * M ^ 3 :=
  norm_quinticSubsetPiece_le_of_le 1 x V y hx hV hy hVM

/-- The `3V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder3V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder3V x V y‖
      ≤ (720 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_quinticSubsetPiece_le 1 x V y

/-- Bound for the `4V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder4V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder4V x V y‖ ≤ (30 / 720 : ℝ) * Vn ^ 2 * M ^ 3 :=
  norm_quinticSubsetPiece_le_of_le 2 x V y hx hV hy hVM

/-- The `4V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder4V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder4V x V y‖
      ≤ (30 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_quinticSubsetPiece_le 2 x V y

/-- **Norm bound for the second-order Taylor remainder**:
`‖C₅(x+V,y) - C₅(x,y) - linDiff‖ ≤ (2430/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`.

`(1680 + 720 + 30)/720 = 2430/720` is the sum of the three pieces' constants. -/
theorem norm_bchQuinticTermTaylor2Remainder_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder x V y‖ ≤
      (2430 / 720 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2 := by
  apply (norm_add_le_of_le (norm_add_le_of_le (norm_bchQuinticTermTaylor2Remainder2V_le x V y)
    (norm_bchQuinticTermTaylor2Remainder3V_le x V y))
    (norm_bchQuinticTermTaylor2Remainder4V_le x V y)).trans_eq
  ring

end FQFP.BCH
