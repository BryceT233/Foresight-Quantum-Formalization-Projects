/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms

/-!
# Lipschitz bounds for the degree-5 term

The quintic term is Lipschitz in its first argument:
`‖C₅(z,y) - C₅(x,y)‖ ≤ M⁴ ‖z - x‖` with `M = ‖z‖ + ‖x‖ + ‖y‖`.

The proof is arity-free where the source's was not. A group is a `Finset.sum` over word patterns
(`BCHTerms.bchQuinticGroup*Words`), so `WordExpansion.norm_sum_wordEval_diff_le` produces the whole
telescoping bound in one step, with the sharp constant being the total number of `a`-positions in
the group's word list — `10`, `25`, `35`, `5` for the four groups, exactly as in `Lean-BCH`. The
source instead expands each group's difference into one summand per `a`-position and spends a
`calc` block per summand (about 700 lines for the five bounds here).

## Main results

* `norm_bchQuinticGroup{1,4,6,24}_diff_le` — the four groups, constants `10`, `25`, `35`, `5`.
* `norm_bchQuinticTerm_diff_le` — the assembled term, constant `1`:
  `(1/720)·(10 + 4·25 + 6·35 + 24·5) = 440/720 ≤ 1`.

## Implementation notes

`NormOneClass 𝔸` is required, where the source's statements do not need it: it comes from the
word-layer API (`WordExpansion.norm_wordEval_le` and hence `norm_prod_sub_prod_le`), which is stated
for products of arbitrary length and so needs `‖1‖ = 1`. Every declaration in the BCH layer carries
`NormOneClass 𝔸` anyway.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

noncomputable section

section Groups

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-! ### The number of `a`-positions -/

/-- The total number of `a`-positions in the coefficient-1 word list, which is the constant of
`norm_bchQuinticGroup1_diff_le`. -/
private lemma card_sum_bchQuinticGroup1Words :
    (∑ i : Fin 4, (Finset.univ.filter fun j => bchQuinticGroup1Words i j).card) = 10 := by
  decide

/-- The total number of `a`-positions in the coefficient-4 word list. -/
private lemma card_sum_bchQuinticGroup4Words :
    (∑ i : Fin 10, (Finset.univ.filter fun j => bchQuinticGroup4Words i j).card) = 25 := by
  decide

/-- The total number of `a`-positions in the coefficient-6 word list. -/
private lemma card_sum_bchQuinticGroup6Words :
    (∑ i : Fin 14, (Finset.univ.filter fun j => bchQuinticGroup6Words i j).card) = 35 := by
  decide

/-- The total number of `a`-positions in the coefficient-24 word list. -/
private lemma card_sum_bchQuinticGroup24Words :
    (∑ i : Fin 2, (Finset.univ.filter fun j => bchQuinticGroup24Words i j).card) = 5 := by
  decide

/-! ### The four groups -/

/-- **Lipschitz bound for `bchQuinticGroup1` in its first argument**:
`‖G₁(z,y) - G₁(x,y)‖ ≤ 10 M⁴ ‖z - x‖` with `M = ‖z‖ + ‖x‖ + ‖y‖`. -/
theorem norm_bchQuinticGroup1_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup1 z y - bchQuinticGroup1 x y‖ ≤ 10 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have hcard : (∑ i : Fin 4, ((Finset.univ.filter fun j => bchQuinticGroup1Words i j).card : ℝ))
      = 10 := by
    rw [← Nat.cast_sum, card_sum_bchQuinticGroup1Words]
    norm_num
  unfold bchQuinticGroup1
  calc ‖∑ i, (List.ofFn (wordEval (bchQuinticGroup1Words i) z y)).prod
        - ∑ i, (List.ofFn (wordEval (bchQuinticGroup1Words i) x y)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => bchQuinticGroup1Words i j).card : ℝ))
          * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
        norm_sum_wordEval_diff_le (M := ‖z‖ + ‖x‖ + ‖y‖) _ z x y
          (by linarith [norm_nonneg x, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg x]) (by positivity)
    _ = 10 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by rw [hcard]

/-- **Lipschitz bound for `bchQuinticGroup4` in its first argument**: `≤ 25 M⁴ ‖z - x‖`. -/
theorem norm_bchQuinticGroup4_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup4 z y - bchQuinticGroup4 x y‖ ≤ 25 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have hcard : (∑ i : Fin 10, ((Finset.univ.filter fun j => bchQuinticGroup4Words i j).card : ℝ))
      = 25 := by
    rw [← Nat.cast_sum, card_sum_bchQuinticGroup4Words]
    norm_num
  unfold bchQuinticGroup4
  calc ‖∑ i, (List.ofFn (wordEval (bchQuinticGroup4Words i) z y)).prod
        - ∑ i, (List.ofFn (wordEval (bchQuinticGroup4Words i) x y)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => bchQuinticGroup4Words i j).card : ℝ))
          * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
        norm_sum_wordEval_diff_le (M := ‖z‖ + ‖x‖ + ‖y‖) _ z x y
          (by linarith [norm_nonneg x, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg x]) (by positivity)
    _ = 25 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by rw [hcard]

/-- **Lipschitz bound for `bchQuinticGroup6` in its first argument**: `≤ 35 M⁴ ‖z - x‖`.

The source proves this one with `set_option maxHeartbeats 3200000`; the arity-free proof needs no
bump, since the 35 telescoping summands are never written down. -/
theorem norm_bchQuinticGroup6_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup6 z y - bchQuinticGroup6 x y‖ ≤ 35 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have hcard : (∑ i : Fin 14, ((Finset.univ.filter fun j => bchQuinticGroup6Words i j).card : ℝ))
      = 35 := by
    rw [← Nat.cast_sum, card_sum_bchQuinticGroup6Words]
    norm_num
  unfold bchQuinticGroup6
  calc ‖∑ i, (List.ofFn (wordEval (bchQuinticGroup6Words i) z y)).prod
        - ∑ i, (List.ofFn (wordEval (bchQuinticGroup6Words i) x y)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => bchQuinticGroup6Words i j).card : ℝ))
          * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
        norm_sum_wordEval_diff_le (M := ‖z‖ + ‖x‖ + ‖y‖) _ z x y
          (by linarith [norm_nonneg x, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg x]) (by positivity)
    _ = 35 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by rw [hcard]

/-- **Lipschitz bound for `bchQuinticGroup24` in its first argument**: `≤ 5 M⁴ ‖z - x‖`. -/
theorem norm_bchQuinticGroup24_diff_le (z x y : 𝔸) :
    ‖bchQuinticGroup24 z y - bchQuinticGroup24 x y‖ ≤ 5 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  have hcard : (∑ i : Fin 2, ((Finset.univ.filter fun j => bchQuinticGroup24Words i j).card : ℝ))
      = 5 := by
    rw [← Nat.cast_sum, card_sum_bchQuinticGroup24Words]
    norm_num
  unfold bchQuinticGroup24
  calc ‖∑ i, (List.ofFn (wordEval (bchQuinticGroup24Words i) z y)).prod
        - ∑ i, (List.ofFn (wordEval (bchQuinticGroup24Words i) x y)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => bchQuinticGroup24Words i j).card : ℝ))
          * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ :=
        norm_sum_wordEval_diff_le (M := ‖z‖ + ‖x‖ + ‖y‖) _ z x y
          (by linarith [norm_nonneg x, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg y])
          (by linarith [norm_nonneg z, norm_nonneg x]) (by positivity)
    _ = 5 * (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by rw [hcard]

end Groups

section Term

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]

/-- **Lipschitz bound for `bchQuinticTerm`**: `‖C₅(z,y) - C₅(x,y)‖ ≤ M⁴ ‖z - x‖` with
`M = ‖z‖ + ‖x‖ + ‖y‖`.

The four group constants enter with the weights of `bchQuinticTerm`:
`(1/720)·(1·10 + 4·25 + 6·35 + 24·5) = 440/720 ≤ 1`, which is why the constant of the assembled term
is `1` while the group constants are larger. -/
theorem norm_bchQuinticTerm_diff_le (z x y : 𝔸) :
    ‖bchQuinticTerm z y - bchQuinticTerm x y‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 4 * ‖z - x‖ := by
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM
  set d := ‖z - x‖ with hd
  have hb1 : ‖bchQuinticGroup1 z y - bchQuinticGroup1 x y‖ ≤ 10 * M ^ 4 * d := by
    rw [hM, hd]; exact norm_bchQuinticGroup1_diff_le z x y
  have hn1 : ‖-(bchQuinticGroup1 z y - bchQuinticGroup1 x y)‖ ≤ 10 * M ^ 4 * d := by
    rw [norm_neg]; exact hb1
  have hb4 : ‖bchQuinticGroup4 z y - bchQuinticGroup4 x y‖ ≤ 25 * M ^ 4 * d := by
    rw [hM, hd]; exact norm_bchQuinticGroup4_diff_le z x y
  have hb6 : ‖bchQuinticGroup6 z y - bchQuinticGroup6 x y‖ ≤ 35 * M ^ 4 * d := by
    rw [hM, hd]; exact norm_bchQuinticGroup6_diff_le z x y
  have hb24 : ‖bchQuinticGroup24 z y - bchQuinticGroup24 x y‖ ≤ 5 * M ^ 4 * d := by
    rw [hM, hd]; exact norm_bchQuinticGroup24_diff_le z x y
  have hs4 : ‖(4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y)‖ ≤ 100 * M ^ 4 * d := by
    calc ‖(4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y)‖
        ≤ ‖(4 : ℚ)‖ * ‖bchQuinticGroup4 z y - bchQuinticGroup4 x y‖ := norm_smul_le _ _
      _ = 4 * ‖bchQuinticGroup4 z y - bchQuinticGroup4 x y‖ := by rw [norm_four_rat]
      _ ≤ 4 * (25 * M ^ 4 * d) := mul_le_mul_of_nonneg_left hb4 (by norm_num)
      _ = 100 * M ^ 4 * d := by ring
  have hs6 : ‖(6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y)‖ ≤ 210 * M ^ 4 * d := by
    calc ‖(6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y)‖
        ≤ ‖(6 : ℚ)‖ * ‖bchQuinticGroup6 z y - bchQuinticGroup6 x y‖ := norm_smul_le _ _
      _ = 6 * ‖bchQuinticGroup6 z y - bchQuinticGroup6 x y‖ := by rw [norm_six_rat]
      _ ≤ 6 * (35 * M ^ 4 * d) := mul_le_mul_of_nonneg_left hb6 (by norm_num)
      _ = 210 * M ^ 4 * d := by ring
  have hs24 : ‖(24 : ℚ) • (bchQuinticGroup24 z y - bchQuinticGroup24 x y)‖ ≤ 120 * M ^ 4 * d := by
    calc ‖(24 : ℚ) • (bchQuinticGroup24 z y - bchQuinticGroup24 x y)‖
        ≤ ‖(24 : ℚ)‖ * ‖bchQuinticGroup24 z y - bchQuinticGroup24 x y‖ := norm_smul_le _ _
      _ = 24 * ‖bchQuinticGroup24 z y - bchQuinticGroup24 x y‖ := by rw [norm_twentyFour_rat]
      _ ≤ 24 * (5 * M ^ 4 * d) := mul_le_mul_of_nonneg_left hb24 (by norm_num)
      _ = 120 * M ^ 4 * d := by ring
  have htel : bchQuinticTerm z y - bchQuinticTerm x y =
      (720 : ℚ)⁻¹ • (-(bchQuinticGroup1 z y - bchQuinticGroup1 x y)
        + (4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
        - (6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y)
        + (24 : ℚ) • (bchQuinticGroup24 z y - bchQuinticGroup24 x y)) := by
    unfold bchQuinticTerm
    module
  rw [htel]
  set X : 𝔸 := -(bchQuinticGroup1 z y - bchQuinticGroup1 x y)
      + (4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
      - (6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y)
      + (24 : ℚ) • (bchQuinticGroup24 z y - bchQuinticGroup24 x y) with hX
  have hinner : ‖X‖ ≤ 440 * M ^ 4 * d := by
    rw [hX]
    have s1 := norm_add_le (-(bchQuinticGroup1 z y - bchQuinticGroup1 x y)
          + (4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
          - (6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y))
        ((24 : ℚ) • (bchQuinticGroup24 z y - bchQuinticGroup24 x y))
    have s2 := norm_sub_le (-(bchQuinticGroup1 z y - bchQuinticGroup1 x y)
          + (4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y))
        ((6 : ℚ) • (bchQuinticGroup6 z y - bchQuinticGroup6 x y))
    have s3 := norm_add_le (-(bchQuinticGroup1 z y - bchQuinticGroup1 x y))
        ((4 : ℚ) • (bchQuinticGroup4 z y - bchQuinticGroup4 x y))
    linarith only [s1, s2, s3, hn1, hs4, hs6, hs24]
  have h720 : ‖((720 : ℚ)⁻¹)‖ = 1 / 720 := by
    rw [norm_inv, norm_sevenTwenty_rat]
    norm_num
  calc ‖(720 : ℚ)⁻¹ • X‖ ≤ ‖((720 : ℚ)⁻¹)‖ * ‖X‖ := norm_smul_le _ _
    _ = (1 / 720) * ‖X‖ := by rw [h720]
    _ ≤ (1 / 720) * (440 * M ^ 4 * d) := mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = (440 / 720) * (M ^ 4 * d) := by ring
    _ ≤ M ^ 4 * d := by
        refine mul_le_of_le_one_left ?_ (by norm_num)
        positivity

end Term

end

end FQFP.BCH
