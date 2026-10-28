/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.QuinticTaylor
public import FQFP.Analysis.Normed.Algebra.Word
public import FQFP.Analysis.Normed.Algebra.BinaryWord

/-!
# Difference and Taylor bounds for the quintic BCH term

This file estimates changes in the homogeneous quintic BCH polynomial. The first-order
Lipschitz estimates and the second-order Taylor remainder use the same binary word groups
and the same weighted bracket norm bound. Algebraic Taylor decompositions are defined in
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

open Finset

namespace FQFP.BCH

/-- **The bracket bound**: the four groups at their coefficients `-1`, `4`, `-6`, `24`. -/
lemma norm_bchQuinticBracket_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (v1 v4 v6 v24 : 𝔸) :
    ‖bchQuinticBracket v1 v4 v6 v24‖ ≤ ‖v1‖ + 4 * ‖v4‖ + 6 * ‖v6‖ + 24 * ‖v24‖ := by
  have h4 : ‖(4 : ℚ) • v4‖ ≤ 4 * ‖v4‖ := by
    calc ‖(4 : ℚ) • v4‖ ≤ ‖(4 : ℚ)‖ * ‖v4‖ := norm_smul_le _ _
      _ = 4 * ‖v4‖ := by simp [← Rat.norm_cast_real]
  have h6 : ‖(6 : ℚ) • v6‖ ≤ 6 * ‖v6‖ := by
    calc ‖(6 : ℚ) • v6‖ ≤ ‖(6 : ℚ)‖ * ‖v6‖ := norm_smul_le _ _
      _ = 6 * ‖v6‖ := by simp [← Rat.norm_cast_real]
  have h24 : ‖(24 : ℚ) • v24‖ ≤ 24 * ‖v24‖ := by
    calc ‖(24 : ℚ) • v24‖ ≤ ‖(24 : ℚ)‖ * ‖v24‖ := norm_smul_le _ _
      _ = 24 * ‖v24‖ := by simp [← Rat.norm_cast_real]
  simpa only [bchQuinticBracket, norm_neg] using
    norm_add_le_of_le
      (norm_sub_le_of_le (norm_add_le_of_le (le_refl ‖-v1‖) h4) h6) h24

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
  let M := ‖z‖ + ‖x‖ + ‖y‖
  let d := ‖z - x‖
  have hinner : ‖bchQuinticBracket
      (bchQuinticGroup1 z y - bchQuinticGroup1 x y)
      (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
      (bchQuinticGroup6 z y - bchQuinticGroup6 x y)
      (bchQuinticGroup24 z y - bchQuinticGroup24 x y)‖ ≤ 440 * M ^ 4 * d := by
    apply (norm_bchQuinticBracket_le _ _ _ _).trans
    have h1 := norm_bchQuinticGroup1_diff_le z x y
    have h4 := norm_bchQuinticGroup4_diff_le z x y
    have h6 := norm_bchQuinticGroup6_diff_le z x y
    have h24 := norm_bchQuinticGroup24_diff_le z x y
    dsimp only [M, d]
    linarith only [h1, h4, h6, h24]
  have htel : bchQuinticTerm z y - bchQuinticTerm x y = (720 : ℚ)⁻¹ •
      bchQuinticBracket (bchQuinticGroup1 z y - bchQuinticGroup1 x y)
        (bchQuinticGroup4 z y - bchQuinticGroup4 x y)
        (bchQuinticGroup6 z y - bchQuinticGroup6 x y)
        (bchQuinticGroup24 z y - bchQuinticGroup24 x y) := by
    unfold bchQuinticTerm bchQuinticBracket
    module
  rw [htel]
  calc
    _ ≤ ‖(720 : ℚ)⁻¹‖ * (440 * M ^ 4 * d) :=
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg _))
    _ = (440 / 720) * (M ^ 4 * d) := by
      rw [← Rat.norm_cast_real]
      norm_num
      ring
    _ ≤ M ^ 4 * d := mul_le_of_le_one_left (by positivity) (by norm_num)

end Term

/-! ### The norm bounds

Each piece is bounded in three steps, none of which needs a case analysis on the words:

1. every substituted word of the `k`-th piece carries exactly `k` letters `V` and `5 - k` letters
   from `{x, y}`. The positive-length bound `norm_prod_piecewise_le_of_pos` gives
   `M ^ (5 - k) * ‖V‖ ^ k`;
2. the number of such words in a group is `∑ i, (#a-positions).choose k`, evaluated by `decide`;
3. use `‖V‖ ≤ M` to obtain `M ^ 3 * ‖V‖ ^ 2`, then enlarge `‖V‖` to an independent
   bound `Vn`. This does not require `Vn ≤ M`.

The resulting constants (`384/720`, `136/720`, `16/720` for the three pieces) are sharper than the
source's `1680/720`, `720/720`, `30/720`, which are kept in the statements. -/

/-- **The group bound**: a group's `k`-subset piece is bounded by its number of terms times
`M ^ (5 - k) * Vn ^ k`. -/
private lemma norm_bchQuinticGroupSubsets_le {𝔸 : Type*} [NormedRing 𝔸] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k : ℕ) (x V y : 𝔸) {M Vn : ℝ} (hx : ‖x‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) :
    ‖bchQuinticGroupSubsets words k x V y‖
      ≤ (∑ i : Fin m, (((wordPositions (words i) 0).card).choose k : ℝ))
          * (M ^ (5 - k) * Vn ^ k) := by
  have hxy : ∀ a : Fin 2, ‖![x, y] a‖ ≤ M := by
    intro a
    fin_cases a
    · exact hx
    · exact hy
  calc ‖bchQuinticGroupSubsets words k x V y‖
      ≤ ∑ i : Fin m, ∑ _s ∈ (wordPositions (words i) 0).powersetCard k,
          M ^ (5 - k) * Vn ^ k := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s hs => ?_)
        have hsk : s.card = k := (Finset.mem_powersetCard.mp hs).2
        simpa only [hsk, mul_comm] using
          norm_prod_piecewise_le_of_pos (by norm_num) s (fun _ => V) (fun j => ![x, y] (words i j))
            (fun _ _ => hV) (fun j _ => hxy (words i j))
    _ = (∑ i : Fin m, (((wordPositions (words i) 0).card).choose k : ℝ))
          * (M ^ (5 - k) * Vn ^ k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- The relaxation `M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2` for `2 ≤ k ≤ 5`. -/
private lemma profile_le (M Vn : ℝ) (hM0 : 0 ≤ M) (hVn0 : 0 ≤ Vn) (hVnM : Vn ≤ M) {k : ℕ}
    (hk : 2 ≤ k) (hk5 : k ≤ 5) : M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by lia⟩
  have hj3 : j ≤ 3 := by lia
  have hM : 5 - (j + 2) = 3 - j := by lia
  rw [hM, pow_add]
  calc M ^ (3 - j) * (Vn ^ j * Vn ^ 2)
      ≤ M ^ (3 - j) * (M ^ j * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hVn0 hVnM j) (pow_nonneg hVn0 2))
          (pow_nonneg hM0 (3 - j))
    _ = M ^ 3 * Vn ^ 2 := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj3]

/-- **The piece bound**: if the four groups of the `k`-th piece have `n1`, `n4`, `n6`, `n24` words
respectively and `(n1 + 4n4 + 6n6 + 24n24)/720 ≤ C`, then the piece is bounded by
`C * M ^ 3 * ‖V‖ ^ 2`. -/
private lemma norm_bchQuinticSubsetPiece_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] {k : ℕ} (hk : 2 ≤ k) (hk5 : k ≤ 5)
    {n1 n4 n6 n24 : ℕ}
    (hc1 : (∑ i : Fin 4,
      ((wordPositions (bchQuinticGroup1Words i) 0).card).choose k) = n1)
    (hc4 : (∑ i : Fin 10,
      ((wordPositions (bchQuinticGroup4Words i) 0).card).choose k) = n4)
    (hc6 : (∑ i : Fin 14,
      ((wordPositions (bchQuinticGroup6Words i) 0).card).choose k) = n6)
    (hc24 : (∑ i : Fin 2,
      ((wordPositions (bchQuinticGroup24Words i) 0).card).choose k) = n24)
    {C : ℝ} (hC : ((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) / 720 ≤ C)
    (x V y : 𝔸) (M : ℝ) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticSubsetPiece k x V y‖ ≤ C * (M ^ 3 * ‖V‖ ^ 2) := by
  let Vn := ‖V‖
  have hM0 : 0 ≤ M := (norm_nonneg x).trans hx
  have hVn0 : 0 ≤ Vn := norm_nonneg _
  have hVnM : Vn ≤ M := hVM
  have hV : ‖V‖ ≤ Vn := le_refl _
  have h1 := norm_bchQuinticGroupSubsets_le bchQuinticGroup1Words k x V y hx hV hy
  have h4 := norm_bchQuinticGroupSubsets_le bchQuinticGroup4Words k x V y hx hV hy
  have h6 := norm_bchQuinticGroupSubsets_le bchQuinticGroup6Words k x V y hx hV hy
  have h24 := norm_bchQuinticGroupSubsets_le bchQuinticGroup24Words k x V y hx hV hy
  rw [show (∑ i : Fin 4, (((wordPositions (bchQuinticGroup1Words i) 0).card
      ).choose k : ℝ)) = n1 by rw [← Nat.cast_sum, hc1]] at h1
  rw [show (∑ i : Fin 10, (((wordPositions (bchQuinticGroup4Words i) 0).card
      ).choose k : ℝ)) = n4 by rw [← Nat.cast_sum, hc4]] at h4
  rw [show (∑ i : Fin 14, (((wordPositions (bchQuinticGroup6Words i) 0).card
      ).choose k : ℝ)) = n6 by rw [← Nat.cast_sum, hc6]] at h6
  rw [show (∑ i : Fin 2, (((wordPositions (bchQuinticGroup24Words i) 0).card
      ).choose k : ℝ)) = n24 by rw [← Nat.cast_sum, hc24]] at h24
  have hbr := norm_bchQuinticBracket_le (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)
  have hprof := profile_le M Vn hM0 hVn0 hVnM hk hk5
  have hX : (0 : ℝ) ≤ M ^ 3 * Vn ^ 2 := by positivity
  have h720 : ‖(720 : ℚ)⁻¹‖ = (720 : ℝ)⁻¹ := by
    rw [← Rat.norm_cast_real, Real.norm_eq_abs]
    norm_num
  have hsm : ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * ‖bchQuinticBracket
          (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)‖ := by
    rw [bchQuinticSubsetPiece]
    refine le_trans (norm_smul_le _ _) ?_
    rw [h720]
  have key : ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2)) := by
    refine le_trans hsm (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have b1 : ‖bchQuinticGroupSubsets bchQuinticGroup1Words k x V y‖
        ≤ (n1 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n1))
    have b4 : ‖bchQuinticGroupSubsets bchQuinticGroup4Words k x V y‖
        ≤ (n4 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h4 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n4))
    have b6 : ‖bchQuinticGroupSubsets bchQuinticGroup6Words k x V y‖
        ≤ (n6 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h6 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n6))
    have b24 : ‖bchQuinticGroupSubsets bchQuinticGroup24Words k x V y‖
        ≤ (n24 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h24 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n24))
    calc ‖bchQuinticBracket _ _ _ _‖
        ≤ ‖bchQuinticGroupSubsets bchQuinticGroup1Words k x V y‖
          + 4 * ‖bchQuinticGroupSubsets bchQuinticGroup4Words k x V y‖
          + 6 * ‖bchQuinticGroupSubsets bchQuinticGroup6Words k x V y‖
          + 24 * ‖bchQuinticGroupSubsets bchQuinticGroup24Words k x V y‖ := hbr
      _ ≤ (n1 : ℝ) * (M ^ 3 * Vn ^ 2) + 4 * ((n4 : ℝ) * (M ^ 3 * Vn ^ 2))
          + 6 * ((n6 : ℝ) * (M ^ 3 * Vn ^ 2)) + 24 * ((n24 : ℝ) * (M ^ 3 * Vn ^ 2)) := by
          linarith
      _ = ((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2) := by ring
  calc ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2)) := key
    _ = (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) / 720) * (M ^ 3 * Vn ^ 2) := by ring
    _ ≤ C * (M ^ 3 * Vn ^ 2) := mul_le_mul_of_nonneg_right hC hX

/-- Bound for the `2V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder2V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder2V x V y‖ ≤ (1680 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  calc ‖bchQuinticTermTaylor2Remainder2V x V y‖
      ≤ (1680 / 720 : ℝ) * (M ^ 3 * ‖V‖ ^ 2) :=
        norm_bchQuinticSubsetPiece_le (k := 2) (by norm_num) (by norm_num)
          (n1 := 12) (n4 := 24) (n6 := 30) (n24 := 4)
          (by decide) (by decide) (by decide) (by decide)
          (C := 1680 / 720) (by norm_num) x V y M hx hy hVM
    _ ≤ (1680 / 720 : ℝ) * (M ^ 3 * Vn ^ 2) := by gcongr
    _ = (1680 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by ring

/-- The `2V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder2V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder2V x V y‖
      ≤ (1680 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  have hx : ‖x‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hy : ‖y‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hVM : ‖V‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  simpa only [mul_assoc, mul_comm (‖V‖ ^ 2)] using
    norm_bchQuinticTermTaylor2Remainder2V_le_of_le x V y (‖x‖ + ‖V‖ + ‖y‖) ‖V‖ hx le_rfl hy hVM

/-- Bound for the `3V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder3V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder3V x V y‖ ≤ (720 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  calc ‖bchQuinticTermTaylor2Remainder3V x V y‖
      ≤ (720 / 720 : ℝ) * (M ^ 3 * ‖V‖ ^ 2) :=
        norm_bchQuinticSubsetPiece_le (k := 3) (by norm_num) (by norm_num)
          (n1 := 8) (n4 := 11) (n6 := 10) (n24 := 1)
          (by decide) (by decide) (by decide) (by decide)
          (C := 720 / 720) (by norm_num) x V y M hx hy hVM
    _ ≤ (720 / 720 : ℝ) * (M ^ 3 * Vn ^ 2) := by gcongr
    _ = (720 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by ring

/-- The `3V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder3V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder3V x V y‖
      ≤ (720 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  have hx : ‖x‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hy : ‖y‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hVM : ‖V‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  simpa only [mul_assoc, mul_comm (‖V‖ ^ 2)] using
    norm_bchQuinticTermTaylor2Remainder3V_le_of_le x V y (‖x‖ + ‖V‖ + ‖y‖) ‖V‖ hx le_rfl hy hVM

/-- Bound for the `4V` piece at independent bounds for the base and perturbation.
Only the actual perturbation norm, not its bound `Vn`, must be bounded by `M`. -/
theorem norm_bchQuinticTermTaylor2Remainder4V_le_of_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) (M Vn : ℝ)
    (hx : ‖x‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) :
    ‖bchQuinticTermTaylor2Remainder4V x V y‖ ≤ (30 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  calc ‖bchQuinticTermTaylor2Remainder4V x V y‖
      ≤ (30 / 720 : ℝ) * (M ^ 3 * ‖V‖ ^ 2) :=
        norm_bchQuinticSubsetPiece_le (k := 4) (by norm_num) (by norm_num)
          (n1 := 2) (n4 := 2) (n6 := 1) (n24 := 0)
          (by decide) (by decide) (by decide) (by decide)
          (C := 30 / 720) (by norm_num) x V y M hx hy hVM
    _ ≤ (30 / 720 : ℝ) * (M ^ 3 * Vn ^ 2) := by gcongr
    _ = (30 / 720 : ℝ) * Vn ^ 2 * M ^ 3 := by ring

/-- The `4V` bound with the common scale `‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder4V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder4V x V y‖
      ≤ (30 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  have hx : ‖x‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hy : ‖y‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  have hVM : ‖V‖ ≤ ‖x‖ + ‖V‖ + ‖y‖ := by
    linarith [norm_nonneg x, norm_nonneg V, norm_nonneg y]
  simpa only [mul_assoc, mul_comm (‖V‖ ^ 2)] using
    norm_bchQuinticTermTaylor2Remainder4V_le_of_le x V y (‖x‖ + ‖V‖ + ‖y‖) ‖V‖ hx le_rfl hy hVM

/-- **Norm bound for the second-order Taylor remainder**:
`‖C₅(x+V,y) - C₅(x,y) - linDiff‖ ≤ (2430/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`.

`(1680 + 720 + 30)/720 = 2430/720` is the sum of the three pieces' constants. -/
theorem norm_bchQuinticTermTaylor2Remainder_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder x V y‖ ≤
      (2430 / 720 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2 := by
  have h2 := norm_bchQuinticTermTaylor2Remainder2V_le x V y
  have h3 := norm_bchQuinticTermTaylor2Remainder3V_le x V y
  have h4 := norm_bchQuinticTermTaylor2Remainder4V_le x V y
  have s1 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y +
    bchQuinticTermTaylor2Remainder3V x V y) (bchQuinticTermTaylor2Remainder4V x V y)
  have s2 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y)
    (bchQuinticTermTaylor2Remainder3V x V y)
  have hsum : (2430 / 720 : ℝ) = 1680 / 720 + 720 / 720 + 30 / 720 := by norm_num
  unfold bchQuinticTermTaylor2Remainder
  rw [hsum]
  linarith only [s1, s2, h2, h3, h4]

end FQFP.BCH
