/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.QuinticMixedTaylor
public import FQFP.Analysis.Normed.Algebra.BCH.QuinticBounds

/-!
# Mixed second-difference bounds for the quintic BCH polynomial

Every term of the higher mixed remainder contains both perturbations and at least three
perturbation positions. Two distinguished factors contribute `‖V‖ * ‖W‖`, a third contributes
`‖V‖ + ‖W‖`, and the two remaining positions are bounded by a common scale `M`.
Counting the same substitution sets used in the algebraic expansion gives the bound.

## Main results

* `norm_bchQuinticTermMixed2Remainder_le_of_le`: independent bounds on the base and perturbations.
* `norm_bchQuinticTermMixed2Remainder_le`: the source bound with coefficient `4488/720`.

The actual perturbation norms must be bounded by `M`; their independent upper bounds
`Vn` and `Wn` need not be. No completeness or normalization of the identity norm is required.
The weighted substitution count is `1040`, which is smaller than the source budget `4488`.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

private lemma mixed_profile_left {M v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvM : v ≤ M) (hwM : w ≤ M) (n p q : ℕ)
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hpq : p + q ≤ n) :
    M ^ (n - (p + q)) * v ^ p * w ^ q ≤ v * w * (v + w) * M ^ (n - 3) := by
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 2 := ⟨p - 2, by lia⟩
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by lia⟩
  have hM : 0 ≤ M := hv.trans hvM
  have hrest : M ^ (n - (i + 2 + (j + 1))) * v ^ i * w ^ j ≤ M ^ (n - 3) := by
    calc
      _ ≤ M ^ (n - (i + 2 + (j + 1))) * M ^ i * M ^ j := by gcongr
      _ = _ := by
        rw [← pow_add, ← pow_add]
        congr 1
        lia
  calc
    _ = (v * w * v) * (M ^ (n - (i + 2 + (j + 1))) * v ^ i * w ^ j) := by
      simp only [pow_add, pow_one]
      ring
    _ ≤ (v * w * (v + w)) * M ^ (n - 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hw) (mul_nonneg hv hw))
        hrest (by positivity) (by positivity)

private lemma mixed_profile {M v w : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvM : v ≤ M) (hwM : w ≤ M) (n p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (h3 : 3 ≤ p + q) (hpq : p + q ≤ n) :
    M ^ (n - (p + q)) * v ^ p * w ^ q ≤ v * w * (v + w) * M ^ (n - 3) := by
  by_cases hp2 : 2 ≤ p
  · exact mixed_profile_left hv hw hvM hwM n p q hp2 hq hpq
  · have hq2 : 2 ≤ q := by lia
    simpa only [add_comm q p, mul_comm, mul_left_comm, mul_assoc, add_comm v w] using
      mixed_profile_left hw hv hwM hvM n q p hq2 hp (by lia)

variable {A : Type*} [NormedRing A]

/-- Choose the perturbed positions in each word, then the positions carrying the first increment. -/
private def mixedGroupCount {m : ℕ} (words : Fin m → Fin 5 → Fin 2) (k p : ℕ) : ℕ :=
  ∑ i, (wordPositions (words i) 0).card.choose k * k.choose p

private def mixedSubsetCount (k p : ℕ) : ℕ :=
  mixedGroupCount bchQuinticGroup1Words k p + 4 * mixedGroupCount bchQuinticGroup4Words k p +
    6 * mixedGroupCount bchQuinticGroup6Words k p + 24 * mixedGroupCount bchQuinticGroup24Words k p

/-- Count the two-color substitutions in a word group and bound each ordered product. -/
private lemma norm_bchQuinticMixedGroupSubsets_le {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k p : ℕ)
    (hk : 3 ≤ k) (hk5 : k ≤ 5) (hp : 1 ≤ p) (hpk : p < k)
    (x V W y : A) {M Vn Wn : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hWM : ‖W‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖bchQuinticMixedGroupSubsets words k p x V W y‖ ≤
      (mixedGroupCount words k p : ℝ) *
        (Vn * Wn * (Vn + Wn) * M ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  have hVn : 0 ≤ Vn := (norm_nonneg V).trans hV
  have hWn : 0 ≤ Wn := (norm_nonneg W).trans hW
  have hprofile : ‖V‖ ^ p * ‖W‖ ^ (k - p) * M ^ (5 - k) ≤
      Vn * Wn * (Vn + Wn) * M ^ 2 := by
    calc
      _ ≤ ‖V‖ * ‖W‖ * (‖V‖ + ‖W‖) * M ^ 2 := by
        simpa only [Nat.add_sub_of_le hpk.le, mul_comm, mul_left_comm, mul_assoc] using
          mixed_profile (norm_nonneg V) (norm_nonneg W) hVM hWM 5 p (k - p)
            hp (by lia) (by lia) (by lia)
      _ ≤ _ := by gcongr
  have hxy := norm_pair_le x y hx hy
  calc
    _ ≤ ∑ i : Fin m, ∑ s ∈ (wordPositions (words i) 0).powersetCard k,
        ∑ _t ∈ s.powersetCard p, Vn * Wn * (Vn + Wn) * M ^ 2 := by
      refine norm_sum_le_of_le _ fun i _ ↦ norm_sum_le_of_le _ fun s hs ↦ ?_
      refine norm_sum_le_of_le _ fun t ht ↦ ?_
      obtain ⟨hts, htp⟩ := mem_powersetCard.mp ht
      have hsk := (mem_powersetCard.mp hs).2
      have hterm : ‖(List.ofFn (t.piecewise (fun _ ↦ V)
          (s.piecewise (fun _ ↦ W) (fun j ↦ ![x, y] (words i j))))).prod‖ ≤
          ‖V‖ ^ p * ‖W‖ ^ (k - p) * M ^ (5 - k) := by
        simpa only [htp, hsk] using
          norm_prod_piecewise_piecewise_le_of_pos (by norm_num) s t hts
            (fun _ ↦ V) (fun _ ↦ W) (fun j ↦ ![x, y] (words i j))
            (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ le_rfl) (fun j _ ↦ hxy (words i j))
      exact hterm.trans hprofile
    _ = _ := by
      rw [mixedGroupCount, Nat.cast_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      calc
        _ = ∑ _s ∈ (wordPositions (words i) 0).powersetCard k,
            (k.choose p : ℝ) * (Vn * Wn * (Vn + Wn) * M ^ 2) := by
          apply sum_congr rfl
          intro s hs
          simp only [sum_const, card_powersetCard, (mem_powersetCard.mp hs).2, nsmul_eq_mul]
        _ = _ := by
          simp only [sum_const, card_powersetCard, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

variable [NormedAlgebra ℚ A]

/-- The weighted substitution count bounds one mixed piece at independent perturbation bounds. -/
private lemma norm_bchQuinticMixedSubsetPiece_le (k p : ℕ)
    (hk : 3 ≤ k) (hk5 : k ≤ 5) (hp : 1 ≤ p) (hpk : p < k)
    (x V W y : A) {M Vn Wn : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hWM : ‖W‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖bchQuinticMixedSubsetPiece k p x V W y‖ ≤
      (mixedSubsetCount k p / 720 : ℝ) * (Vn * Wn * (Vn + Wn) * M ^ 2) := by
  have groupBound {m : ℕ} (words : Fin m → Fin 5 → Fin 2) :=
    norm_bchQuinticMixedGroupSubsets_le words k p hk hk5 hp hpk x V W y hx hy hVM hWM hV hW
  simpa only [bchQuinticMixedSubsetPiece, mixedSubsetCount, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] using norm_inv_smul_bchQuinticBracket_le_of_le
      (groupBound bchQuinticGroup1Words) (groupBound bchQuinticGroup4Words)
      (groupBound bchQuinticGroup6Words) (groupBound bchQuinticGroup24Words)

/-- The mixed second-difference remainder at independent base and perturbation bounds.
Only the actual norms of `V` and `W`, not the bounds `Vn` and `Wn`, must lie below `M`. -/
theorem norm_bchQuinticTermMixed2Remainder_le_of_le (x V W y : A) (M Vn Wn : ℝ)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hVM : ‖V‖ ≤ M) (hWM : ‖W‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖bchQuinticTermMixed2Remainder x V W y‖ ≤
      (4488 / 720 : ℝ) * (Vn * Wn * (Vn + Wn) * M ^ 2) := by
  let R := Vn * Wn * (Vn + Wn) * M ^ 2
  have hcount : ∑ k ∈ Ico 3 5, ∑ p ∈ Ico 1 k, mixedSubsetCount k p = 1040 := by decide +kernel
  rw [bchQuinticTermMixed2Remainder_eq_sum]
  calc
    _ ≤ ∑ k ∈ Ico 3 5, ∑ p ∈ Ico 1 k, (mixedSubsetCount k p / 720 : ℝ) * R := by
      refine norm_sum_le_of_le _ fun k hk ↦ norm_sum_le_of_le _ fun p hp ↦ ?_
      obtain ⟨hk3, hk5⟩ := mem_Ico.mp hk
      obtain ⟨hp1, hpk⟩ := mem_Ico.mp hp
      exact norm_bchQuinticMixedSubsetPiece_le k p hk3 hk5.le hp1 hpk x V W y hx hy hVM hWM hV hW
    _ = (1040 / 720 : ℝ) * R := by
      simp only [← sum_mul, ← sum_div, ← Nat.cast_sum, hcount, Nat.cast_ofNat]
    _ ≤ _ := by
      have hv := (norm_nonneg V).trans hV
      have hw := (norm_nonneg W).trans hW
      exact mul_le_mul_of_nonneg_right (by norm_num) (by dsimp [R]; positivity)

/-- **Mixed second-difference remainder bound** with the source coefficient `4488/720`:
the common scale is `M = ‖x‖ + ‖V‖ + ‖W‖ + ‖y‖`. -/
theorem norm_bchQuinticTermMixed2Remainder_le (x V W y : A) :
    ‖bchQuinticTermMixed2Remainder x V W y‖ ≤
      (4488 / 720 : ℝ) *
        (‖V‖ * ‖W‖ * (‖V‖ + ‖W‖) * (‖x‖ + ‖V‖ + ‖W‖ + ‖y‖) ^ 2) := by
  apply norm_bchQuinticTermMixed2Remainder_le_of_le
  all_goals linarith only [norm_nonneg x, norm_nonneg V, norm_nonneg W, norm_nonneg y]

end FQFP.BCH
