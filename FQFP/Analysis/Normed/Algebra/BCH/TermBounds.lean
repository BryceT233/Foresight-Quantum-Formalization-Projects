/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import FQFP.Analysis.Normed.Algebra.BinaryWord
public import FQFP.Analysis.Normed.Algebra.Commutator
public import FQFP.Algebra.Lie.BCH.Associative.Terms
public import FQFP.Analysis.Normed.Algebra.WordTable

/-!
# Norm bounds for the homogeneous BCH terms

The algebraic terms and identities are defined in `FQFP.Algebra.Lie.BCH.Associative.Terms`.
This file bounds their norms and the cubic difference in normed rational algebras.

## Main results

* `norm_bchCubicTerm_le` through `norm_bchOcticTerm_le`: degree bounds.
* `norm_bchCubicTerm_diff_le`: the cubic difference bound.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable TrotterError

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

/-! ### Norm bounds for products with one distinguished factor -/

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- `‖u * v - v * u‖ ≤ 2 ‖u‖ ‖v‖`: the norm of the ring commutator. -/
lemma norm_mul_sub_mul_le (u v : 𝔸) : ‖u * v - v * u‖ ≤ 2 * ‖u‖ * ‖v‖ :=
  norm_commutator_le u v

/-- `‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 ‖a‖² ‖b‖`: the norm of the double bracket
`[a,[a,b]]`, written out rather than in `⁅·,·⁆` notation. -/
lemma norm_double_commutator_le (a b : 𝔸) :
    ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by
  have h := norm_nestedCommOfList_le b [a, a]
  norm_num [nestedCommOfList, Ring.lie_def] at h
  exact h.trans_eq (by ring)

/-- `‖P * w * Q‖ ≤ M² ‖w‖` when `‖P‖, ‖Q‖ ≤ M`. -/
lemma norm_mul_w_mul_le {P w Q : 𝔸} {M : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) :
    ‖P * w * Q‖ ≤ M ^ 2 * ‖w‖ := by
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    norm_mul_le_of_le (norm_mul_le_of_le hP (le_refl ‖w‖)) hQ

/-- `‖w * Q * R‖ ≤ M² ‖w‖` when `‖Q‖, ‖R‖ ≤ M`. -/
lemma norm_w_mul_mul_le {w Q R : 𝔸} {M : ℝ} (hQ : ‖Q‖ ≤ M) (hR : ‖R‖ ≤ M) :
    ‖w * Q * R‖ ≤ M ^ 2 * ‖w‖ := by
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    norm_mul_le_of_le (norm_mul_le_of_le (le_refl ‖w‖) hQ) hR

/-- `‖P * Q * w‖ ≤ M² ‖w‖` when `‖P‖, ‖Q‖ ≤ M`. -/
lemma norm_mul_mul_w_le {P Q w : 𝔸} {M : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) :
    ‖P * Q * w‖ ≤ M ^ 2 * ‖w‖ := by
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    norm_mul_le_of_le (norm_mul_le_of_le hP hQ) (le_refl ‖w‖)

/-! ### The degree-3 term -/

variable [NormedAlgebra ℚ 𝔸]

private lemma bchCubicTerm_eq_smul_lie (a b : 𝔸) :
    bchCubicTerm a b = (12 : ℚ)⁻¹ • ⁅a - b, ⁅a, b⁆⁆ := by
  change (12 : ℚ)⁻¹ • ⁅a, ⁅a, b⁆⁆ + (12 : ℚ)⁻¹ • ⁅b, ⁅b, a⁆⁆ = _
  rw [← smul_add, sub_lie, ← lie_skew b a, lie_neg, sub_eq_add_neg]

private lemma norm_twelfth_smul_double_commutator_le (u v w : 𝔸) :
    ‖(12 : ℚ)⁻¹ • ⁅u, ⁅v, w⁆⁆‖ ≤ ‖u‖ * ‖v‖ * ‖w‖ := by
  simpa [nestedCommOfList, mul_comm, mul_left_comm, mul_assoc] using
    norm_smul_nestedCommOfList_le_of_le_one w [v, u] (c := (12 : ℚ)⁻¹)
      (by norm_num [← Rat.norm_cast_real])

/-- Norm bound for `bchCubicTerm`: `‖C₃(a,b)‖ ≤ s³` where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bchCubicTerm_le (a b : 𝔸) :
    ‖bchCubicTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 3 := by
  rw [bchCubicTerm_eq_smul_lie, pow_succ, pow_two]
  apply (norm_twelfth_smul_double_commutator_le (a - b) a b).trans
  gcongr <;> first | exact norm_sub_le a b | simp

/-- **Lipschitz-style bound for `bchCubicTerm` in its first argument**:
`‖C₃(z,y) - C₃(x,y)‖ ≤ (‖z‖+‖x‖+‖y‖)² ‖z-x‖`.

Writing the cubic as `(1/12) • [a-b,[a,b]]` splits the difference into two double
commutators, each with one factor `z-x`. -/
theorem norm_bchCubicTerm_diff_le (z x y : 𝔸) :
    ‖bchCubicTerm z y - bchCubicTerm x y‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 2 * ‖z - x‖ := by
  have hdiff : ⁅z - y, ⁅z, y⁆⁆ - ⁅x - y, ⁅x, y⁆⁆ =
      ⁅z - x, ⁅z, y⁆⁆ + ⁅x - y, ⁅z - x, y⁆⁆ := by
    simp only [sub_lie, lie_sub]
    abel
  rw [bchCubicTerm_eq_smul_lie, bchCubicTerm_eq_smul_lie, ← smul_sub, hdiff, smul_add]
  calc
    _ ≤ ‖z - x‖ * ‖z‖ * ‖y‖ + ‖x - y‖ * ‖z - x‖ * ‖y‖ :=
      norm_add_le_of_le (norm_twelfth_smul_double_commutator_le (z - x) z y)
        (norm_twelfth_smul_double_commutator_le (x - y) (z - x) y)
    _ ≤ ‖z - x‖ * ‖z‖ * ‖y‖ + (‖x‖ + ‖y‖) * ‖z - x‖ * ‖y‖ := by
      gcongr
      exact norm_sub_le x y
    _ = (‖z‖ + ‖x‖ + ‖y‖) * ‖y‖ * ‖z - x‖ := by ring
    _ ≤ _ := by
      rw [pow_two]
      gcongr
      exact le_add_of_nonneg_left (by positivity)

/-- Norm bound for `bchQuarticTerm`: `‖C₄(a,b)‖ ≤ s⁴` where `s = ‖a‖ + ‖b‖`.

`C₄` is a single triple bracket, so `‖C₄‖ ≤ (1/24)·2‖b‖·4‖a‖²‖b‖ = (1/3)‖a‖²‖b‖² ≤ s⁴`. -/
theorem norm_bchQuarticTerm_le (a b : 𝔸) :
    ‖bchQuarticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 4 := by
  rw [bchQuarticTerm, norm_neg]
  have h := norm_smul_nestedCommOfList_le_of_le_one b [a, a, b] (c := (24 : ℚ)⁻¹)
    (by norm_num [← Rat.norm_cast_real])
  calc
    _ ≤ ‖b‖ * (‖a‖ * (‖a‖ * ‖b‖)) := by simpa [nestedCommOfList, Ring.lie_def] using h
    _ ≤ (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) * (‖a‖ + ‖b‖))) := by
      gcongr <;> simp
    _ = _ := by ring

/-- Norm bound for the coefficient-1 group: `‖bchQuinticGroup1 a b‖ ≤ 4 s⁵` with `s = ‖a‖ + ‖b‖`. -/
theorem norm_bchQuinticGroup1_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup1 a b‖ ≤ 4 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup1] using norm_sum_wordEval_le_of_pos (by decide) bchQuinticGroup1Words a b

/-- Norm bound for the coefficient-4 group: `‖bchQuinticGroup4 a b‖ ≤ 10 s⁵`. -/
theorem norm_bchQuinticGroup4_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup4 a b‖ ≤ 10 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup4] using norm_sum_wordEval_le_of_pos (by decide) bchQuinticGroup4Words a b

/-- Norm bound for the coefficient-6 group: `‖bchQuinticGroup6 a b‖ ≤ 14 s⁵`. -/
theorem norm_bchQuinticGroup6_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup6 a b‖ ≤ 14 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup6] using norm_sum_wordEval_le_of_pos (by decide) bchQuinticGroup6Words a b

/-- Norm bound for the coefficient-24 group: `‖bchQuinticGroup24 a b‖ ≤ 2 s⁵`. -/
theorem norm_bchQuinticGroup24_le {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup24 a b‖ ≤ 2 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup24] using norm_sum_wordEval_le_of_pos (by decide) bchQuinticGroup24Words a b

/-- Apply the absolute coefficient bound at the BCH table scale. -/
private lemma norm_bchTermTable_le (t : Table (Fin 2)) (a b : 𝔸) {n : ℕ}
    (hn : 0 < n) (hlen : ∀ p ∈ t, p.1.length = n)
    (hbudget : |(coefficientScale ^ n)⁻¹| * (((t.map fun p ↦ p.2.natAbs).sum : ℕ) : ℚ) ≤ 1) :
    ‖eval coefficientScale ![a, b] t‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  rw [eval_of_length _ _ _ n hlen]
  exact norm_smul_eval_one_pair_le _ t a b hn hlen hbudget

/-- Norm bound for `bchQuinticTerm`: `‖C₅(a,b)‖ ≤ s⁵` where `s = ‖a‖ + ‖b‖`.

The sum of the absolute coefficients is `4·1 + 10·4 + 14·6 + 2·24 = 176`, and `176/720 < 1`, so the
`(1/720)·` scaling of `bchQuinticTerm` absorbs the four group bounds into `s⁵`. -/
theorem norm_bchQuinticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchQuinticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  rw [← eval_bchQuinticTermTable]
  exact norm_bchTermTable_le bchQuinticTermTable a b (by decide) (by decide +kernel)
    (by decide +kernel)

end

/-- **Norm bound for `bchSexticTerm`**: `‖C₆(a,b)‖ ≤ (‖a‖ + ‖b‖)⁶`.

The coefficient budget is `28 · (24/1440) = 7/15 ≤ 1`, and every word has six letters. -/
theorem norm_bchSexticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchSexticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 6 :=
  norm_bchTermTable_le bchSexticTermTable a b (by decide) (by decide +kernel)
    (by decide +kernel)

/-- **Norm bound for `bchSepticTerm`**: `‖C₇(a,b)‖ ≤ (‖a‖ + ‖b‖)⁷`.

The coefficient budget is `126 · (216/30240) = 9/10 ≤ 1` (the true sum of absolute values is
`31/315`), and every word has seven letters. -/
theorem norm_bchSepticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchSepticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 :=
  norm_bchTermTable_le bchSepticTermTable a b (by decide) (by decide +kernel)
    (by decide +kernel)

/-- **Norm bound for `bchOcticTerm`**: `‖C₈(a,b)‖ ≤ (‖a‖ + ‖b‖)⁸`.

The coefficient budget is `124 · (432/120960) = 31/70 ≤ 1`, and every word has eight letters. -/
theorem norm_bchOcticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchOcticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 8 :=
  norm_bchTermTable_le bchOcticTermTable a b (by decide) (by decide +kernel)
    (by decide +kernel)

end FQFP.BCH
