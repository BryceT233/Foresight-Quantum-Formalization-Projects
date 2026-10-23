/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import FQFP.BCH.WordExpansion
public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Analysis.WordTable

/-!
# Norm bounds for the homogeneous BCH terms

The algebraic terms and identities are defined in `FQFP.BCH.Algebra.Terms`.
This file bounds their norms and the cubic difference in normed rational algebras.

## Main results

* `norm_bchCubicTerm_le` through `norm_bchOcticTerm_le`: degree bounds.
* `norm_bchCubicTerm_diff_le`: the cubic difference bound.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

noncomputable section

/-! ### Scalar and real-arithmetic helpers -/

/-- `4xy(x+y) ≤ (x+y)³` for `x, y ≥ 0`: the two cubic cross terms of `(x+y)³`. -/
private lemma four_mul_mul_add_le_cube (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    4 * x * y * (x + y) ≤ (x + y) ^ 3 := by
  have h4 : 4 * x * y ≤ (x + y) ^ 2 := four_mul_le_sq_add x y
  calc 4 * x * y * (x + y) ≤ (x + y) ^ 2 * (x + y) :=
        mul_le_mul_of_nonneg_right h4 (by linarith)
    _ = (x + y) ^ 3 := by ring

private lemma norm_twelfth_inv : ‖(12 : ℚ)⁻¹‖ = (12 : ℝ)⁻¹ := by
  rw [norm_inv, ← Rat.norm_cast_real]
  norm_num

private lemma norm_twelfth_inv_le_one : ‖(12 : ℚ)⁻¹‖ ≤ 1 := by
  rw [norm_twelfth_inv]
  norm_num

/-- `8 x² y² ≤ (x + y)⁴` for `x, y ≥ 0`: the middle term of `(x+y)⁴` dominates twice the two
quartic cross terms `x³y` and `xy³`. -/
private lemma eight_mul_sq_mul_sq_le_pow_four (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    8 * x ^ 2 * y ^ 2 ≤ (x + y) ^ 4 := by
  have h4 : 4 * x * y ≤ (x + y) ^ 2 := four_mul_le_sq_add x y
  have hxy : x * y ≤ (x + y) ^ 2 / 4 := by linarith only [h4]
  have hsq : (x * y) ^ 2 ≤ ((x + y) ^ 2 / 4) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hx hy) hxy 2
  calc 8 * x ^ 2 * y ^ 2 = 8 * (x * y) ^ 2 := by ring
    _ ≤ 8 * ((x + y) ^ 2 / 4) ^ 2 := by linarith only [hsq]
    _ = (x + y) ^ 4 / 2 := by ring
    _ ≤ (x + y) ^ 4 := by
        have hnn : 0 ≤ (x + y) ^ 4 := by positivity
        linarith only [hnn]

/-! ### Norm bounds for products with one distinguished factor -/

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- `‖u * v - v * u‖ ≤ 2 ‖u‖ ‖v‖`: the norm of the ring commutator. -/
lemma norm_mul_sub_mul_le (u v : 𝔸) : ‖u * v - v * u‖ ≤ 2 * ‖u‖ * ‖v‖ := by
  calc ‖u * v - v * u‖ ≤ ‖u * v‖ + ‖v * u‖ := norm_sub_le _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖u‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖u‖ * ‖v‖ := by ring

/-- `‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 ‖a‖² ‖b‖`: the norm of the double bracket
`[a,[a,b]]`, written out rather than in `⁅·,·⁆` notation. -/
lemma norm_double_commutator_le (a b : 𝔸) :
    ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by
  have hcomm := norm_mul_sub_mul_le a b
  calc ‖a * (a * b - b * a) - (a * b - b * a) * a‖
      ≤ ‖a * (a * b - b * a)‖ + ‖(a * b - b * a) * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖a * b - b * a‖ + ‖a * b - b * a‖ * ‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖a‖ * (2 * ‖a‖ * ‖b‖) + (2 * ‖a‖ * ‖b‖) * ‖a‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hcomm (norm_nonneg a))
          (mul_le_mul_of_nonneg_right hcomm (norm_nonneg a))
    _ = 4 * ‖a‖ ^ 2 * ‖b‖ := by ring

/-- `‖P * w * Q‖ ≤ M² ‖w‖` when `‖P‖, ‖Q‖ ≤ M`. -/
lemma norm_mul_w_mul_le {P w Q : 𝔸} {M : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) :
    ‖P * w * Q‖ ≤ M ^ 2 * ‖w‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg P) hP
  calc ‖P * w * Q‖ ≤ ‖P * w‖ * ‖Q‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖w‖) * ‖Q‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg Q)
    _ ≤ (M * ‖w‖) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg w)) hQ (norm_nonneg Q)
          (mul_nonneg hM (norm_nonneg w))
    _ = M ^ 2 * ‖w‖ := by ring

/-- `‖w * Q * R‖ ≤ M² ‖w‖` when `‖Q‖, ‖R‖ ≤ M`. -/
lemma norm_w_mul_mul_le {w Q R : 𝔸} {M : ℝ} (hQ : ‖Q‖ ≤ M) (hR : ‖R‖ ≤ M) :
    ‖w * Q * R‖ ≤ M ^ 2 * ‖w‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg Q) hQ
  calc ‖w * Q * R‖ ≤ ‖w * Q‖ * ‖R‖ := norm_mul_le _ _
    _ ≤ (‖w‖ * ‖Q‖) * ‖R‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg R)
    _ ≤ (‖w‖ * M) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQ (norm_nonneg w)) hR (norm_nonneg R)
          (mul_nonneg (norm_nonneg w) hM)
    _ = M ^ 2 * ‖w‖ := by ring

/-- `‖P * Q * w‖ ≤ M² ‖w‖` when `‖P‖, ‖Q‖ ≤ M`. -/
lemma norm_mul_mul_w_le {P Q w : 𝔸} {M : ℝ} (hP : ‖P‖ ≤ M) (hQ : ‖Q‖ ≤ M) :
    ‖P * Q * w‖ ≤ M ^ 2 * ‖w‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg P) hP
  calc ‖P * Q * w‖ ≤ ‖P * Q‖ * ‖w‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖Q‖) * ‖w‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg w)
    _ ≤ (M * M) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul hP hQ (norm_nonneg Q) hM) (norm_nonneg w)
    _ = M ^ 2 * ‖w‖ := by ring

/-! ### The degree-3 term -/

variable [NormedAlgebra ℚ 𝔸]

/-- Scaling by `(12 : ℚ)⁻¹` does not increase a norm bound. -/
private lemma norm_twelfth_smul_le {u : 𝔸} {B : ℝ} (hu : ‖u‖ ≤ B) :
    ‖(12 : ℚ)⁻¹ • u‖ ≤ B := by
  calc ‖(12 : ℚ)⁻¹ • u‖ ≤ ‖(12 : ℚ)⁻¹‖ * ‖u‖ := norm_smul_le _ _
    _ ≤ 1 * B := mul_le_mul norm_twelfth_inv_le_one hu (norm_nonneg u) (by norm_num)
    _ = B := one_mul B

/-- Norm bound for `bchCubicTerm`: `‖C₃(a,b)‖ ≤ s³` where `s = ‖a‖ + ‖b‖`. -/
theorem norm_bchCubicTerm_le (a b : 𝔸) :
    ‖bchCubicTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 3 := by
  have h1 : ‖a * (a * b - b * a) - (a * b - b * a) * a‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ :=
    norm_double_commutator_le a b
  have h2 : ‖b * (b * a - a * b) - (b * a - a * b) * b‖ ≤ 4 * ‖a‖ * ‖b‖ ^ 2 := by
    calc ‖b * (b * a - a * b) - (b * a - a * b) * b‖ ≤ 4 * ‖b‖ ^ 2 * ‖a‖ :=
          norm_double_commutator_le b a
      _ = 4 * ‖a‖ * ‖b‖ ^ 2 := by ring
  unfold bchCubicTerm
  calc ‖(12 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) +
        (12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖
      ≤ ‖(12 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a)‖ +
        ‖(12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)‖ := norm_add_le _ _
    _ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ + 4 * ‖a‖ * ‖b‖ ^ 2 :=
        add_le_add (norm_twelfth_smul_le h1) (norm_twelfth_smul_le h2)
    _ = 4 * ‖a‖ * ‖b‖ * (‖a‖ + ‖b‖) := by ring
    _ ≤ (‖a‖ + ‖b‖) ^ 3 := four_mul_mul_add_le_cube _ _ (norm_nonneg a) (norm_nonneg b)

/-- **Lipschitz-style bound for `bchCubicTerm` in its first argument**:
`‖C₃(z,y) - C₃(x,y)‖ ≤ (‖z‖+‖x‖+‖y‖)² ‖z-x‖`.

The difference telescopes into 12 summands, each a product `P * (z-x) * Q` with `P`, `Q` single
letters from `{z, x, y}` (9 distinct patterns, three of them appearing twice). Every summand has
norm at most `M²‖z-x‖` with `M = ‖z‖+‖x‖+‖y‖`, and the `(1/12)·` scaling of `bchCubicTerm` trims
the resulting `12 M²‖z-x‖` to exactly `M²‖z-x‖`. -/
theorem norm_bchCubicTerm_diff_le (z x y : 𝔸) :
    ‖bchCubicTerm z y - bchCubicTerm x y‖ ≤ (‖z‖ + ‖x‖ + ‖y‖) ^ 2 * ‖z - x‖ := by
  have htel : bchCubicTerm z y - bchCubicTerm x y =
      (12 : ℚ)⁻¹ • (
          z * (z - x) * y + (z - x) * x * y
        - z * y * (z - x) - z * y * (z - x)
        - (z - x) * y * x - (z - x) * y * x
        + y * z * (z - x) + y * (z - x) * x
        + y * y * (z - x)
        - y * (z - x) * y - y * (z - x) * y
        + (z - x) * y * y) := by
    unfold bchCubicTerm
    simp only [smul_sub, smul_add, mul_sub, sub_mul, ← mul_assoc]
    match_scalars <;> ring
  rw [htel]
  set M := ‖z‖ + ‖x‖ + ‖y‖ with hM
  have hz : ‖z‖ ≤ M := by rw [hM]; linarith [norm_nonneg x, norm_nonneg y]
  have hx : ‖x‖ ≤ M := by rw [hM]; linarith [norm_nonneg z, norm_nonneg y]
  have hy : ‖y‖ ≤ M := by rw [hM]; linarith [norm_nonneg z, norm_nonneg x]
  -- The nine distinct summands; `t3`, `t4` and `t8` each occur twice in the telescoping sum.
  let t1 : 𝔸 := z * (z - x) * y
  let t2 : 𝔸 := (z - x) * x * y
  let t3 : 𝔸 := -(z * y * (z - x))
  let t4 : 𝔸 := -((z - x) * y * x)
  let t5 : 𝔸 := y * z * (z - x)
  let t6 : 𝔸 := y * (z - x) * x
  let t7 : 𝔸 := y * y * (z - x)
  let t8 : 𝔸 := -(y * (z - x) * y)
  let t9 : 𝔸 := (z - x) * y * y
  have hsum_eq : (z * (z - x) * y + (z - x) * x * y
        - z * y * (z - x) - z * y * (z - x)
        - (z - x) * y * x - (z - x) * y * x
        + y * z * (z - x) + y * (z - x) * x
        + y * y * (z - x)
        - y * (z - x) * y - y * (z - x) * y
        + (z - x) * y * y) =
      t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8 + t9 := by
    dsimp only [t1, t2, t3, t4, t5, t6, t7, t8, t9]
    abel
  rw [hsum_eq]
  have ht1 : ‖t1‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t1]; exact norm_mul_w_mul_le hz hy
  have ht2 : ‖t2‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t2]; exact norm_w_mul_mul_le hx hy
  have ht3 : ‖t3‖ ≤ M ^ 2 * ‖z - x‖ := by
    dsimp only [t3]; rw [norm_neg]; exact norm_mul_mul_w_le hz hy
  have ht4 : ‖t4‖ ≤ M ^ 2 * ‖z - x‖ := by
    dsimp only [t4]; rw [norm_neg]; exact norm_w_mul_mul_le hy hx
  have ht5 : ‖t5‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t5]; exact norm_mul_mul_w_le hy hz
  have ht6 : ‖t6‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t6]; exact norm_mul_w_mul_le hy hx
  have ht7 : ‖t7‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t7]; exact norm_mul_mul_w_le hy hy
  have ht8 : ‖t8‖ ≤ M ^ 2 * ‖z - x‖ := by
    dsimp only [t8]; rw [norm_neg]; exact norm_mul_w_mul_le hy hy
  have ht9 : ‖t9‖ ≤ M ^ 2 * ‖z - x‖ := by dsimp only [t9]; exact norm_w_mul_mul_le hy hy
  have hsum : ‖t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8 + t9‖ ≤
      12 * (M ^ 2 * ‖z - x‖) := by
    have a1 := norm_add_le t1 t2
    have a2 := norm_add_le (t1 + t2) t3
    have a3 := norm_add_le (t1 + t2 + t3) t3
    have a4 := norm_add_le (t1 + t2 + t3 + t3) t4
    have a5 := norm_add_le (t1 + t2 + t3 + t3 + t4) t4
    have a6 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4) t5
    have a7 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4 + t5) t6
    have a8 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6) t7
    have a9 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7) t8
    have a10 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8) t8
    have a11 := norm_add_le (t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8) t9
    linarith only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
      ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  calc ‖(12 : ℚ)⁻¹ • (t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8 + t9)‖
      ≤ ‖(12 : ℚ)⁻¹‖ * ‖t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8 + t9‖ :=
        norm_smul_le _ _
    _ = (12 : ℝ)⁻¹ * ‖t1 + t2 + t3 + t3 + t4 + t4 + t5 + t6 + t7 + t8 + t8 + t9‖ := by
        rw [norm_twelfth_inv]
    _ ≤ (12 : ℝ)⁻¹ * (12 * (M ^ 2 * ‖z - x‖)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = M ^ 2 * ‖z - x‖ := by ring

/-- Norm bound for `bchQuarticTerm`: `‖C₄(a,b)‖ ≤ s⁴` where `s = ‖a‖ + ‖b‖`.

`C₄` is a single triple bracket, so `‖C₄‖ ≤ (1/24)·2‖b‖·4‖a‖²‖b‖ = (1/3)‖a‖²‖b‖² ≤ s⁴`. -/
theorem norm_bchQuarticTerm_le (a b : 𝔸) :
    ‖bchQuarticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 4 := by
  have h24 : ‖(24 : ℚ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, ← Rat.norm_cast_real]
    norm_num
  unfold bchQuarticTerm
  set DC : 𝔸 := a * (a * b - b * a) - (a * b - b * a) * a with hDC
  have hDC_le : ‖DC‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ := by rw [hDC]; exact norm_double_commutator_le a b
  have htc : ‖b * DC - DC * b‖ ≤ 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    calc ‖b * DC - DC * b‖ ≤ 2 * ‖b‖ * ‖DC‖ := norm_mul_sub_mul_le b DC
      _ ≤ 2 * ‖b‖ * (4 * ‖a‖ ^ 2 * ‖b‖) :=
          mul_le_mul_of_nonneg_left hDC_le (by positivity)
      _ = 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring
  calc ‖-((24 : ℚ)⁻¹ • (b * DC - DC * b))‖
      = ‖(24 : ℚ)⁻¹ • (b * DC - DC * b)‖ := norm_neg _
    _ ≤ ‖(24 : ℚ)⁻¹‖ * ‖b * DC - DC * b‖ := norm_smul_le _ _
    _ ≤ 1 * (8 * ‖a‖ ^ 2 * ‖b‖ ^ 2) :=
        mul_le_mul h24 htc (norm_nonneg _) (by norm_num)
    _ = 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := one_mul _
    _ ≤ (‖a‖ + ‖b‖) ^ 4 := eight_mul_sq_mul_sq_le_pow_four _ _ (norm_nonneg a) (norm_nonneg b)

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

/-- Norm bound for `bchQuinticTerm`: `‖C₅(a,b)‖ ≤ s⁵` where `s = ‖a‖ + ‖b‖`.

The sum of the absolute coefficients is `4·1 + 10·4 + 14·6 + 2·24 = 176`, and `176/720 < 1`, so the
`(1/720)·` scaling of `bchQuinticTerm` absorbs the four group bounds into `s⁵`. -/
theorem norm_bchQuinticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchQuinticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  have hbudget : (bchQuinticTermTable.map
      fun p ↦ ‖(p.2 : ℚ) / coefficientScale ^ p.1.length‖).sum ≤ 1 := by
    norm_num [bchQuinticTermTable, bchQuinticGroup1Words, bchQuinticGroup4Words,
      bchQuinticGroup6Words, bchQuinticGroup24Words, coefficientScale,
      ← Rat.norm_cast_real, Real.norm_eq_abs, List.ofFn_succ]
  have hn : ∀ p ∈ bchQuinticTermTable, p.1.length = 5 := by
    have hall : bchQuinticTermTable.all (fun p ↦ p.1.length == 5) = true := by decide
    intro p hp
    simpa using (List.all_eq_true.mp hall) p hp
  rw [← eval_bchQuinticTermTable]
  refine (WordTable.norm_eval_le coefficientScale ![a, b] bchQuinticTermTable
    (fun p hp ↦ ?_)).trans (mul_le_of_le_one_left (by positivity) hbudget)
  simpa only [hn p hp] using
    norm_prod_map_pair_le_of_ne_nil p.1 (by have := hn p hp; grind) a b

end

/-- **Norm bound for `bchSexticTerm`**: `‖C₆(a,b)‖ ≤ (‖a‖ + ‖b‖)⁶`.

The coefficient budget is `28 · (24/1440) = 7/15 ≤ 1`, and every word has six letters. -/
theorem norm_bchSexticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchSexticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 6 := by
  have hbudget : (bchSexticTermTable.map
      fun p ↦ ‖(p.2 : ℚ) / coefficientScale ^ p.1.length‖).sum ≤ 1 := by
    norm_num [bchSexticTermTable, coefficientScale, ← Rat.norm_cast_real,
      Real.norm_eq_abs]
  have hn : ∀ p ∈ bchSexticTermTable, p.1.length = 6 := by
    have hall : bchSexticTermTable.all (fun p ↦ p.1.length == 6) = true := by decide
    intro p hp
    simpa using (List.all_eq_true.mp hall) p hp
  refine (WordTable.norm_eval_le coefficientScale ![a, b] bchSexticTermTable
    (fun p hp ↦ ?_)).trans (mul_le_of_le_one_left (by positivity) hbudget)
  simpa only [hn p hp] using
    norm_prod_map_pair_le_of_ne_nil p.1 (by have := hn p hp; grind) a b

/-- **Norm bound for `bchSepticTerm`**: `‖C₇(a,b)‖ ≤ (‖a‖ + ‖b‖)⁷`.

The coefficient budget is `126 · (216/30240) = 9/10 ≤ 1` (the true sum of absolute values is
`31/315`), and every word has seven letters. -/
theorem norm_bchSepticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchSepticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 7 := by
  have hbudget : (bchSepticTermTable.map
      fun p ↦ ‖(p.2 : ℚ) / coefficientScale ^ p.1.length‖).sum ≤ 1 := by
    norm_num [bchSepticTermTable, coefficientScale, ← Rat.norm_cast_real,
      Real.norm_eq_abs]
  have hn : ∀ p ∈ bchSepticTermTable, p.1.length = 7 := by
    have hall : bchSepticTermTable.all (fun p ↦ p.1.length == 7) = true := by decide
    intro p hp
    simpa using (List.all_eq_true.mp hall) p hp
  refine (WordTable.norm_eval_le coefficientScale ![a, b] bchSepticTermTable
    (fun p hp ↦ ?_)).trans (mul_le_of_le_one_left (by positivity) hbudget)
  simpa only [hn p hp] using
    norm_prod_map_pair_le_of_ne_nil p.1 (by have := hn p hp; grind) a b

/-- **Norm bound for `bchOcticTerm`**: `‖C₈(a,b)‖ ≤ (‖a‖ + ‖b‖)⁸`.

The coefficient budget is `124 · (432/120960) = 31/70 ≤ 1`, and every word has eight letters. -/
theorem norm_bchOcticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (a b : 𝔸) : ‖bchOcticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 8 := by
  have hbudget : (bchOcticTermTable.map
      fun p ↦ ‖(p.2 : ℚ) / coefficientScale ^ p.1.length‖).sum ≤ 1 := by
    norm_num [bchOcticTermTable, coefficientScale, ← Rat.norm_cast_real,
      Real.norm_eq_abs]
  have hn : ∀ p ∈ bchOcticTermTable, p.1.length = 8 := by
    have hall : bchOcticTermTable.all (fun p ↦ p.1.length == 8) = true := by decide
    intro p hp
    simpa using (List.all_eq_true.mp hall) p hp
  refine (WordTable.norm_eval_le coefficientScale ![a, b] bchOcticTermTable
    (fun p hp ↦ ?_)).trans (mul_le_of_le_one_left (by positivity) hbudget)
  simpa only [hn p hp] using
    norm_prod_map_pair_le_of_ne_nil p.1 (by have := hn p hp; grind) a b

end FQFP.BCH
