/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import FQFP.BCH.WordExpansion

/-!
# The graded terms of the BCH series

The BCH element expands as `bch a b = a + b + ½[a,b] + C₃(a,b) + C₄(a,b) + ⋯`, where `Cₙ` is
homogeneous of degree `n`. Throughout, `[x,y] = x * y - y * x` is written out; the Lie-bracket form
of the bounds on `bch a b - (a + b)` is in `BCHCommutator.lean`.

* `bchCubicTerm` — `C₃(a,b) = (1/12)([a,[a,b]] + [b,[b,a]])`, the leading correction after `½[a,b]`.
  `bchCubicTerm_smul` records the homogeneity `C₃(c·a, c·b) = c³·C₃(a,b)`, which is what lets the
  Suzuki parameter condition `4p³ + (1-4p)³ = 0` cancel it, and `norm_bchCubicTerm_le` bounds it by
  `s³` with `s = ‖a‖ + ‖b‖`.
* `bchQuarticTerm` — `C₄(a,b) = -(1/24)[b,[a,[a,b]]]`, with `bchQuarticTerm_smul` (`c⁴`) and
  `norm_bchQuarticTerm_le` (`s⁴`).
* `bchQuinticTerm` — `C₅(a,b)`, assembled from four groups `bchQuinticGroup1`, `bchQuinticGroup4`,
  `bchQuinticGroup6`, `bchQuinticGroup24` collecting the 30 five-letter words by the absolute value
  of their coefficient (`1`, `4`, `6`, `24`, over the common denominator `720`). The group
  definitions need only `[NormedRing 𝔸]`. With `bchQuinticTerm_smul` (`c⁵`) and
  `norm_bchQuinticTerm_le` (`s⁵`).
* The `…_LQ_decomp` lemmas split `C_n(x+W,y) - C_n(x,y)` into a part linear in `W` and a part
  quadratic in `W`; `norm_bchCubicTerm_diff_le` is the coarser statement of the same telescoping,
  `‖C₃(z,y) - C₃(x,y)‖ ≤ (‖z‖+‖x‖+‖y‖)² ‖z-x‖`.

## Provenance

Ported from `Lean-BCH/BCH/Basic.lean` (`bch_cubic_term`, `bch_quartic_term`, `bch_quintic_group_*`,
`bch_quintic_term`, their `_smul` lemmas, the `norm_…_le` bounds and the `_LQ_decomp` lemmas). The
source states the terms over an arbitrary `RCLike 𝕂`; this file uses the `ℚ`-scalar interface of the
rest of `FQFP.BCH`, which is all these terms need, since their coefficients are rational. The
definitions are renamed to Mathlib's `lowerCamelCase`; the theorem names are the source's.
-/

@[expose] public section

namespace FQFP.BCH

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

/-- Any 5-letter word on `{a, b}` has norm at most `s⁵`, where `s = ‖a‖ + ‖b‖`. -/
lemma norm_word5_le (a b x₁ x₂ x₃ x₄ x₅ : 𝔸)
    (h₁ : x₁ = a ∨ x₁ = b) (h₂ : x₂ = a ∨ x₂ = b) (h₃ : x₃ = a ∨ x₃ = b)
    (h₄ : x₄ = a ∨ x₄ = b) (h₅ : x₅ = a ∨ x₅ = b) :
    ‖x₁ * x₂ * x₃ * x₄ * x₅‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖ with hs
  have hxs : ∀ x : 𝔸, x = a ∨ x = b → ‖x‖ ≤ s := by
    intro x hx
    rcases hx with h | h
    · rw [h, hs]; linarith [norm_nonneg b]
    · rw [h, hs]; linarith [norm_nonneg a]
  calc ‖x₁ * x₂ * x₃ * x₄ * x₅‖
      ≤ ‖x₁ * x₂ * x₃ * x₄‖ * ‖x₅‖ := norm_mul_le _ _
    _ ≤ ‖x₁ * x₂ * x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁ * x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖x₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ * ‖x₅‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ s * s * s * s * s := by
        gcongr <;> [exact hxs _ h₁; exact hxs _ h₂; exact hxs _ h₃; exact hxs _ h₄;
          exact hxs _ h₅]
    _ = (‖a‖ + ‖b‖) ^ 5 := by rw [hs]; ring

/-! ### The degree-3 term -/

variable [NormedAlgebra ℚ 𝔸]

/-- Scaling by `(12 : ℚ)⁻¹` does not increase a norm bound. -/
private lemma norm_twelfth_smul_le {u : 𝔸} {B : ℝ} (hu : ‖u‖ ≤ B) :
    ‖(12 : ℚ)⁻¹ • u‖ ≤ B := by
  calc ‖(12 : ℚ)⁻¹ • u‖ ≤ ‖(12 : ℚ)⁻¹‖ * ‖u‖ := norm_smul_le _ _
    _ ≤ 1 * B := mul_le_mul norm_twelfth_inv_le_one hu (norm_nonneg u) (by norm_num)
    _ = B := one_mul B

/-- The degree-3 BCH term: `(1/12)([a,[a,b]] + [b,[b,a]])` with `[x,y] = x * y - y * x`.

This is the leading cubic correction to the BCH element,
`bch a b = a + b + ½[a,b] + bchCubicTerm a b + O(s⁴)`. -/
noncomputable def bchCubicTerm (a b : 𝔸) : 𝔸 :=
  (12 : ℚ)⁻¹ • (a * (a * b - b * a) - (a * b - b * a) * a) +
  (12 : ℚ)⁻¹ • (b * (b * a - a * b) - (b * a - a * b) * b)

/-- **Homogeneity of `bchCubicTerm`**: `C₃(c·a, c·b) = c³·C₃(a,b)`.

This is the property that lets the Suzuki condition `4p³ + (1-4p)³ = 0` kill the cubic term. -/
theorem bchCubicTerm_smul (a b : 𝔸) (c : ℚ) :
    bchCubicTerm (c • a) (c • b) = c ^ 3 • bchCubicTerm a b := by
  have triple : ∀ x y z : 𝔸, (c • x) * ((c • y) * (c • z)) = c ^ 3 • (x * (y * z)) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  have triple' : ∀ x y z : 𝔸, ((c • x) * (c • y)) * (c • z) = c ^ 3 • (x * y * z) := by
    intro x y z
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  unfold bchCubicTerm
  simp only [mul_sub, sub_mul, triple, triple', ← smul_sub, smul_comm (c ^ 3) ((12 : ℚ)⁻¹),
    ← smul_add]

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

/-- **`C₃` decomposition along `x ↦ x + W`**: the difference `C₃(x+W,y) - C₃(x,y)` is
`(1/12)·`(a part linear in `W`) plus `(1/12)·`(a part quadratic in `W`).

This refines the telescoping identity behind `norm_bchCubicTerm_diff_le`, which only sees the
collapsed form: separating the two parts extracts the degree-5 (linear in `W`, when `W = O(s²)`) and
degree-6-or-more (quadratic in `W`) contributions of the cubic difference. -/
theorem bchCubicTerm_LQ_decomp (x W y : 𝔸) :
    bchCubicTerm (x + W) y - bchCubicTerm x y =
      (12 : ℚ)⁻¹ • (
        x * W * y + W * x * y - x * y * W - x * y * W - W * y * x - W * y * x +
        y * x * W + y * W * x + y * y * W - y * W * y - y * W * y + W * y * y) +
      (12 : ℚ)⁻¹ • (
        W * W * y - W * y * W - W * y * W + y * W * W) := by
  unfold bchCubicTerm
  simp only [smul_sub, smul_add, mul_add, add_mul, mul_sub, sub_mul, ← mul_assoc]
  match_scalars <;> ring

/-! ### The degree-4 term -/

/-- The degree-4 BCH term: `-(1/24) [b,[a,[a,b]]]`, the quartic correction in
`bch a b = a + b + ½[a,b] + C₃(a,b) + C₄(a,b) + O(s⁵)`.

In the free Lie algebra `[b,[a,[a,b]]] + [a,[b,[b,a]]] = 0`, so this single triple bracket also
equals `(1/24)[a,[b,[b,a]]]`; the sign convention is the one that makes the expansion of
`bch a b` come out right. -/
noncomputable def bchQuarticTerm (a b : 𝔸) : 𝔸 :=
  -((24 : ℚ)⁻¹ • (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
    (a * (a * b - b * a) - (a * b - b * a) * a) * b))

/-- **Homogeneity of `bchQuarticTerm`**: `C₄(c·a, c·b) = c⁴·C₄(a,b)`.

The inner double bracket is cubic in `(a,b)`, and the outer one adds one more factor of `c`. The
proof is the source's: push the scalars outwards, then split the resulting scalar equalities. -/
theorem bchQuarticTerm_smul (a b : 𝔸) (c : ℚ) :
    bchQuarticTerm (c • a) (c • b) = c ^ 4 • bchQuarticTerm a b := by
  unfold bchQuarticTerm
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub, mul_sub, sub_mul, smul_smul,
    smul_neg, neg_inj]
  ring_nf

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

/-- **`C₄` decomposition along `x ↦ x + W`**: the difference `C₄(x+W,y) - C₄(x,y)` is
`(1/24)·`(a part linear in `W`) plus `(1/24)·`(a part quadratic in `W`).

The degree-4 analogue of `bchCubicTerm_LQ_decomp`. It extracts the degree-4 (linear in `W` when
`W = O(s)`) and degree-6 (quadratic in `W`) leading parts of the quartic difference. -/
theorem bchQuarticTerm_LQ_decomp (x W y : 𝔸) :
    bchQuarticTerm (x + W) y - bchQuarticTerm x y =
      (24 : ℚ)⁻¹ • (
        x * W * y * y + W * x * y * y - x * y * W * y - x * y * W * y -
        W * y * x * y - W * y * x * y +
        y * W * y * x + y * W * y * x + y * x * y * W + y * x * y * W -
        y * y * x * W - y * y * W * x) +
      (24 : ℚ)⁻¹ • (
        W * W * y * y - W * y * W * y - W * y * W * y +
        y * W * y * W + y * W * y * W - y * y * W * W) := by
  unfold bchQuarticTerm
  simp only [smul_sub, smul_add, mul_add, add_mul, mul_sub, sub_mul, sub_neg_eq_add,
    ← mul_assoc]
  match_scalars <;> ring

/-! ### The degree-5 term

The four groups are sums over an explicit list of **word patterns** (`true` is the letter `a`),
in the form consumed by `WordExpansion.norm_sum_wordEval_le`: the word data is a
`Fin m → Fin 5 → Bool`, so the norm bound of a group is one application of the group lemma rather
than one estimate per word. -/

/-- The four word patterns of `bchQuinticGroup1`: the "almost pure" words `AAAAB`, `ABBBB`, `BAAAA`,
`BBBBA`. -/
def bchQuinticGroup1Words : Fin 4 → Fin 5 → Bool :=
  ![![true, true, true, true, false], ![true, false, false, false, false],
    ![false, true, true, true, true], ![false, false, false, false, true]]

/-- The ten word patterns of `bchQuinticGroup4`. -/
def bchQuinticGroup4Words : Fin 10 → Fin 5 → Bool :=
  ![![true, true, true, false, true], ![true, true, true, false, false],
    ![true, true, false, false, false], ![true, false, true, true, true],
    ![true, false, false, false, true], ![false, true, true, true, false],
    ![false, true, false, false, false], ![false, false, true, true, true],
    ![false, false, false, true, true], ![false, false, false, true, false]]

/-- The fourteen word patterns of `bchQuinticGroup6`. -/
def bchQuinticGroup6Words : Fin 14 → Fin 5 → Bool :=
  ![![true, true, false, true, true], ![true, true, false, true, false],
    ![true, true, false, false, true], ![true, false, true, true, false],
    ![true, false, true, false, false], ![true, false, false, true, true],
    ![true, false, false, true, false], ![false, true, true, false, true],
    ![false, true, true, false, false], ![false, true, false, true, true],
    ![false, true, false, false, true], ![false, false, true, true, false],
    ![false, false, true, false, true], ![false, false, true, false, false]]

/-- The two palindromic word patterns of `bchQuinticGroup24`. -/
def bchQuinticGroup24Words : Fin 2 → Fin 5 → Bool :=
  ![![true, false, true, false, true], ![false, true, false, true, false]]

/-- **Coefficient-1 group** of `bchQuinticTerm`: the four 5-letter words whose coefficient has
absolute value 1. -/
noncomputable def bchQuinticGroup1 {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, (List.ofFn (wordEval (bchQuinticGroup1Words i) a b)).prod

/-- **Coefficient-4 group** of `bchQuinticTerm`: the ten 5-letter words whose coefficient has
absolute value 4. -/
noncomputable def bchQuinticGroup4 {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, (List.ofFn (wordEval (bchQuinticGroup4Words i) a b)).prod

/-- **Coefficient-6 group** of `bchQuinticTerm`: the fourteen 5-letter words whose coefficient has
absolute value 6. -/
noncomputable def bchQuinticGroup6 {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, (List.ofFn (wordEval (bchQuinticGroup6Words i) a b)).prod

/-- **Coefficient-24 group** of `bchQuinticTerm`: the two palindromic 5-letter words whose
coefficient has absolute value 24. -/
noncomputable def bchQuinticGroup24 {𝔸 : Type*} [NormedRing 𝔸] (a b : 𝔸) : 𝔸 :=
  ∑ i, (List.ofFn (wordEval (bchQuinticGroup24Words i) a b)).prod

/-- The degree-5 BCH term: the degree-5 part of `bch a b = log (exp a * exp b)`.

It involves 30 of the 32 five-letter words on `{a, b}`: the pure words `aaaaa` and `bbbbb` are
absent, since `bch a 0 = a` and `bch 0 b = b` have no quintic correction. The common denominator is
`720`. The words are collected into four groups by the absolute value of their coefficient (`1`,
`4`, `6`, `24`), which keeps the homogeneity and norm bookkeeping uniform. -/
noncomputable def bchQuinticTerm (a b : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • (
    -bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
      (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b)

/-! #### Homogeneity of the degree-5 term -/

theorem bchQuinticGroup1_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸)
    (c : ℚ) : bchQuinticGroup1 (c • a) (c • b) = c ^ 5 • bchQuinticGroup1 a b := by
  unfold bchQuinticGroup1
  exact sum_wordEval_smul bchQuinticGroup1Words a b c

theorem bchQuinticGroup4_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸)
    (c : ℚ) : bchQuinticGroup4 (c • a) (c • b) = c ^ 5 • bchQuinticGroup4 a b := by
  unfold bchQuinticGroup4
  exact sum_wordEval_smul bchQuinticGroup4Words a b c

theorem bchQuinticGroup6_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸)
    (c : ℚ) : bchQuinticGroup6 (c • a) (c • b) = c ^ 5 • bchQuinticGroup6 a b := by
  unfold bchQuinticGroup6
  exact sum_wordEval_smul bchQuinticGroup6Words a b c

theorem bchQuinticGroup24_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸)
    (c : ℚ) : bchQuinticGroup24 (c • a) (c • b) = c ^ 5 • bchQuinticGroup24 a b := by
  unfold bchQuinticGroup24
  exact sum_wordEval_smul bchQuinticGroup24Words a b c

/-- **Homogeneity of `bchQuinticTerm`**: `C₅(c·a, c·b) = c⁵·C₅(a,b)`. -/
theorem bchQuinticTerm_smul (a b : 𝔸) (c : ℚ) :
    bchQuinticTerm (c • a) (c • b) = c ^ 5 • bchQuinticTerm a b := by
  unfold bchQuinticTerm
  rw [bchQuinticGroup1_smul, bchQuinticGroup4_smul, bchQuinticGroup6_smul,
    bchQuinticGroup24_smul]
  -- Pull `c ^ 5` out of each scaled group, then out of the outer `(720)⁻¹` scaling.
  rw [smul_comm ((4 : ℚ)) (c ^ 5), smul_comm ((6 : ℚ)) (c ^ 5),
    smul_comm ((24 : ℚ)) (c ^ 5),
    ← smul_neg, ← smul_add, ← smul_sub, ← smul_add,
    smul_comm ((720 : ℚ)⁻¹) (c ^ 5)]

/-! #### Norm bounds for the four groups and the headline bound -/

/-- Norm bound for the coefficient-1 group: `‖bchQuinticGroup1 a b‖ ≤ 4 s⁵` with `s = ‖a‖ + ‖b‖`. -/
theorem norm_bchQuinticGroup1_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup1 a b‖ ≤ 4 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup1] using norm_sum_wordEval_le bchQuinticGroup1Words a b

/-- Norm bound for the coefficient-4 group: `‖bchQuinticGroup4 a b‖ ≤ 10 s⁵`. -/
theorem norm_bchQuinticGroup4_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup4 a b‖ ≤ 10 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup4] using norm_sum_wordEval_le bchQuinticGroup4Words a b

/-- Norm bound for the coefficient-6 group: `‖bchQuinticGroup6 a b‖ ≤ 14 s⁵`. -/
theorem norm_bchQuinticGroup6_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup6 a b‖ ≤ 14 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup6] using norm_sum_wordEval_le bchQuinticGroup6Words a b

/-- Norm bound for the coefficient-24 group: `‖bchQuinticGroup24 a b‖ ≤ 2 s⁵`. -/
theorem norm_bchQuinticGroup24_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (a b : 𝔸) :
    ‖bchQuinticGroup24 a b‖ ≤ 2 * (‖a‖ + ‖b‖) ^ 5 := by
  simpa [bchQuinticGroup24] using norm_sum_wordEval_le bchQuinticGroup24Words a b

/-- Norm bound for `bchQuinticTerm`: `‖C₅(a,b)‖ ≤ s⁵` where `s = ‖a‖ + ‖b‖`.

The sum of the absolute coefficients is `4·1 + 10·4 + 14·6 + 2·24 = 176`, and `176/720 < 1`, so the
`(1/720)·` scaling of `bchQuinticTerm` absorbs the four group bounds into `s⁵`. -/
theorem norm_bchQuinticTerm_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸]
    (a b : 𝔸) :
    ‖bchQuinticTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  set s := ‖a‖ + ‖b‖ with hs
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  have hs5_nn : 0 ≤ s ^ 5 := pow_nonneg hs_nn 5
  have hg1 : ‖bchQuinticGroup1 a b‖ ≤ 4 * s ^ 5 := by
    rw [hs]; exact norm_bchQuinticGroup1_le a b
  have hg4 : ‖bchQuinticGroup4 a b‖ ≤ 10 * s ^ 5 := by
    rw [hs]; exact norm_bchQuinticGroup4_le a b
  have hg6 : ‖bchQuinticGroup6 a b‖ ≤ 14 * s ^ 5 := by
    rw [hs]; exact norm_bchQuinticGroup6_le a b
  have hg24 : ‖bchQuinticGroup24 a b‖ ≤ 2 * s ^ 5 := by
    rw [hs]; exact norm_bchQuinticGroup24_le a b
  have hng1 : ‖-bchQuinticGroup1 a b‖ ≤ 4 * s ^ 5 := by rw [norm_neg]; exact hg1
  have h4n : ‖(4 : ℚ) • bchQuinticGroup4 a b‖ ≤ 40 * s ^ 5 := by
    calc ‖(4 : ℚ) • bchQuinticGroup4 a b‖
        ≤ ‖(4 : ℚ)‖ * ‖bchQuinticGroup4 a b‖ := norm_smul_le _ _
      _ = 4 * ‖bchQuinticGroup4 a b‖ := by simp [← Rat.norm_cast_real]
      _ ≤ 4 * (10 * s ^ 5) := mul_le_mul_of_nonneg_left hg4 (by norm_num)
      _ = 40 * s ^ 5 := by ring
  have h6n : ‖(6 : ℚ) • bchQuinticGroup6 a b‖ ≤ 84 * s ^ 5 := by
    calc ‖(6 : ℚ) • bchQuinticGroup6 a b‖
        ≤ ‖(6 : ℚ)‖ * ‖bchQuinticGroup6 a b‖ := norm_smul_le _ _
      _ = 6 * ‖bchQuinticGroup6 a b‖ := by simp [← Rat.norm_cast_real]
      _ ≤ 6 * (14 * s ^ 5) := mul_le_mul_of_nonneg_left hg6 (by norm_num)
      _ = 84 * s ^ 5 := by ring
  have h24n : ‖(24 : ℚ) • bchQuinticGroup24 a b‖ ≤ 48 * s ^ 5 := by
    calc ‖(24 : ℚ) • bchQuinticGroup24 a b‖
        ≤ ‖(24 : ℚ)‖ * ‖bchQuinticGroup24 a b‖ := norm_smul_le _ _
      _ = 24 * ‖bchQuinticGroup24 a b‖ := by simp [← Rat.norm_cast_real]
      _ ≤ 24 * (2 * s ^ 5) := mul_le_mul_of_nonneg_left hg24 (by norm_num)
      _ = 48 * s ^ 5 := by ring
  have h_inner : ‖-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
      (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b‖ ≤ 176 * s ^ 5 := by
    have step1 := norm_add_le (-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
      (6 : ℚ) • bchQuinticGroup6 a b) ((24 : ℚ) • bchQuinticGroup24 a b)
    have step2 := norm_sub_le (-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b)
      ((6 : ℚ) • bchQuinticGroup6 a b)
    have step3 := norm_add_le (-bchQuinticGroup1 a b) ((4 : ℚ) • bchQuinticGroup4 a b)
    linarith only [step1, step2, step3, hng1, h4n, h6n, h24n]
  have h720 : ‖((720 : ℚ)⁻¹)‖ = 1 / 720 := by simp [← Rat.norm_cast_real]
  unfold bchQuinticTerm
  calc ‖(720 : ℚ)⁻¹ • (-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
        (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b)‖
      ≤ ‖((720 : ℚ)⁻¹)‖ * ‖-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
        (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b‖ :=
        norm_smul_le _ _
    _ = (1 / 720) * ‖-bchQuinticGroup1 a b + (4 : ℚ) • bchQuinticGroup4 a b -
        (6 : ℚ) • bchQuinticGroup6 a b + (24 : ℚ) • bchQuinticGroup24 a b‖ := by rw [h720]
    _ ≤ (1 / 720) * (176 * s ^ 5) := mul_le_mul_of_nonneg_left h_inner (by norm_num)
    _ = (176 / 720) * s ^ 5 := by ring
    _ ≤ s ^ 5 := by
        refine mul_le_of_le_one_left hs5_nn ?_
        norm_num

end

end FQFP.BCH
