/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SymmetricQuintic
public import FQFP.Analysis.Normed.Algebra.Commutator
import Mathlib.Tactic.GCongr

/-!
# A direct bracket bound for the symmetric quintic polynomial

The six Lie monomials are estimated by their bracket structure. No ordered-word table or
coefficient collection is used. The sum of the absolute integer weights is `103`, giving
the intermediate bound `(103 / 360) * (‖a‖ + ‖b‖)^5` and hence the bound with constant one.

## Main results

* `FQFP.norm_symmetricBchQuinticLieTerm_le`: the degree-five input-norm bound.
-/

@[expose] public section

namespace FQFP

attribute [local instance 100] LieRing.ofAssociativeRing

private lemma norm_lie_le_mul_pow {A : Type*} [NormedRing A]
    {x y : A} {s : ℝ} (u v : ℕ) {m n : ℕ}
    (hx : ‖x‖ ≤ (u : ℝ) * s ^ m) (hy : ‖y‖ ≤ (v : ℝ) * s ^ n) :
    ‖⁅x, y⁆‖ ≤ ((2 * u * v : ℕ) : ℝ) * s ^ (m + n) := by
  calc
    _ ≤ 2 * (u * s ^ m) * (v * s ^ n) :=
      (TrotterError.norm_commutator_le x y).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hy
          (norm_nonneg y) (mul_nonneg (by norm_num) ((norm_nonneg x).trans hx)))
    _ = _ := by
      push_cast
      rw [pow_add]
      ring

/-- The quintic symmetric BCH Lie polynomial is bounded by the fifth input-norm power.
No completeness or normalization of the unit norm is required. -/
theorem norm_symmetricBchQuinticLieTerm_le
    {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] (a b : A) :
    ‖symmetricBchQuinticLieTerm a b‖ ≤ (‖a‖ + ‖b‖) ^ 5 := by
  let s := ‖a‖ + ‖b‖
  let c := ⁅b, a⁆
  let cx := ⁅c, a⁆
  let cy := ⁅c, b⁆
  let cxx := ⁅cx, a⁆
  let cxy := ⁅cx, b⁆
  let cyy := ⁅cy, b⁆
  have hs : 0 ≤ s := add_nonneg (norm_nonneg a) (norm_nonneg b)
  have ha : ‖a‖ ≤ ((1 : ℕ) : ℝ) * s ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using le_add_of_nonneg_right (norm_nonneg b)
  have hb : ‖b‖ ≤ ((1 : ℕ) : ℝ) * s ^ 1 := by
    simpa only [Nat.cast_one, one_mul, pow_one] using le_add_of_nonneg_left (norm_nonneg a)
  have hc : ‖c‖ ≤ 2 * s ^ 2 := by simpa [c] using norm_lie_le_mul_pow 1 1 hb ha
  have hcx : ‖cx‖ ≤ 4 * s ^ 3 := by simpa [cx] using norm_lie_le_mul_pow 2 1 hc ha
  have hcy : ‖cy‖ ≤ 4 * s ^ 3 := by simpa [cy] using norm_lie_le_mul_pow 2 1 hc hb
  have hcxx : ‖cxx‖ ≤ 8 * s ^ 4 := by simpa [cxx] using norm_lie_le_mul_pow 4 1 hcx ha
  have hcxy : ‖cxy‖ ≤ 8 * s ^ 4 := by simpa [cxy] using norm_lie_le_mul_pow 4 1 hcx hb
  have hcyy : ‖cyy‖ ≤ 8 * s ^ 4 := by simpa [cyy] using norm_lie_le_mul_pow 4 1 hcy hb
  have h9 : ‖⁅cxx, a⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 8 1 hcxx ha
  have h10 : ‖⁅cxx, b⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 8 1 hcxx hb
  have h11 : ‖⁅cxy, b⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 8 1 hcxy hb
  have h12 : ‖⁅cyy, b⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 8 1 hcyy hb
  have h13 : ‖⁅cx, c⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 4 2 hcx hc
  have h14 : ‖⁅cy, c⁆‖ ≤ 16 * s ^ 5 := by simpa using norm_lie_le_mul_pow 4 2 hcy hc
  have hweight {z : A} (n : ℕ) (hz : ‖z‖ ≤ 16 * s ^ 5) :
      ‖n • z‖ ≤ n * (16 * s ^ 5) := norm_nsmul_le.trans (by gcongr)
  have hsum : ‖7 • ⁅cxx, a⁆ + 28 • ⁅cxx, b⁆ + 32 • ⁅cxy, b⁆ +
      8 • ⁅cyy, b⁆ + 12 • ⁅cx, c⁆ - 16 • ⁅cy, c⁆‖ ≤ 1648 * s ^ 5 := by
    calc
      _ ≤ 7 * (16 * s ^ 5) + 28 * (16 * s ^ 5) + 32 * (16 * s ^ 5) +
          8 * (16 * s ^ 5) + 12 * (16 * s ^ 5) + 16 * (16 * s ^ 5) := by
        exact (norm_sub_le _ _).trans (add_le_add
          (norm_add_le_of_le (norm_add_le_of_le
            (norm_add_le_of_le (norm_add_le_of_le (hweight 7 h9) (hweight 28 h10))
              (hweight 32 h11)) (hweight 8 h12)) (hweight 12 h13)) (hweight 16 h14))
      _ = _ := by ring
  change ‖(5760 : ℚ)⁻¹ • _‖ ≤ s ^ 5
  calc
    _ ≤ ‖(5760 : ℚ)⁻¹‖ * (1648 * s ^ 5) :=
      (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ = (103 / 360 : ℝ) * s ^ 5 := by
      norm_num [← Rat.norm_cast_real]
      ring
    _ ≤ _ := mul_le_of_le_one_left (pow_nonneg hs 5) (by norm_num)

end FQFP
