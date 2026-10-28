/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Coefficients
public import FQFP.Algebra.Lie.BCH.SymmetricCoefficients

import Mathlib.Tactic.Module

/-!
# Low-degree regressions of the ordinary BCH Lie coefficients

The first coefficients follow by the finite conjugation sum. The sixth-degree
expression uses only the already identified cubic and quintic symmetric terms.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp]
theorem bchLieCoeff_zero (x y : L) : bchLieCoeff x y 0 = 0 := by
  simp [bchLieCoeff]

@[simp]
theorem bchLieCoeff_one (x y : L) : bchLieCoeff x y 1 = x + y := by
  simp [bchLieCoeff, sum_range_succ]

/-- The second ordinary BCH coefficient is half the bracket. -/
theorem bchLieCoeff_two (x y : L) : bchLieCoeff x y 2 = (1 / 2 : ℚ) • ⁅x, y⁆ := by
  simp [bchLieCoeff, sum_range_succ,
    symmetricBchLieCoeff_eq_zero_of_even x y 2 (by decide),
    LieAlgebra.ad, LieModule.toEnd, lie_add]

/-- The cubic ordinary BCH coefficient in the classical Hall orientation. -/
theorem bchLieCoeff_three (x y : L) :
    bchLieCoeff x y 3 =
      (1 / 12 : ℚ) • ⁅⁅y, x⁆, x⁆ - (1 / 12 : ℚ) • ⁅⁅y, x⁆, y⁆ := by
  norm_num [-lie_lie, bchLieCoeff, sum_range_succ,
    symmetricBchLieCoeff_eq_zero_of_even x y 2 (by decide), symmetricBchLieCoeff_three,
    symmetricBchCubicLieTerm, pow_succ, Module.End.mul_apply, LieAlgebra.ad,
    LieModule.toEnd, lie_add, add_lie, lie_self, lie_smul, smul_lie, smul_smul]
  rw [← lie_skew x y, lie_neg, ← lie_skew x ⁅y, x⁆]
  module

/-- The quartic ordinary BCH coefficient in the classical Hall orientation. -/
theorem bchLieCoeff_four (x y : L) :
    bchLieCoeff x y 4 = (1 / 24 : ℚ) • ⁅⁅⁅y, x⁆, x⁆, y⁆ := by
  have hcyx : ⁅⁅⁅y, x⁆, y⁆, x⁆ = ⁅⁅⁅y, x⁆, x⁆, y⁆ := by
    rw [lie_lie, ← lie_skew y ⁅⁅y, x⁆, x⁆]
    simp only [lie_self, sub_neg_eq_add, zero_add]
  norm_num [-lie_lie, bchLieCoeff, sum_range_succ,
    symmetricBchLieCoeff_eq_zero_of_even x y 2 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even x y 4 (by decide), symmetricBchLieCoeff_three,
    symmetricBchCubicLieTerm, Nat.factorial, pow_succ, Module.End.mul_apply, LieAlgebra.ad,
    LieModule.toEnd, lie_add, add_lie, lie_self, lie_smul, smul_lie, smul_smul]
  simp only [← lie_skew x y, lie_neg, ← lie_skew x ⁅y, x⁆, lie_neg, neg_neg,
    ← lie_skew x ⁅⁅y, x⁆, x⁆, ← lie_skew x ⁅⁅y, x⁆, y⁆, hcyx]
  module

/-- A fixed sixth-degree Lie polynomial obtained from the cubic and quintic symmetric terms. -/
def bchSexticLieTerm (x y : L) : L :=
  (1 / 2 : ℚ) • (LieAlgebra.ad ℚ L x) (symmetricBchQuinticLieTerm x y) +
    (1 / 48 : ℚ) • (LieAlgebra.ad ℚ L x ^ 3) (symmetricBchCubicLieTerm x y) +
      (1 / 3840 : ℚ) • (LieAlgebra.ad ℚ L x ^ 5) (x + y)

/-- Degree six needs only the known odd symmetric coefficients through degree five. -/
theorem bchLieCoeff_six (x y : L) : bchLieCoeff x y 6 = bchSexticLieTerm x y := by
  norm_num [bchLieCoeff, sum_range_succ, bchSexticLieTerm, Nat.factorial,
    symmetricBchLieCoeff_eq_zero_of_even x y 2 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even x y 4 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even x y 6 (by decide),
    symmetricBchLieCoeff_three, symmetricBchLieCoeff_five]

end FQFP
