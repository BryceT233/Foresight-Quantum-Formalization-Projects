/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SymmetricRecurrence
public import FQFP.Algebra.Lie.BCH.SymmetricTerms

import Mathlib.Tactic.Module
import Mathlib.Tactic.DefEqTransformations

/-!
# Low-degree Lie regressions of the homogeneous recursion

These identities are derived by Lie convolution and Jacobi, with no conversion
to associative words. The auxiliary polynomial retains its actual powers.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PolynomialModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp]
theorem symmetricBchHomogeneous_two (x y : L) : symmetricBchHomogeneous x y 2 = 0 :=
  symmetricBchHomogeneous_eq_zero_of_even x y 2 (by decide)

/-- The cubic coefficient polynomial has auxiliary degrees one and two. -/
theorem symmetricBchHomogeneous_three (x y : L) :
    symmetricBchHomogeneous x y 3 =
      (-1 / 12 : ℚ) • single ℚ 1 ⁅⁅y, x⁆, y⁆ +
        (-1 / 24 : ℚ) • single ℚ 2 ⁅⁅y, x⁆, x⁆ := by
  rw [symmetricBchHomogeneous_eq_integral x y 3 (by decide)]
  norm_num [-lie_lie, symmetricBchRhs, sum_range_succ, bernoulli_two]
  norm_num [positiveAdCoeff, sum_range_succ, symmetricBchHomogeneous_one,
    lieBracket_single, LinearMap.add_apply, add_lie, lie_add, lie_self, smul_smul, -lie_lie]
  rw [← lie_skew y ⁅y, x⁆, ← lie_skew x ⁅y, x⁆]
  simp only [single_neg, smul_neg]

private theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  norm_num [bernoulli, bernoulli', Fin.sum_univ_succ]

/-- The recursive quintic is the six-bracket Hall expression in every rational Lie algebra. -/
theorem symmetricBchLieCoeff_five (x y : L) :
    symmetricBchLieCoeff x y 5 = symmetricBchQuinticLieTerm x y := by
  let c := ⁅y, x⁆
  let cx := ⁅c, x⁆
  let cy := ⁅c, y⁆
  let cxx := ⁅cx, x⁆
  let cxy := ⁅cx, y⁆
  let cyy := ⁅cy, y⁆
  have hinter (u : L) : ⁅⁅u, y⁆, x⁆ = ⁅⁅u, x⁆, y⁆ + ⁅u, c⁆ := by
    rw [lie_lie, ← lie_skew y ⁅u, x⁆]
    module
  have hcyx : ⁅cy, x⁆ = cxy := by simpa only [lie_self, add_zero] using hinter c
  have hcyyx : ⁅cyy, x⁆ = ⁅cxy, y⁆ + ⁅cy, c⁆ := by
    simpa only [hcyx] using hinter cy
  have hcxyx : ⁅cxy, x⁆ = ⁅cxx, y⁆ + ⁅cx, c⁆ := hinter cx
  rw [symmetricBchLieCoeff, symmetricBchHomogeneous_eq_integral x y 5 (by decide)]
  norm_num [-lie_lie, symmetricBchRhs, sum_range_succ, bernoulli_two, bernoulli_four, Nat.factorial]
  norm_num [-lie_lie, positiveAdCoeff, sum_range_succ, symmetricBchHomogeneous_one,
    symmetricBchHomogeneous_two, symmetricBchHomogeneous_three, lieBracket_single,
    LinearMap.add_apply, add_lie, lie_add, lie_self, smul_lie, lie_smul, smul_smul]
  simp only [symmetricBchQuinticLieTerm]
  refold_let c cx cy cxx cxy cyy
  simp only [← lie_skew x c, ← lie_skew y c, lie_neg]
  refold_let cx cy
  simp only [← lie_skew x cx, ← lie_skew y cx, ← lie_skew x cy, ← lie_skew y cy,
    lie_neg, neg_neg, hcyx]
  refold_let cxx cxy cyy
  simp only [← lie_skew x cxx, ← lie_skew y cxx, ← lie_skew x cxy, ← lie_skew y cxy,
    ← lie_skew x cyy, ← lie_skew y cyy, hcyyx, hcxyx]
  module

@[simp]
theorem symmetricBchLieCoeff_zero (x y : L) : symmetricBchLieCoeff x y 0 = 0 := by
  simp [symmetricBchLieCoeff]

@[simp]
theorem symmetricBchLieCoeff_one (x y : L) : symmetricBchLieCoeff x y 1 = x + y := by
  simp [symmetricBchLieCoeff, add_comm]

/-- The recursive cubic coefficient is the cubic Hall expression. -/
theorem symmetricBchLieCoeff_three (x y : L) :
    symmetricBchLieCoeff x y 3 = symmetricBchCubicLieTerm x y := by
  simp [-lie_lie, symmetricBchLieCoeff, symmetricBchHomogeneous_three,
    symmetricBchCubicLieTerm, add_comm]

/-- Every even Lie coefficient vanishes in the abstract Lie algebra recursion. -/
theorem symmetricBchLieCoeff_eq_zero_of_even (x y : L) (n : ℕ) (hn : Even n) :
    symmetricBchLieCoeff x y n = 0 := by
  rw [symmetricBchLieCoeff, symmetricBchHomogeneous_eq_zero_of_even x y n hn, map_zero]

end FQFP
