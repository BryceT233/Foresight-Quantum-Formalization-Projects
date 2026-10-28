/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Compatibility.Coefficients
public import FQFP.Algebra.Lie.BCH.LowDegree
public import FQFP.Algebra.Lie.BCH.Associative.Terms

import Mathlib.Tactic.Module

/-!
# Compatibility with the existing low-degree BCH polynomials

The cubic and quartic coefficients use the existing polynomial definitions.
The sixth-degree logarithm also has a fixed Lie expression obtained from the
known symmetric coefficients, without a new word certificate.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The cubic coefficient agrees with the existing ordinary BCH polynomial. -/
theorem bchLieCoeff_three_eq_bchCubicTerm (a b : A) :
    bchLieCoeff a b 3 = bchCubicTerm a b := by
  rw [bchLieCoeff_three]
  simp only [bchCubicTerm, Ring.lie_def, mul_sub, sub_mul, ← mul_assoc]
  module

/-- The quartic coefficient agrees with the existing ordinary BCH polynomial. -/
theorem bchLieCoeff_four_eq_bchQuarticTerm (a b : A) :
    bchLieCoeff a b 4 = bchQuarticTerm a b := by
  rw [bchLieCoeff_four]
  simp only [bchQuarticTerm, Ring.lie_def, mul_sub, sub_mul, ← mul_assoc]
  module

/-- The sixth logarithm coefficient is the fixed conjugation expression in Lie brackets. -/
theorem expListLogCoeff_pair_six_eq_lieTerm (a b : A) :
    expListLogCoeff [a, b] 6 = bchSexticLieTerm a b := by
  rw [← bchLieCoeff_eq_expListLogCoeff, bchLieCoeff_six]

end FQFP.BCH
