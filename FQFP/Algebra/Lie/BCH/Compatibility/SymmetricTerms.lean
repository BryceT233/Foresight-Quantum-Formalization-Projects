/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SymmetricTerms
public import FQFP.Algebra.Lie.BCH.Associative.SymmetricTerms
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Module

/-!
# Compatibility of the symmetric BCH polynomial presentations

The cubic and quintic Lie polynomials agree with the existing associative
presentations. These equalities depend only on the polynomial definitions,
without importing a finite logarithm identity or the homogeneous recursion.
-/

@[expose] public section

namespace FQFP.BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The ordered-word quintic symmetric BCH coefficient is the six-bracket Lie polynomial. -/
theorem symmetricBchQuinticTerm_eq_lieTerm
    {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    symmetricBchQuinticTerm a b = symmetricBchQuinticLieTerm a b := by
  simp only [symmetricBchQuinticTerm, symmetricBchQuinticTermTable,
    WordTable.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.prod_cons, List.prod_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, div_one,
    symmetricBchQuinticLieTerm, Ring.lie_def, mul_sub, sub_mul,
    mul_one, ← mul_assoc]
  module

/-- The existing cubic commutator and the cubic Lie expression use the same convention. -/
theorem symmetricBchCubicTerm_eq_lieTerm
    {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    symmetricBchCubicTerm a b = symmetricBchCubicLieTerm a b := by
  simp only [symmetricBchCubicTerm, symmetricBchCubicLieTerm,
    Ring.lie_def, mul_sub, sub_mul, ← mul_assoc]
  module

end FQFP.BCH
