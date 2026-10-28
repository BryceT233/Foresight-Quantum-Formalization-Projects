/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Compatibility.SymmetricTerms
public import FQFP.Algebra.Lie.BCH.SymmetricCoefficients
public import FQFP.Algebra.Lie.BCH.Associative.SymmetricSeries

/-!
# The Lie presentation of the symmetric quintic BCH coefficient

The polynomial presentation equalities are re-exported from a lower compatibility
module. This outer consumer combines them with the finite logarithm through degree
six, whose odd coefficients retain the existing word certificates.

## Main results

* `FQFP.BCH.symmetricBchQuinticTerm_eq_lieTerm`: equality of the two presentations.
* `FQFP.BCH.sum_logCoeff_positivePowerTrunc_eq_symmetric_lieTerm`: the finite logarithm.
-/

@[expose] public section

namespace FQFP.BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The finite symmetric logarithm through degree six uses the quintic Lie polynomial. -/
theorem sum_logCoeff_positivePowerTrunc_eq_symmetric_lieTerm
    {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    (∑ k ∈ Finset.range 7, logCoeff k •
      positivePowerTrunc
        (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k 7) =
      (a + b) + symmetricBchCubicTerm a b + symmetricBchQuinticLieTerm a b := by
  rw [sum_logCoeff_positivePowerTrunc_eq_symmetric, symmetricBchQuinticTerm_eq_lieTerm]

end FQFP.BCH
