/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.Polynomial
public import FQFP.Algebra.Polynomial.Module.Polynomial

/-!
# Lie bracket and polynomial realization

The coefficient algebra may be noncommutative; the finite Lie convolution realizes its commutator.

## Main results

* `PolynomialModule.toPolynomial_lieBracket`: realization respects the Lie bracket.
-/

@[expose] public noncomputable section

namespace PolynomialModule

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The finite Lie convolution is the commutator of polynomial realizations. -/
theorem toPolynomial_lieBracket (p q : PolynomialModule ℚ A) :
    toPolynomial (lieBracket p q) = ⁅toPolynomial p, toPolynomial q⁆ := by
  induction p using induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp', add_lie]
  | single i a =>
    induction q using induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq', lie_add]
    | single j b =>
      simp [Ring.lie_def, Polynomial.monomial_mul_monomial, add_comm]

end PolynomialModule
