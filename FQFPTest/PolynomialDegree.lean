/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.Algebra.Polynomial.Module.Degree

/-!
# Polynomial-module degree bounds without a Lie structure

The generic module alone supplies support bounds and the degree bound on primitives.
-/

open PolynomialModule

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

example (x : M) : DegreeLE (integralZero (single ℚ 0 x)) 1 := by
  exact (degreeLE_single (n := 0) x (by lia)).integralZero

example {p : PolynomialModule ℚ M} {n i : ℕ}
    (hp : DegreeLE p n) (hi : i ∈ p.coeff.support) : i ≤ n :=
  hp.le_of_mem_support hi
