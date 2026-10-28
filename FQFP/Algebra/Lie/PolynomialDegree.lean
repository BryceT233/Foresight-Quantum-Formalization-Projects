/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.Polynomial
public import FQFP.Algebra.Polynomial.Module.Degree
public import Mathlib.Tactic.Linarith

/-!
# Degree bounds for vector-valued polynomials

`DegreeLE p n` means that coefficients above `n` vanish, including when the
coefficient space is trivial. The integral and Lie bracket bounds justify
pruning the auxiliary polynomial degree in homogeneous recursions.
-/

@[expose] public noncomputable section

namespace PolynomialModule

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

private theorem le_of_mem_support {p : PolynomialModule ℚ M} {n i : ℕ}
    (hp : DegreeLE p n) (hi : i ∈ p.coeff.support) : i ≤ n :=
  hp.le_of_mem_support hi

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- A convolution bracket adds the auxiliary polynomial degree bounds. -/
theorem DegreeLE.lieBracket {p q : PolynomialModule ℚ L} {m n : ℕ}
    (hp : DegreeLE p m) (hq : DegreeLE q n) : DegreeLE (lieBracket p q) (m + n) := by
  rw [lieBracket_eq_sum]
  apply degreeLE_sum
  intro i hi
  apply degreeLE_sum
  intro j hj
  exact degreeLE_single _ (Nat.add_le_add (le_of_mem_support hp hi) (le_of_mem_support hq hj))

end PolynomialModule
