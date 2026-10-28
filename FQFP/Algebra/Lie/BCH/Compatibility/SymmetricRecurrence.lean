/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.GradedRealization

/-!
# All-degree equivalence of the symmetric homogeneous recursion

The existing logarithm coefficients satisfy the same initial values and
triangular differential equation as the Lie recursion. Uniqueness therefore
identifies them in every homogeneous degree over an arbitrary rational algebra.
The proof imports no finite BCH coefficient certificate or word table.
-/

@[expose] public noncomputable section

namespace FQFP

open PolynomialModule PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Lie homogeneous recursion realizes the existing symmetric logarithm in every degree. -/
theorem toPolynomial_symmetricBchHomogeneous (a b : A) (n : ℕ) :
    toPolynomial (symmetricBchHomogeneous a b n) = symmetricLogPolynomial a b n := by
  let u := fun k ↦ ofPolynomial (symmetricLogPolynomial a b k)
  have hs : homogeneousLieSeries u = formalLog (symmetricExponentialSeries a b) := by
    apply PowerSeries.ext
    intro k
    cases k with
    | zero =>
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_homogeneousLieSeries,
        coeff_zero_eq_constantCoeff_apply, constantCoeff_formalLog]
    | succ k =>
      rw [homogeneousLieSeries, coeff_positiveSeries_succ,
        coeff_formalLog_symmetricExponentialSeries]
      exact toPolynomial_ofPolynomial _
  have hu : u = symmetricBchHomogeneous a b := by
    apply symmetricBchHomogeneous_unique
    · simp [u]
    · apply toPolynomial_injective
      simp [u]
    · intro k hk
      change (symmetricLogPolynomial a b k).coeff 0 = 0
      rw [constantCoeff_symmetricLogPolynomial, ite_eq_right (by lia : k ≠ 1)]
    · intro k hk
      apply toPolynomial_injective
      change toPolynomial (PolynomialModule.derivative
        (ofPolynomial (symmetricLogPolynomial a b k))) = toPolynomial (symmetricBchRhs u a k)
      rw [toPolynomial_derivative, toPolynomial_ofPolynomial]
      have hd := congrArg (PowerSeries.coeff k)
        (mapSeriesLinear_formalLog_symmetricExponentialSeries a b)
      simp only [coeff_mapSeriesLinear, polynomialDerivative_apply,
        coeff_formalLog_symmetricExponentialSeries] at hd
      rw [← hs, coeff_adjointSeriesApply_eq_symmetricBchRhs u a k hk] at hd
      exact hd
  rw [← congrFun hu n]
  exact toPolynomial_ofPolynomial _

/-- Auxiliary rational evaluation of the Lie recursion equals the existing logarithm coefficient. -/
theorem eval_symmetricBchHomogeneous_eq_expListLogCoeff (a b : A) (n : ℕ) (r : ℚ) :
    PolynomialModule.eval r (symmetricBchHomogeneous a b n) =
      expListLogCoeff [((r / 2 : ℚ) • a), b, ((r / 2 : ℚ) • a)] n := by
  rw [← eval_toPolynomial, toPolynomial_symmetricBchHomogeneous, symmetricLogPolynomial,
    map_expListLogCoeff]
  simp only [List.map_cons, List.map_nil, evalPolynomial_monomial, pow_one, evalPolynomial_C,
    smul_smul, div_eq_mul_inv]

/-- At time one, the recursive Lie coefficient equals the existing coefficient in all degrees. -/
theorem symmetricBchLieCoeff_eq_expListLogCoeff (a b : A) (n : ℕ) :
    symmetricBchLieCoeff a b n =
      expListLogCoeff [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)] n := by
  simpa [symmetricBchLieCoeff] using
    eval_symmetricBchHomogeneous_eq_expListLogCoeff a b n (1 : ℚ)

/-- Every even symmetric logarithm coefficient vanishes, independently of any finite certificate. -/
theorem expListLogCoeff_symmetric_eq_zero_of_even (a b : A) (n : ℕ) (hn : Even n) :
    expListLogCoeff [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)] n = 0 := by
  rw [← symmetricBchLieCoeff_eq_expListLogCoeff, symmetricBchLieCoeff,
    symmetricBchHomogeneous_eq_zero_of_even a b n hn, map_zero]

end FQFP
