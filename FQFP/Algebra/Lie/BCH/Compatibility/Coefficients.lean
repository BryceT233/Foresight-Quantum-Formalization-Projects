/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Coefficients
public import FQFP.Algebra.Lie.BCH.Compatibility.SymmetricRecurrence
public import FQFP.RingTheory.PowerSeries.Noncommutative.Conjugation
public import FQFP.RingTheory.PowerSeries.Noncommutative.ExponentialProduct

/-!
# Conjugation identifies ordinary and symmetric BCH coefficients

The ordinary exponential product is conjugate to the symmetric product by
`exp(t a / 2)`. Formal logarithm equivariance and the exponential adjoint action
identify the coefficients in every degree, without finite word certificates.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exponentialCurve_half_mul_self (a : A) :
    exponentialCurve ((2 : ℚ)⁻¹ • a) * exponentialCurve ((2 : ℚ)⁻¹ • a) =
      exponentialCurve a := by
  have hz : constantCoeff (monomial 1 a) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [coeff_monomial]
  have h := formalExp_add_smul (monomial 1 a) hz (2 : ℚ)⁻¹ (2 : ℚ)⁻¹
  norm_num at h
  have hs : ((1 / 2 : ℚ) • monomial 1 a) = monomial 1 ((2 : ℚ)⁻¹ • a) := by
    ext n
    simp only [coeff_smul, coeff_monomial]
    split_ifs <;> simp
  simpa only [hs, formalExp_monomial_one] using h

/-- The ordinary product is the conjugate of the symmetric three-factor product. -/
theorem expListSeries_eq_conjugate_symmetric (a b : A) :
    expListSeries [a, b] =
      exponentialCurve ((2 : ℚ)⁻¹ • a) *
        expListSeries [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)] *
          exponentialCurve (-((2 : ℚ)⁻¹ • a)) := by
  simp only [expListSeries_cons_eq_exponentialCurve, expListSeries_nil, mul_one,
    mul_assoc, exponentialCurve_mul_neg]
  rw [← mul_assoc, exponentialCurve_half_mul_self]

/-- Formal logarithms of the two products are related by the exponential adjoint action. -/
theorem formalLog_expListSeries_eq_conjugate_symmetric (a b : A) :
    formalLog (expListSeries [a, b]) =
      exponentialCurve ((2 : ℚ)⁻¹ • a) *
        formalLog (expListSeries [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)]) *
          exponentialCurve (-((2 : ℚ)⁻¹ • a)) := by
  rw [expListSeries_eq_conjugate_symmetric,
    formalLog_conjugate _ _ _ (exponentialCurve_mul_neg _) (by
      simpa only [neg_neg] using exponentialCurve_mul_neg (-((2 : ℚ)⁻¹ • a)))]
  simp [expListSeries]

/-- In every degree, ordinary BCH coefficients are the conjugated symmetric coefficients. -/
theorem expListLogCoeff_eq_sum_ad_symmetric (a b : A) (n : ℕ) :
    expListLogCoeff [a, b] n =
      ∑ j ∈ range (n + 1), ((2 : ℚ) ^ j * (Nat.factorial j : ℚ))⁻¹ •
        (LieAlgebra.ad ℚ A a ^ j)
          (expListLogCoeff [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)] (n - j)) := by
  rw [← coeff_formalLog_expListSeries,
    formalLog_expListSeries_eq_conjugate_symmetric, coeff_exponentialCurve_conjugate]
  apply sum_congr rfl
  intro j hj
  simp only [coeff_formalLog_expListSeries, map_smul, smul_pow, LinearMap.smul_apply,
    smul_smul, mul_inv_rev, inv_pow]

/-- The abstract Lie coefficient equals the associative logarithm coefficient in every degree. -/
theorem bchLieCoeff_eq_expListLogCoeff (a b : A) (n : ℕ) :
    bchLieCoeff a b n = expListLogCoeff [a, b] n := by
  rw [expListLogCoeff_eq_sum_ad_symmetric, bchLieCoeff]
  simp only [symmetricBchLieCoeff_eq_expListLogCoeff]

/-- Every finite ordinary logarithm is the sum of its abstract BCH Lie coefficients. -/
theorem sum_logCoeff_positivePowerTrunc_eq_sum_bchLieCoeff (a b : A) (m : ℕ) :
    (∑ k ∈ range m, logCoeff k • positivePowerTrunc (expMulTerm a b) k m) =
      ∑ n ∈ range m, bchLieCoeff a b n := by
  rw [← funext (expListTerm_pair a b), ← sum_expListLogCoeff]
  simp only [bchLieCoeff_eq_expListLogCoeff]

end FQFP
