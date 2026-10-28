/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.PowerSeries.Noncommutative.AdjointSeries
public import FQFP.Algebra.Lie.PolynomialRealization

import Mathlib.Tactic.Module

/-!
# The differential equation of a symmetric exponential product

The polynomial variable scales the outer exponentials. The series variable
records total homogeneous degree. Polynomial differentiation is valid over
noncommutative coefficients.
-/

@[expose] public noncomputable section

namespace FQFP

open PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Differentiation in the auxiliary polynomial variable, as a rational linear map. -/
def polynomialDerivative : Polynomial A →ₗ[ℚ] Polynomial A :=
  Polynomial.derivative.restrictScalars ℚ

@[simp]
theorem polynomialDerivative_apply (p : Polynomial A) :
    polynomialDerivative p = Polynomial.derivative p := rfl

theorem polynomialDerivative_mul (p q : Polynomial A) :
    polynomialDerivative (p * q) = polynomialDerivative p * q + p * polynomialDerivative q :=
  Polynomial.derivative_mul

/-- A total-degree-one series constant in the auxiliary polynomial variable. -/
def linearSeries (a : A) : PowerSeries (Polynomial A) :=
  PowerSeries.X * PowerSeries.C (Polynomial.C a)

private theorem factorial_succ_cancel (n : ℕ) :
    (Nat.factorial (n + 1) : ℚ)⁻¹ * (n + 1) = (Nat.factorial n : ℚ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (show (n + 1 : ℚ) ≠ 0 by positivity), mul_one]

/-- Differentiation of an exponential whose argument is linear in the auxiliary variable. -/
theorem mapSeriesLinear_polynomialDerivative_exponentialCurve (a : A) :
    mapSeriesLinear polynomialDerivative (exponentialCurve (Polynomial.monomial 1 a)) =
      linearSeries a * exponentialCurve (Polynomial.monomial 1 a) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [linearSeries]
  | succ n =>
    rw [linearSeries, mul_assoc]
    simp only [coeff_mapSeriesLinear, coeff_exponentialCurve, polynomialDerivative_apply,
      Polynomial.derivative_smul, Polynomial.monomial_pow, one_mul,
      Polynomial.derivative_monomial_succ, coeff_succ_X_mul, coeff_C_mul, mul_smul_comm,
      Polynomial.C_mul_monomial, ← pow_succ']
    have hcast : a ^ (n + 1) * (n + 1 : A) = (n + 1 : ℚ) • a ^ (n + 1) := by
      simpa only [← Nat.cast_add_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using
        (Nat.cast_commute (n + 1) (a ^ (n + 1))).symm.eq
    rw [hcast, ← Polynomial.smul_monomial, smul_smul, factorial_succ_cancel]

theorem linearSeries_mul_exponentialCurve (a : A) :
    linearSeries a * exponentialCurve (Polynomial.monomial 1 a) =
      exponentialCurve (Polynomial.monomial 1 a) * linearSeries a := by
  unfold linearSeries
  rw [mul_assoc, ← mul_assoc (exponentialCurve _), ← PowerSeries.X_mul, mul_assoc]
  congr 1
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C, coeff_exponentialCurve,
    mul_smul_comm, smul_mul_assoc, Polynomial.monomial_pow, one_mul,
    Polynomial.C_mul_monomial, Polynomial.monomial_mul_C, ← pow_succ', ← pow_succ]

theorem mapSeriesLinear_polynomialDerivative_exponentialCurve_C (b : A) :
    mapSeriesLinear polynomialDerivative (exponentialCurve (Polynomial.C b)) = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_mapSeriesLinear, coeff_exponentialCurve, polynomialDerivative_apply,
    Polynomial.derivative_smul, ← map_pow, Polynomial.derivative_C, smul_zero, map_zero]

theorem linearSeries_smul (r : ℚ) (a : A) : linearSeries (r • a) = r • linearSeries a := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [linearSeries]
  | succ n =>
    simp only [linearSeries, coeff_succ_X_mul, PowerSeries.coeff_C, coeff_smul]
    split_ifs <;> simp

/-- Symmetric exponential product with the outer arguments scaled by the polynomial variable. -/
def symmetricExponentialSeries (a b : A) : PowerSeries (Polynomial A) :=
  expListSeries [Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a), Polynomial.C b,
    Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a)]

theorem symmetricExponentialSeries_eq_curves (a b : A) :
    symmetricExponentialSeries a b =
      exponentialCurve (Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a)) *
        exponentialCurve (Polynomial.C b) *
        exponentialCurve (Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a)) := by
  rw [symmetricExponentialSeries, expListSeries_cons, expListSeries_cons,
    expListSeries_cons, expListSeries_nil, mul_one]
  simp only [exponentialCurve, mul_assoc]

/-- The differential equation for the symmetric exponential product holds in all degrees. -/
theorem mapSeriesLinear_symmetricExponentialSeries (a b : A) :
    mapSeriesLinear polynomialDerivative (symmetricExponentialSeries a b) =
      (2 : ℚ)⁻¹ • (linearSeries a * symmetricExponentialSeries a b +
        symmetricExponentialSeries a b * linearSeries a) := by
  rw [symmetricExponentialSeries_eq_curves]
  simp only [mapSeriesLinear_mul (polynomialDerivative (A := A))
      (polynomialDerivative_mul (A := A)),
    mapSeriesLinear_polynomialDerivative_exponentialCurve,
    mapSeriesLinear_polynomialDerivative_exponentialCurve_C, mul_zero, add_zero]
  conv_lhs => arg 2; rw [linearSeries_mul_exponentialCurve]
  simp only [linearSeries_smul, smul_mul_assoc, mul_smul_comm, smul_add, mul_assoc]

/-- The symmetric logarithm satisfies the Bernoulli adjoint equation in all total degrees. -/
theorem mapSeriesLinear_formalLog_symmetricExponentialSeries (a b : A) :
    mapSeriesLinear polynomialDerivative (formalLog (symmetricExponentialSeries a b)) =
      adjointSeriesApply (bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • PowerSeries.X)
        (formalLog (symmetricExponentialSeries a b)) (linearSeries a) := by
  apply mapSeriesLinear_formalLog_eq_adjointSeriesApply (polynomialDerivative (A := A))
    (polynomialDerivative_mul (A := A))
  · simp [symmetricExponentialSeries, expListSeries]
  · exact mapSeriesLinear_symmetricExponentialSeries a b

/-- A single nonzero exponent has a linear formal logarithm in every total degree. -/
theorem expListLogCoeff_zero_middle (b : A) (n : ℕ) :
    expListLogCoeff [0, b, 0] n = if n = 1 then b else 0 := by
  rw [← coeff_formalLog_expListSeries]
  have he : expListSeries [0, b, 0] = formalExp (PowerSeries.monomial 1 b) := by
    rw [expListSeries_cons_eq_exponentialCurve, expListSeries_cons_eq_exponentialCurve,
      expListSeries_cons_eq_exponentialCurve, expListSeries_nil,
      exponentialCurve_zero, one_mul, mul_one, mul_one, formalExp_monomial_one]
  rw [he, formalLog_formalExp _ (by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [PowerSeries.coeff_monomial]), PowerSeries.coeff_monomial]

/-- The existing symmetric logarithm coefficient, polynomial in the outer scaling parameter. -/
def symmetricLogPolynomial (a b : A) (n : ℕ) : Polynomial A :=
  expListLogCoeff [Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a), Polynomial.C b,
    Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a)] n

theorem coeff_formalLog_symmetricExponentialSeries (a b : A) (n : ℕ) :
    coeff n (formalLog (symmetricExponentialSeries a b)) = symmetricLogPolynomial a b n :=
  coeff_formalLog_expListSeries _ _

@[simp]
theorem symmetricLogPolynomial_zero (a b : A) : symmetricLogPolynomial a b 0 = 0 := by
  simp [symmetricLogPolynomial]

@[simp]
theorem symmetricLogPolynomial_one (a b : A) :
    symmetricLogPolynomial a b 1 = Polynomial.C b + Polynomial.monomial 1 a := by
  simp only [symmetricLogPolynomial, expListLogCoeff_one, List.sum_cons, List.sum_nil,
    add_zero, ← Polynomial.smul_monomial]
  module

private def polynomialConstantCoeff : Polynomial A →ₐ[ℚ] A where
  toRingHom := Polynomial.constantCoeff
  commutes' r := by
    change (Polynomial.C (algebraMap ℚ A r)).coeff 0 = algebraMap ℚ A r
    exact Polynomial.coeff_C_zero

/-- At auxiliary time zero, the symmetric logarithm has only the middle linear coefficient. -/
theorem constantCoeff_symmetricLogPolynomial (a b : A) (n : ℕ) :
    (symmetricLogPolynomial a b n).coeff 0 = if n = 1 then b else 0 := by
  have h := map_expListLogCoeff (polynomialConstantCoeff (A := A))
    [Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a), Polynomial.C b,
      Polynomial.monomial 1 ((2 : ℚ)⁻¹ • a)] n
  simpa [polynomialConstantCoeff, symmetricLogPolynomial, expListLogCoeff_zero_middle] using h

end FQFP
