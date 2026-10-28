/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Formal calculus for polynomial modules

Coefficientwise differentiation and the primitive with zero constant coefficient
for rational vector-valued polynomials, together with linear-map compatibility.
These are algebraic operations on the auxiliary polynomial variable.
-/

@[expose] public noncomputable section

namespace PolynomialModule

variable {M N : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N]

/-- Extend a family of linear maps from the monomials of a polynomial module. -/
def lift (f : ℕ → M →ₗ[ℚ] N) : PolynomialModule ℚ M →ₗ[ℚ] N :=
  (Finsupp.lsum ℚ f).comp (coeffLinearEquiv ℚ ℚ).toLinearMap

@[simp]
theorem lift_single (f : ℕ → M →ₗ[ℚ] N) (n : ℕ) (m : M) :
    lift f (single ℚ n m) = f n m := by
  exact Finsupp.lsum_single ℚ f n m

@[simp]
theorem single_neg (n : ℕ) (m : M) : single ℚ n (-m) = -single ℚ n m :=
  (lsingle ℚ n).map_neg m

/-- Differentiation in the polynomial variable. -/
def derivative : PolynomialModule ℚ M →ₗ[ℚ] PolynomialModule ℚ M :=
  lift fun n ↦ (n : ℚ) • lsingle ℚ (n - 1)

/-- Integration in the polynomial variable with constant coefficient zero. -/
def integralZero : PolynomialModule ℚ M →ₗ[ℚ] PolynomialModule ℚ M :=
  lift fun n ↦ (n + 1 : ℚ)⁻¹ • lsingle ℚ (n + 1)

@[simp]
theorem derivative_single (n : ℕ) (m : M) :
    derivative (single ℚ n m) = (n : ℚ) • single ℚ (n - 1) m := by
  simp [derivative, lsingle]

@[simp]
theorem integralZero_single (n : ℕ) (m : M) :
    integralZero (single ℚ n m) = (n + 1 : ℚ)⁻¹ • single ℚ (n + 1) m := by
  simp [integralZero, lsingle]

@[simp]
theorem derivative_integralZero (p : PolynomialModule ℚ M) :
    derivative (integralZero p) = p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n m =>
    simp [smul_smul, inv_mul_cancel₀ (show (n + 1 : ℚ) ≠ 0 by positivity)]

@[simp]
theorem coeff_integralZero_zero (p : PolynomialModule ℚ M) :
    (integralZero p).coeff 0 = 0 := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n m => simp [← single_smul]

/-- Integrating the derivative removes exactly the constant coefficient. -/
theorem integralZero_derivative (p : PolynomialModule ℚ M) :
    integralZero (derivative p) = p - single ℚ 0 (p.coeff 0) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, sub_add_sub_comm]
  | single n m =>
    cases n with
    | zero => simp
    | succ n =>
      simp [smul_smul, mul_inv_cancel₀ (show (n + 1 : ℚ) ≠ 0 by positivity)]

/-- A polynomial is determined by its derivative and its constant coefficient. -/
theorem ext_derivative {p q : PolynomialModule ℚ M}
    (hd : derivative p = derivative q) (hc : p.coeff 0 = q.coeff 0) : p = q := by
  have h := congrArg integralZero hd
  rw [integralZero_derivative, integralZero_derivative, hc] at h
  exact sub_left_injective h

/-- Linear maps commute with the zero-constant primitive. -/
theorem map_integralZero (f : M →ₗ[ℚ] N) (p : PolynomialModule ℚ M) :
    map ℚ f (integralZero p) = integralZero (map ℚ f p) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n m => simp

end PolynomialModule
