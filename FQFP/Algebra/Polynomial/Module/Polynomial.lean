/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Polynomial.Module.Calculus
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Ordinary realizations of polynomial modules

Finite module coefficients realize central-variable polynomials over noncommutative algebras.

## Main results

* `PolynomialModule.toPolynomial`, `PolynomialModule.ofPolynomial`: inverse realizations.
* `PolynomialModule.eval_toPolynomial`, `PolynomialModule.toPolynomial_derivative`: compatibility.
-/

@[expose] public section
noncomputable section

namespace PolynomialModule

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Realize a polynomial module over an associative algebra as a central-variable polynomial. -/
def toPolynomial : PolynomialModule ℚ A →ₗ[ℚ] Polynomial A where
  toFun p := Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff p.coeff)
  map_add' p q := by ext n; simp
  map_smul' r p := by ext n; rfl

@[simp]
theorem coeff_toPolynomial (p : PolynomialModule ℚ A) (n : ℕ) :
    (toPolynomial p).coeff n = p.coeff n := rfl

theorem toPolynomial_injective : Function.Injective (toPolynomial (A := A)) := by
  intro p q h
  apply PolynomialModule.ext
  ext n
  exact congrArg (fun r : Polynomial A ↦ r.coeff n) h

@[simp]
theorem toPolynomial_single (n : ℕ) (a : A) :
    toPolynomial (single ℚ n a) = Polynomial.monomial n a := rfl

/-- View an ordinary polynomial as a finite vector-valued polynomial. -/
def ofPolynomial : Polynomial A →ₗ[ℚ] PolynomialModule ℚ A where
  toFun p := ofCoeff ℚ p.coeff
  map_add' p q := by ext n; simp
  map_smul' r p := by ext n; rfl

@[simp]
theorem coeff_ofPolynomial (p : Polynomial A) (n : ℕ) :
    (ofPolynomial p).coeff n = p.coeff n := rfl

@[simp]
theorem toPolynomial_ofPolynomial (p : Polynomial A) : toPolynomial (ofPolynomial p) = p := rfl

@[simp]
theorem ofPolynomial_toPolynomial (p : PolynomialModule ℚ A) :
    ofPolynomial (toPolynomial p) = p := rfl

/-- Evaluate the central polynomial variable at a rational scalar in the coefficient algebra. -/
def evalPolynomial (r : ℚ) : Polynomial A →ₐ[ℚ] A :=
  Polynomial.eval₂AlgHom (AlgHom.id ℚ A) (algebraMap ℚ A r)
    (fun a ↦ Algebra.commute_algebraMap_right r ((AlgHom.id ℚ A) a))

@[simp]
theorem evalPolynomial_C (r : ℚ) (a : A) : evalPolynomial r (Polynomial.C a) = a := by
  simp [evalPolynomial]

theorem evalPolynomial_monomial (r : ℚ) (n : ℕ) (a : A) :
    evalPolynomial r (Polynomial.monomial n a) = r ^ n • a := by
  simp only [evalPolynomial, Polynomial.eval₂AlgHom_apply, Polynomial.eval₂_monomial,
    AlgHom.id_toRingHom, RingHom.id_apply]
  rw [← map_pow, ← Algebra.commutes (r ^ n) a, Algebra.smul_def]

/-- Central rational evaluation agrees with polynomial-module evaluation. -/
theorem eval_toPolynomial (r : ℚ) (p : PolynomialModule ℚ A) :
    evalPolynomial r (toPolynomial p) = eval r p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n a => rw [toPolynomial_single, evalPolynomial_monomial, eval_single]

/-- Differentiation is preserved by polynomial realization. -/
theorem toPolynomial_derivative (p : PolynomialModule ℚ A) :
    toPolynomial (derivative p) = Polynomial.derivative (toPolynomial p) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n a =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [derivative_single, Nat.add_sub_cancel, LinearMap.map_smul, toPolynomial_single,
        Polynomial.derivative_monomial_succ]
      rw [Polynomial.smul_monomial]
      congr 1
      simp only [← Nat.cast_add_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      exact (Nat.cast_commute _ _).eq

end PolynomialModule
