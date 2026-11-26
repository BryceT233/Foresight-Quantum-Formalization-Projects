/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Carleman.TwoModeBurgers.Algebra

/-!
# Lie derivatives of two-mode monomials

The formula here identifies every possible monomial transition. It is the
algebraic input for degree growth and for finite monomial dictionaries.

## Main results

* `TwoModeBurgers.coeff_pow_mul_pow_mul`: coefficients after multiplying by `aᵏ bˡ`.
* `TwoModeBurgers.lieDerivation_pow_mul_pow`: the full action on `aⁱbʲ`.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The product of the two coordinate powers is the monomial with their exponent pair. -/
lemma pow_mul_pow_eq_monomial (i j : ℕ) :
    (X 0 : MvPolynomial (Fin 2) R) ^ i * X 1 ^ j =
      monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 := by
  simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]

/-- Multiplication by `aᵏ bˡ` shifts both exponents. A coefficient below either shift is zero. -/
lemma coeff_pow_mul_pow_mul (p : MvPolynomial (Fin 2) R) (k l i j : ℕ) :
    (X 0 ^ k * X 1 ^ l * p).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      if k ≤ i ∧ l ≤ j then p.coeff (Finsupp.single 0 (i - k) + Finsupp.single 1 (j - l))
      else 0 := by
  have hsub : (Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ) -
      (Finsupp.single 0 k + Finsupp.single 1 l) =
        Finsupp.single 0 (i - k) + Finsupp.single 1 (j - l) := by
    ext t
    fin_cases t <;> simp
  rw [pow_mul_pow_eq_monomial, coeff_monomial_mul', hsub]
  simp [Finsupp.le_def, Fin.forall_fin_two]

/-- Multiplying by `aᵏ` shifts the first exponent by `k`. -/
lemma coeff_first_pow_mul (p : MvPolynomial (Fin 2) R) (k i j : ℕ) :
    (X 0 ^ k * p).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      if k ≤ i then p.coeff (Finsupp.single 0 (i - k) + Finsupp.single 1 j) else 0 := by
  simpa using coeff_pow_mul_pow_mul p k 0 i j

/-- Multiplying by `bᵏ` shifts the second exponent by `k`. -/
lemma coeff_second_pow_mul (p : MvPolynomial (Fin 2) R) (k i j : ℕ) :
    (X 1 ^ k * p).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      if k ≤ j then p.coeff (Finsupp.single 0 i + Finsupp.single 1 (j - k)) else 0 := by
  simpa using coeff_pow_mul_pow_mul p 0 k i j

/-- The Lie derivative of `aⁱbʲ`; the final term vanishes when `j = 0`. -/
theorem lieDerivation_pow_mul_pow (α γ β : ℝ) (i j : ℕ) :
    (mkDerivation ℝ (vectorField α γ β))
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j) =
      -C (α * (i : ℝ) + γ * (j : ℝ)) * X 0 ^ i * X 1 ^ j +
        C (β * (i : ℝ)) * X 0 ^ i * X 1 ^ (j + 1) -
          C (β * (j : ℝ)) * X 0 ^ (i + 2) * X 1 ^ (j - 1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow,
    mkDerivation_X, mkDerivation_X]
  simp only [vectorField, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]
  cases i <;> cases j <;>
    simp only [Nat.succ_sub_one, Nat.cast_succ, Nat.cast_zero, nsmul_eq_mul, pow_zero,
      map_add, map_mul, map_natCast, map_zero, map_one] <;> ring

end TwoModeBurgers
