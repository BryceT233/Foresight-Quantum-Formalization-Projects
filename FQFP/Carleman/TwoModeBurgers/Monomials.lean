/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Algebra

/-!
# Lie derivatives of two-mode monomials

The formula here identifies every possible monomial transition. It is the
algebraic input for degree growth and for finite monomial dictionaries.

## Main result

* `TwoModeBurgers.lieDerivation_pow_mul_pow`: the full action on `aⁱbʲ`.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

/-- The Lie derivative of `aⁱbʲ`; the final term vanishes when `j = 0`. -/
theorem lieDerivation_pow_mul_pow (α γ β : ℝ) (i j : ℕ) :
    (mkDerivation ℝ (vectorField α γ β))
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j) =
      -C (α * (i : ℝ) + γ * (j : ℝ)) * X 0 ^ i * X 1 ^ j +
        C (β * (i : ℝ)) * X 0 ^ i * X 1 ^ (j + 1) -
          C (β * (j : ℝ)) * X 0 ^ (i + 2) * X 1 ^ (j - 1) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
  rw [mkDerivation_X, mkDerivation_X]
  simp only [vectorField, Matrix.cons_val_zero, Matrix.cons_val_one, map_neg]
  cases i with
  | zero =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [pow_zero, zero_add, Nat.zero_sub, Nat.succ_sub_one,
        Nat.cast_zero, mul_zero, Nat.cast_succ, nsmul_eq_mul]
      simp only [map_add, map_mul, map_natCast, map_zero, map_one, mul_one]
      ring
  | succ i =>
    cases j with
    | zero =>
      simp only [pow_zero, mul_one, Nat.zero_sub, Nat.succ_sub_one,
        Nat.cast_zero, mul_zero, Nat.cast_succ, nsmul_eq_mul]
      simp only [map_add, map_mul, map_natCast, map_zero, map_one]
      ring
    | succ j =>
      simp only [Nat.succ_sub_one, Nat.cast_succ, nsmul_eq_mul]
      simp only [map_add, map_mul, map_natCast, map_one]
      ring

end TwoModeBurgers
