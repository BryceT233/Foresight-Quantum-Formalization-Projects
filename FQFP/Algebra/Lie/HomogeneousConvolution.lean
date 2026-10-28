/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.Polynomial
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith

/-!
# Positive homogeneous adjoint convolution

`positiveAdCoeff u x j n` is the coefficient of total degree `n` in
`ad_U^j (t x)`, where `U = ∑_{i ≥ 1} t^i u_i`. The polynomial variable
inside each `u_i` is separate from `t`. No associative words are constructed.

## Main results

* `positiveAdCoeff_eq_zero_of_lt`: each bracket raises the minimum total degree.
* `positiveAdCoeff_congr`: the coefficient reads only degrees at most `n - j`.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PolynomialModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The homogeneous coefficient of an iterated adjoint applied to a degree-one element. -/
def positiveAdCoeff (u : ℕ → PolynomialModule ℚ L) (x : L) :
    ℕ → ℕ → PolynomialModule ℚ L
  | 0, n => if n = 1 then single ℚ 0 x else 0
  | j + 1, n => ∑ i ∈ range (n - (j + 1)),
      lieBracket (u (i + 1)) (positiveAdCoeff u x j (n - (i + 1)))

@[simp]
theorem positiveAdCoeff_zero (u : ℕ → PolynomialModule ℚ L) (x : L) (n : ℕ) :
    positiveAdCoeff u x 0 n = if n = 1 then single ℚ 0 x else 0 := rfl

/-- Every adjoint increases the minimum homogeneous degree by one. -/
theorem positiveAdCoeff_eq_zero_of_lt (u : ℕ → PolynomialModule ℚ L) (x : L)
    (j n : ℕ) (h : n < j + 1) : positiveAdCoeff u x j n = 0 := by
  cases j with
  | zero => simp [positiveAdCoeff, show n ≠ 1 by lia]
  | succ j => simp [positiveAdCoeff, Nat.sub_eq_zero_of_le (by lia : n ≤ j + 1)]

/-- Only positive homogeneous degrees at most `n - j` contribute. -/
theorem positiveAdCoeff_congr (u v : ℕ → PolynomialModule ℚ L) (x : L) (j n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n - j → u i = v i) :
    positiveAdCoeff u x j n = positiveAdCoeff v x j n := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [positiveAdCoeff]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [h (i + 1) (by lia) (by lia)]
    congr 1
    apply ih
    intro k hk hkn
    exact h k hk (by lia)

/-- If the input has only odd degrees, the `j`th adjoint has parity `j + 1`. -/
theorem positiveAdCoeff_eq_zero_of_parity (u : ℕ → PolynomialModule ℚ L) (x : L)
    (j n : ℕ) (h : ∀ i, 1 ≤ i → i ≤ n - j → i % 2 = 0 → u i = 0)
    (hn : n % 2 = j % 2) : positiveAdCoeff u x j n = 0 := by
  induction j generalizing n with
  | zero => simp [positiveAdCoeff, show n ≠ 1 by lia]
  | succ j ih =>
    simp only [positiveAdCoeff]
    apply sum_eq_zero
    intro i hi
    have hi' := mem_range.mp hi
    by_cases he : (i + 1) % 2 = 0
    · rw [h (i + 1) (by lia) (by lia) he]
      simp
    · rw [ih (n - (i + 1)) (fun k hk hkn ↦ h k hk (by lia)) (by lia)]
      simp

/-- The last degree-one argument is constant in the auxiliary polynomial variable. -/
theorem degreeLE_positiveAdCoeff (u : ℕ → PolynomialModule ℚ L) (x : L) (j n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n - j → DegreeLE (u i) i) :
    DegreeLE (positiveAdCoeff u x j n) (n - 1) := by
  induction j generalizing n with
  | zero =>
    simp only [positiveAdCoeff]
    split_ifs
    · exact degreeLE_single _ (Nat.zero_le _)
    · exact degreeLE_zero _
  | succ j ih =>
    simp only [positiveAdCoeff]
    apply degreeLE_sum
    intro i hi
    have hi' := mem_range.mp hi
    exact ((h (i + 1) (by lia) (by lia)).lieBracket
      (ih (n - (i + 1)) (fun k hk hkn ↦ h k hk (by lia)))).mono (by lia)

/-- Homomorphisms preserve each homogeneous iterated adjoint coefficient. -/
theorem map_positiveAdCoeff {L' : Type*} [LieRing L'] [LieAlgebra ℚ L']
    (f : L →ₗ⁅ℚ⁆ L') (u : ℕ → PolynomialModule ℚ L) (x : L) (j n : ℕ) :
    PolynomialModule.map ℚ f.toLinearMap (positiveAdCoeff u x j n) =
      positiveAdCoeff (fun i ↦ PolynomialModule.map ℚ f.toLinearMap (u i)) (f x) j n := by
  induction j generalizing n with
  | zero => simp only [positiveAdCoeff]; split_ifs <;> simp
  | succ j ih => simp only [positiveAdCoeff, map_sum, map_lieBracket, ih]

end FQFP
