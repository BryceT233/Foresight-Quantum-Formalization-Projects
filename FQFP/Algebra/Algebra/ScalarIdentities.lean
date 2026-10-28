/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Central real scalar identities

Real algebra scalars commute with coefficients and powers.

## Main results

* `TrotterError.smul_eq_mul_right`.
* `TrotterError.pow_smul_eq_smul_mul`.
* `TrotterError.smul_mul_cast`.
-/

@[expose] public section

namespace TrotterError

open scoped BigOperators

open scoped algebraMap

/-- In an ℝ-algebra, the scalar action `r • a` equals right multiplication `a * (r : 𝔸)`. -/
lemma smul_eq_mul_right {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r : ℝ) (a : 𝔸) :
    r • a = a * (r : 𝔸) := by
  rw [Algebra.smul_def, Algebra.commutes]

/-- The Taylor coefficient `(j! : ℝ)⁻¹ * τ^j` acting by `•` equals the paper's form
`(j! : ℝ)⁻¹ • x * (τ : 𝔸)^j`. -/
lemma pow_smul_eq_smul_mul {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (j : ℕ) (x : 𝔸) (τ : ℝ) :
    ((Nat.factorial j : ℝ)⁻¹ * τ ^ j) • x = (Nat.factorial j : ℝ)⁻¹ • x * (τ : 𝔸) ^ j := by
  rw [mul_smul, smul_eq_mul_right (τ ^ j) x]
  simp

/-- `(r • a) * (c : 𝔸) = (r * c) • a` for scalars `r, c : ℝ`. -/
lemma smul_mul_cast {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (r c : ℝ) (a : 𝔸) :
    (r • a) * (c : 𝔸) = (r * c) • a := by
  rw [smul_eq_mul_right r a, smul_eq_mul_right (r * c) a, mul_assoc, ← map_mul (algebraMap ℝ 𝔸) r c]

end TrotterError
