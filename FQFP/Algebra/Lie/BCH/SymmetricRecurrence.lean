/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.HomogeneousConvolution
public import Mathlib.NumberTheory.Bernoulli

/-!
# Homogeneous recursion for symmetric BCH

The auxiliary variable scales the two outer exponentials. The middle exponential
is fixed in this variable. All coefficients are finite Lie polynomials over `ℚ`.

## Main definitions

* `symmetricBchRhs`: the even Bernoulli adjoint terms in a fixed homogeneous degree.
* `symmetricBchHomogeneous`: the triangular recursion with initial value `t y`.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PolynomialModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The degree `n` nonlinear part of the symmetric BCH differential equation. -/
def symmetricBchRhs (u : ℕ → PolynomialModule ℚ L) (x : L) (n : ℕ) :
    PolynomialModule ℚ L :=
  ∑ p ∈ range ((n - 1) / 2),
    (bernoulli (2 * (p + 1)) / (Nat.factorial (2 * (p + 1)) : ℚ)) •
      positiveAdCoeff u x (2 * (p + 1)) n

/-- The nonlinear right-hand side in degree `n` uses only degrees at most `n - 2`. -/
theorem symmetricBchRhs_congr (u v : ℕ → PolynomialModule ℚ L) (x : L) (n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n - 2 → u i = v i) :
    symmetricBchRhs u x n = symmetricBchRhs v x n := by
  unfold symmetricBchRhs
  apply sum_congr rfl
  intro p hp
  congr 1
  apply positiveAdCoeff_congr
  intro i hi hin
  exact h i hi (by lia)

/-- The symmetric BCH homogeneous recursion, polynomial in the auxiliary variable. -/
def symmetricBchHomogeneous (x y : L) : ℕ → PolynomialModule ℚ L :=
  fun k ↦ Nat.strongRecOn k fun n prev ↦
    if n = 0 then 0 else if n = 1 then single ℚ 0 y + single ℚ 1 x else
      integralZero (symmetricBchRhs (fun i ↦ if h : i < n then prev i h else 0) x n)

@[simp]
theorem symmetricBchHomogeneous_zero (x y : L) : symmetricBchHomogeneous x y 0 = 0 := by
  rw [symmetricBchHomogeneous, Nat.strongRecOn_eq]
  simp

@[simp]
theorem symmetricBchHomogeneous_one (x y : L) :
    symmetricBchHomogeneous x y 1 = single ℚ 0 y + single ℚ 1 x := by
  rw [symmetricBchHomogeneous, Nat.strongRecOn_eq]
  simp

/-- The recursion equation holds in every nonlinear homogeneous degree. -/
theorem symmetricBchHomogeneous_eq_integral (x y : L) (n : ℕ) (hn : 2 ≤ n) :
    symmetricBchHomogeneous x y n =
      integralZero (symmetricBchRhs (symmetricBchHomogeneous x y) x n) := by
  conv_lhs => rw [symmetricBchHomogeneous, Nat.strongRecOn_eq]
  simp only [show n ≠ 0 by lia, show n ≠ 1 by lia, ↓reduceIte]
  apply congrArg integralZero
  apply symmetricBchRhs_congr
  intro i hi hin
  simp only [show i < n by lia, ↓reduceDIte]
  rfl

/-- Evaluation of the homogeneous recursion at auxiliary time one. -/
def symmetricBchLieCoeff (x y : L) (n : ℕ) : L :=
  eval 1 (symmetricBchHomogeneous x y n)

/-- The nonlinear coefficients have zero initial value in the auxiliary variable. -/
theorem coeff_symmetricBchHomogeneous_zero (x y : L) (n : ℕ) (hn : 2 ≤ n) :
    (symmetricBchHomogeneous x y n).coeff 0 = 0 := by
  rw [symmetricBchHomogeneous_eq_integral x y n hn, coeff_integralZero_zero]

/-- The homogeneous coefficients satisfy the differential recurrence in every degree. -/
theorem derivative_symmetricBchHomogeneous (x y : L) (n : ℕ) (hn : 2 ≤ n) :
    derivative (symmetricBchHomogeneous x y n) =
      symmetricBchRhs (symmetricBchHomogeneous x y) x n := by
  rw [symmetricBchHomogeneous_eq_integral x y n hn, derivative_integralZero]

/-- Initial values and the triangular differential equation determine all coefficients. -/
theorem symmetricBchHomogeneous_unique (x y : L) (u : ℕ → PolynomialModule ℚ L)
    (hzero : u 0 = 0) (hone : u 1 = single ℚ 0 y + single ℚ 1 x)
    (hinit : ∀ n, 2 ≤ n → (u n).coeff 0 = 0)
    (hderiv : ∀ n, 2 ≤ n → derivative (u n) = symmetricBchRhs u x n) :
    u = symmetricBchHomogeneous x y := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simpa using hzero
    by_cases hn1 : n = 1
    · subst n
      simpa using hone
    have hn : 2 ≤ n := by lia
    apply ext_derivative
    · rw [hderiv n hn, derivative_symmetricBchHomogeneous x y n hn]
      apply symmetricBchRhs_congr
      intro i hi hin
      exact ih i (by lia)
    · rw [hinit n hn, coeff_symmetricBchHomogeneous_zero x y n hn]

/-- Every even homogeneous coefficient vanishes, by parity of the adjoint recursion. -/
theorem symmetricBchHomogeneous_eq_zero_of_even (x y : L) (n : ℕ) (he : Even n) :
    symmetricBchHomogeneous x y n = 0 := by
  have he' : n % 2 = 0 := Nat.even_iff.mp he
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    have hn : 2 ≤ n := by lia
    rw [symmetricBchHomogeneous_eq_integral x y n hn]
    suffices symmetricBchRhs (symmetricBchHomogeneous x y) x n = 0 by
      rw [this, map_zero]
    unfold symmetricBchRhs
    apply sum_eq_zero
    intro p hp
    rw [positiveAdCoeff_eq_zero_of_parity]
    · simp
    · intro i hi hin hie
      exact ih i (by lia) (Nat.even_iff.mpr hie) hie
    · lia

/-- The auxiliary polynomial degree never exceeds the total homogeneous degree. -/
theorem degreeLE_symmetricBchHomogeneous (x y : L) (n : ℕ) :
    DegreeLE (symmetricBchHomogeneous x y n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [symmetricBchHomogeneous_zero]
      exact degreeLE_zero _
    by_cases hn1 : n = 1
    · subst n
      rw [symmetricBchHomogeneous_one]
      exact (degreeLE_single _ (by lia)).add (degreeLE_single _ (by lia))
    have hn : 2 ≤ n := by lia
    rw [symmetricBchHomogeneous_eq_integral x y n hn]
    have hr : DegreeLE (symmetricBchRhs (symmetricBchHomogeneous x y) x n) (n - 1) := by
      apply degreeLE_sum
      intro p hp
      apply DegreeLE.smul
      apply degreeLE_positiveAdCoeff
      intro i hi hin
      exact ih i (by lia)
    exact hr.integralZero.mono (by lia)

/-- Lie algebra homomorphisms preserve the entire homogeneous recursion. -/
theorem map_symmetricBchHomogeneous {L' : Type*} [LieRing L'] [LieAlgebra ℚ L']
    (f : L →ₗ⁅ℚ⁆ L') (x y : L) (n : ℕ) :
    PolynomialModule.map ℚ f.toLinearMap (symmetricBchHomogeneous x y n) =
      symmetricBchHomogeneous (f x) (f y) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    have hn : 2 ≤ n := by lia
    rw [symmetricBchHomogeneous_eq_integral x y n hn,
      symmetricBchHomogeneous_eq_integral (f x) (f y) n hn, map_integralZero]
    apply congrArg integralZero
    calc
      PolynomialModule.map ℚ f.toLinearMap (symmetricBchRhs (symmetricBchHomogeneous x y) x n) =
          symmetricBchRhs
            (fun i ↦ PolynomialModule.map ℚ f.toLinearMap (symmetricBchHomogeneous x y i))
            (f x) n := by
              simp only [symmetricBchRhs, map_sum, LinearMap.map_smul, map_positiveAdCoeff]
      _ = _ := symmetricBchRhs_congr _ _ _ _ (fun i hi hin ↦ ih i (by lia))

/-- Evaluation at one is natural for Lie algebra homomorphisms. -/
theorem map_symmetricBchLieCoeff {L' : Type*} [LieRing L'] [LieAlgebra ℚ L']
    (f : L →ₗ⁅ℚ⁆ L') (x y : L) (n : ℕ) :
    f (symmetricBchLieCoeff x y n) = symmetricBchLieCoeff (f x) (f y) n := by
  rw [symmetricBchLieCoeff, symmetricBchLieCoeff, ← map_symmetricBchHomogeneous f x y n]
  simpa using (eval_map ℚ f.toLinearMap (symmetricBchHomogeneous x y n) (1 : ℚ)).symm

end FQFP
