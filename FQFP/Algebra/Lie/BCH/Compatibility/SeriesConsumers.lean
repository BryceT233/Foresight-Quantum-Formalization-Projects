/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Compatibility.SymmetricRecurrence
public import FQFP.Algebra.Lie.BCH.SymmetricCoefficients
public import FQFP.RingTheory.PowerSeries.Noncommutative.ExponentialProduct

/-!
# Finite logarithm consumers of the homogeneous recursion

The ordered-list and triple-product conventions agree by associativity of
Cauchy multiplication. Finite logarithms therefore use the homogeneous Lie
coefficients without importing any finite word certificate.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Any finite symmetric logarithm is the sum of the recursive homogeneous Lie coefficients. -/
theorem sum_logCoeff_positivePowerTrunc_eq_sum_symmetricBchLieCoeff (a b : A) (m : ℕ) :
    (∑ k ∈ range m, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k m) =
      ∑ n ∈ range m, symmetricBchLieCoeff a b n := by
  rw [← funext (expListTerm_triple ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)),
    ← sum_expListLogCoeff]
  apply sum_congr rfl
  intro n hn
  exact (symmetricBchLieCoeff_eq_expListLogCoeff a b n).symm

/-- The finite symmetric logarithm through degree six, derived from the all-degree recursion. -/
theorem sum_logCoeff_positivePowerTrunc_eq_symmetricLie_quintic (a b : A) :
    (∑ k ∈ range 7, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k 7) =
      (a + b) + symmetricBchCubicLieTerm a b + symmetricBchQuinticLieTerm a b := by
  rw [sum_logCoeff_positivePowerTrunc_eq_sum_symmetricBchLieCoeff]
  simp only [sum_range_succ, sum_range_zero, symmetricBchLieCoeff_zero,
    symmetricBchLieCoeff_one, symmetricBchLieCoeff_three, symmetricBchLieCoeff_five,
    symmetricBchLieCoeff_eq_zero_of_even a b 2 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even a b 4 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even a b 6 (by decide), add_zero, zero_add]

/-- The finite logarithm through degree eight retains the unnormalized recursive seventh term. -/
theorem sum_logCoeff_positivePowerTrunc_eq_symmetricLie_septic (a b : A) :
    (∑ k ∈ range 9, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k 9) =
      (a + b) + symmetricBchCubicLieTerm a b + symmetricBchQuinticLieTerm a b +
        symmetricBchLieCoeff a b 7 := by
  rw [sum_logCoeff_positivePowerTrunc_eq_sum_symmetricBchLieCoeff]
  simp only [sum_range_succ, sum_range_zero, symmetricBchLieCoeff_zero,
    symmetricBchLieCoeff_one, symmetricBchLieCoeff_three, symmetricBchLieCoeff_five,
    symmetricBchLieCoeff_eq_zero_of_even a b 2 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even a b 4 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even a b 6 (by decide),
    symmetricBchLieCoeff_eq_zero_of_even a b 8 (by decide), add_zero, zero_add]

end FQFP
