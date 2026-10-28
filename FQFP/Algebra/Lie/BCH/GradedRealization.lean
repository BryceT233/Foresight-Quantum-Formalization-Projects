/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.HomogeneousConvolution
public import FQFP.Algebra.Lie.BCH.SymmetricRecurrence
public import FQFP.Algebra.Lie.BCH.SymmetricProduct

/-!
# Formal series semantics of homogeneous Lie convolution

The positive adjoint convolution is the coefficient of an actual iterated
adjoint in the formal series algebra. The range pruning follows from its
minimum homogeneous degree, without expanding associative words.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PolynomialModule PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Realize a positive family of finite Lie polynomials as an associative formal series. -/
def homogeneousLieSeries (u : ℕ → PolynomialModule ℚ A) : PowerSeries (Polynomial A) :=
  positiveSeries fun n ↦ toPolynomial (u n)

@[simp]
theorem constantCoeff_homogeneousLieSeries (u : ℕ → PolynomialModule ℚ A) :
    constantCoeff (homogeneousLieSeries u) = 0 := by
  simp [homogeneousLieSeries, positiveSeries]

omit [Algebra ℚ A] in
theorem linearSeries_eq_monomial (a : A) :
    linearSeries a = PowerSeries.monomial 1 (Polynomial.C a) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [linearSeries, PowerSeries.coeff_monomial]
  | succ n => simp [linearSeries, PowerSeries.coeff_monomial, PowerSeries.coeff_X]

private theorem ad_apply_poly (p q : Polynomial A) :
    LieAlgebra.ad ℚ (Polynomial A) p q = ⁅p, q⁆ := rfl

/-- Positive adjoint convolution is the actual total-degree coefficient of an iterated adjoint. -/
theorem toPolynomial_positiveAdCoeff (u : ℕ → PolynomialModule ℚ A) (a : A) (j n : ℕ) :
    toPolynomial (positiveAdCoeff u a j n) =
      PowerSeries.coeff n
        ((LieAlgebra.ad ℚ (PowerSeries (Polynomial A)) (homogeneousLieSeries u) ^ j)
          (linearSeries a)) := by
  induction j generalizing n with
  | zero =>
    rw [pow_zero, Module.End.one_apply, linearSeries_eq_monomial]
    simp only [positiveAdCoeff, PowerSeries.coeff_monomial]
    split_ifs <;> simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ← seriesLinearAction_adjointSeries,
      coeff_seriesLinearAction, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ']
    simp only [coeff_adjointSeries, homogeneousLieSeries, coeff_positiveSeries_zero,
      map_zero, LinearMap.zero_apply, add_zero, coeff_positiveSeries_succ]
    simp only [positiveAdCoeff, map_sum, toPolynomial_lieBracket, ih]
    simp only [homogeneousLieSeries, ad_apply_poly]
    apply sum_subset (range_mono (Nat.sub_le n (j + 1)))
    intro i hi hin
    have hi' := mem_range.mp hi
    have hin' := mem_range.not.mp hin
    rw [coeff_ad_pow_eq_zero_of_le (positiveSeries fun k ↦ toPolynomial (u k)) (linearSeries a)
      (by simp [positiveSeries])
      (by
        rw [linearSeries_eq_monomial, ← coeff_zero_eq_constantCoeff_apply]
        simp [PowerSeries.coeff_monomial]) j (n - (i + 1)) (by lia), lie_zero]

private theorem coeff_symmetricBernoulli (j : ℕ) :
    PowerSeries.coeff j (bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • PowerSeries.X) =
      if j = 0 then 1 else if j % 2 = 0 then bernoulli j / (j.factorial : ℚ) else 0 := by
  rw [← bernoulliPowerSeries_mul_half_exp_add_one]
  exact coeff_bernoulliPowerSeries_mul_half_exp_add_one j

/-- Extracting the even Bernoulli adjoint equation gives the finite homogeneous right-hand side. -/
theorem coeff_adjointSeriesApply_eq_symmetricBchRhs (u : ℕ → PolynomialModule ℚ A)
    (a : A) (n : ℕ) (hn : 2 ≤ n) :
    PowerSeries.coeff n (adjointSeriesApply
      (bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • PowerSeries.X)
      (homogeneousLieSeries u) (linearSeries a)) = toPolynomial (symmetricBchRhs u a n) := by
  let g := fun j ↦ PowerSeries.coeff j
      (bernoulliPowerSeries ℚ + (2 : ℚ)⁻¹ • PowerSeries.X) •
    PowerSeries.coeff n
      ((LieAlgebra.ad ℚ (PowerSeries (Polynomial A)) (homogeneousLieSeries u) ^ j)
        (linearSeries a))
  let s := (range (n + 1)).filter fun j ↦ 2 ≤ j ∧ j % 2 = 0 ∧ j < n
  have hs : ∑ j ∈ s, g j = ∑ j ∈ range (n + 1), g j := by
    apply sum_subset (filter_subset _ _)
    intro j hj hjout
    have hj' := mem_range.mp hj
    by_cases hj0 : j = 0
    · subst j
      simp [g, linearSeries_eq_monomial, PowerSeries.coeff_monomial, show n ≠ 1 by lia]
    by_cases he : j % 2 = 0
    · have hnj : n ≤ j := by
        have hout : ¬(2 ≤ j ∧ j % 2 = 0 ∧ j < n) := by
          intro h
          exact hjout (mem_filter.mpr ⟨hj, h⟩)
        lia
      simp only [g, coeff_ad_pow_eq_zero_of_le (homogeneousLieSeries u) (linearSeries a)
        (constantCoeff_homogeneousLieSeries u)
        (by
          rw [linearSeries_eq_monomial, ← coeff_zero_eq_constantCoeff_apply]
          simp [PowerSeries.coeff_monomial]) j n hnj, smul_zero]
    · simp [g, coeff_symmetricBernoulli, hj0, he]
  rw [coeff_adjointSeriesApply _ _ _ (constantCoeff_homogeneousLieSeries u), ← hs]
  simp only [symmetricBchRhs, map_sum, LinearMap.map_smul, toPolynomial_positiveAdCoeff]
  symm
  apply sum_nbij' (fun p ↦ 2 * (p + 1)) (fun j ↦ j / 2 - 1)
  · intro p hp
    have hp' := mem_range.mp hp
    change 2 * (p + 1) ∈ (range (n + 1)).filter _
    simp only [mem_filter, mem_range]
    exact ⟨by lia, by lia, by lia, by lia⟩
  · intro j hj
    obtain ⟨hjrange, hj2, he, hjn⟩ := mem_filter.mp hj
    exact mem_range.mpr (by have := mem_range.mp hjrange; lia)
  · intro p hp
    have hp' := mem_range.mp hp
    lia
  · intro j hj
    obtain ⟨hjrange, hj2, he, hjn⟩ := mem_filter.mp hj
    lia
  · intro p hp
    simp [g, coeff_symmetricBernoulli, show 2 * (p + 1) ≠ 0 by lia,
      show (2 * (p + 1)) % 2 = 0 by lia]

end FQFP
