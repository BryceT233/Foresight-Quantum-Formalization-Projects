/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.BCH.Composition
public import FQFP.Analysis.Normed.Algebra.ExponentialProductTriple
import FQFP.RingTheory.PowerSeries.Noncommutative.ExponentialProduct
import FQFP.RingTheory.PowerSeries.Noncommutative.Palindromic

/-!
# Symmetric BCH and its homogeneous approximations

For `s = ‖a‖ + ‖b‖ < 1/4`, the logarithm of `exp (a/2) * exp b * exp (a/2)` satisfies
`‖bch (bch (a/2) b) (a/2) - (a + b)‖ ≤ 300 s³`.

The logarithm of the palindromic product has zero quadratic coefficient. Its linear
coefficient is the sum of the three arguments, `a + b`. The homogeneous tail estimate
at order three thus bounds the error by `28 s³`.

## Main results

* `symmetricBch_eq_log_exp_mul_exp_mul_exp`: the three-factor logarithm representation.
* `norm_symmetricBch_sub_sum_le`: a finite homogeneous approximation at any truncation order.
* `norm_symmetricBch_sub_le_of_sum_eq`: a remainder bound for an explicit truncation polynomial.
* `norm_symmetric_bch_sub_add_le`: the cubic Strang splitting error bound.

## Provenance and design

The theorem statement comes from `Lean-BCH/BCH/Basic.lean` (`norm_symmetric_bch_sub_add_le`).
Its proof specializes the finite logarithm estimate used for the higher symmetric remainders.

`symmetricBch` names the nested BCH element itself. Its exponential-product identity
provides the logarithm representation used by higher-order symmetric expansions.

The source's `norm_symmetric_bch_sub_add_lie_le` is deliberately not ported: it is this statement
verbatim under a second name.
-/

@[expose] public section

open NormedSpace Finset

namespace FQFP.BCH

noncomputable section

/-- The BCH element of the symmetric three-factor product with two half steps. -/
def symmetricBch {A : Type*} [Ring A] [Algebra ℚ A] [TopologicalSpace A]
    [IsTopologicalRing A] (a b : A) : A :=
  bch (bch ((2 : ℚ)⁻¹ • a) b) ((2 : ℚ)⁻¹ • a)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The symmetric BCH element is the logarithm of its ordered exponential product. -/
theorem symmetricBch_eq_log_exp_mul_exp_mul_exp (a b : 𝔸)
    (hab : ‖(2 : ℚ)⁻¹ • a‖ + ‖b‖ < Real.log 2) :
    symmetricBch a b =
      log (exp ((2 : ℚ)⁻¹ • a) * exp b * exp ((2 : ℚ)⁻¹ • a)) := by
  rw [symmetricBch, bch, exp_bch _ _ hab]

/-- Bound the symmetric BCH element by its finite homogeneous logarithm approximation
at any truncation order, using the total norm of the two full inputs. -/
theorem norm_symmetricBch_sub_sum_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) (n : ℕ) :
    ‖symmetricBch a b - ∑ k ∈ range n, logCoeff k • positivePowerTrunc
      (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (‖a‖ + ‖b‖) ^ n := by
  let h := (2 : ℚ)⁻¹ • a
  let s := ‖a‖ + ‖b‖
  let r := ‖h‖ + ‖b‖ + ‖h‖
  have hr0 : 0 ≤ r := by positivity
  have hr : r ≤ s := by
    dsimp only [r, h, s]
    linarith only [two_mul_norm_half_smul_add_norm_le a b]
  have hinner : ‖h‖ + ‖b‖ < Real.log 2 := by
    have hi : ‖h‖ + ‖b‖ ≤ s := by
      dsimp only [r] at hr
      linarith only [hr, norm_nonneg h]
    exact hi.trans_lt (hab.trans ((by norm_num : (1 : ℝ) / 4 < 1 / 2).trans half_lt_log_two))
  rw [symmetricBch_eq_log_exp_mul_exp_mul_exp a b hinner]
  exact (norm_log_exp_mul_exp_mul_exp_sub_sum_le h b h (hr.trans_lt hab) n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr n) (by positivity))

/-- Transfer the homogeneous logarithm tail estimate to an identified truncation polynomial. -/
theorem norm_symmetricBch_sub_le_of_sum_eq (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4)
    (n : ℕ) {P : 𝔸} {C : ℝ}
    (hP : (∑ k ∈ range n, logCoeff k • positivePowerTrunc
      (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n) = P)
    (hC : (n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1) ≤ C) :
    ‖symmetricBch a b - P‖ ≤ C * (‖a‖ + ‖b‖) ^ n := by
  rw [← hP]
  exact (norm_symmetricBch_sub_sum_le a b hab n).trans
    (mul_le_mul_of_nonneg_right hC (by positivity))

/-- **Symmetric BCH (Strang splitting)**: `bch (bch (a/2) b) (a/2) = a + b + O(s³)`, with an
explicit constant: `‖· - (a + b)‖ ≤ 300 s³` for `s = ‖a‖ + ‖b‖ < 1/4`.

The second-order commutators `½[a/2, b]` and `½[bch (a/2) b, a/2]` cancel, which is exactly what
makes the Strang splitting a second-order integrator. -/
theorem norm_symmetric_bch_sub_add_le (a b : 𝔸) (hab : ‖a‖ + ‖b‖ < 1 / 4) :
    ‖bch (bch ((2 : ℚ)⁻¹ • a) b) ((2 : ℚ)⁻¹ • a) - (a + b)‖ ≤ 300 * (‖a‖ + ‖b‖) ^ 3 := by
  refine norm_symmetricBch_sub_le_of_sum_eq a b hab 3 ?_ (by norm_num)
  let h := (2 : ℚ)⁻¹ • a
  rw [← funext (expListTerm_triple h b h), ← sum_expListLogCoeff,
    sum_expListLogCoeff_three_of_reverse_eq _ (by simp)]
  simp only [List.sum_cons, List.sum_nil, add_zero, h]
  module

end

end FQFP.BCH
