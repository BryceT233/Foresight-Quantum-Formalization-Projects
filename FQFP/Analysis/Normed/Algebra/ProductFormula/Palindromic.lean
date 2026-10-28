/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ExponentialList
public import FQFP.Analysis.Normed.Algebra.Logarithm
public import FQFP.Analysis.Normed.Algebra.BCH.Symmetric
public import Mathlib.Analysis.RCLike.Basic

/-!
# Palindromic Suzuki products

The eleven exponential arguments of the five-block Suzuki composition form a
palindrome. Reflection of the time parameter therefore inverts the product.
Its logarithm exponentiates back to the product on the source convergence domain,
and is odd when both logarithms lie in the local injectivity ball.

## Main definitions

* `suzuki5Arguments`: the ordered eleven exponent arguments.
* `suzuki5Product`: their ordered exponential product, with arbitrary parameter `p`.
* `suzuki5ArgNormBound`: the source coefficient bound for the argument norms.
* `suzuki5Bch`: the logarithm of the product.
* `strangBlock`: a single symmetric three-factor step.

## Main results

* `suzuki5Product_mul_neg_eq_one`: reflection gives an inverse.
* `exp_suzuki5Bch`: the local exponential/logarithm round trip.
* `suzuki5Bch_neg`: local oddness of the logarithm.
* `suzuki5Product_eq_strangBlock_prod`: the five-block factorization.
* `log_strangBlock_eq_symmetricBch`: the local symmetric BCH representation of a Strang block.
* `suzuki5Bch_neg_of_lt_quarter`: oddness from the coefficient bound alone.
-/

@[expose] public noncomputable section

open NormedSpace

namespace FQFP.BCH

section Definitions

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The eleven ordered arguments of the five-block Suzuki composition. -/
def suzuki5Arguments (a b : A) (p t : K) : List A :=
  [(p / 2 * t) • a, (p * t) • b, (p * t) • a, (p * t) • b,
    ((1 - 3 * p) / 2 * t) • a, ((1 - 4 * p) * t) • b,
    ((1 - 3 * p) / 2 * t) • a, (p * t) • b, (p * t) • a,
    (p * t) • b, (p / 2 * t) • a]

/-- The argument list is unchanged by reversal. -/
lemma suzuki5Arguments_reverse (a b : A) (p t : K) :
    (suzuki5Arguments a b p t).reverse = suzuki5Arguments a b p t := rfl

/-- Time reflection negates each exponent argument. -/
lemma suzuki5Arguments_neg (a b : A) (p t : K) :
    suzuki5Arguments a b p (-t) = (suzuki5Arguments a b p t).map Neg.neg := by
  simp [suzuki5Arguments, mul_neg, neg_smul]

variable [TopologicalSpace A] [IsTopologicalRing A]

/-- The ordered eleven-factor Suzuki product, with unrestricted coefficient `p`. -/
def suzuki5Product (a b : A) (p t : K) : A :=
  ((suzuki5Arguments a b p t).map exp).prod

/-- The logarithm of the five-block Suzuki product. -/
def suzuki5Bch (a b : A) (p t : K) : A := log (suzuki5Product a b p t)

/-- A symmetric three-factor Strang step with coefficient `c`. -/
def strangBlock (a b : A) (c t : K) : A :=
  exp ((c * t / 2) • a) * exp ((c * t) • b) * exp ((c * t / 2) • a)

/-- The argument-list definition agrees with the explicit eleven-factor source product. -/
lemma suzuki5Product_eq (a b : A) (p t : K) :
    suzuki5Product a b p t =
      exp ((p / 2 * t) • a) * exp ((p * t) • b) *
      exp ((p * t) • a) * exp ((p * t) • b) *
      exp (((1 - 3 * p) / 2 * t) • a) * exp (((1 - 4 * p) * t) • b) *
      exp (((1 - 3 * p) / 2 * t) • a) * exp ((p * t) • b) *
      exp ((p * t) • a) * exp ((p * t) • b) * exp ((p / 2 * t) • a) := by
  simp [suzuki5Product, suzuki5Arguments, mul_assoc]

/-- At time zero, the product is one. -/
@[simp]
lemma suzuki5Product_zero (a b : A) (p : K) : suzuki5Product a b p 0 = 1 := by
  simp [suzuki5Product, suzuki5Arguments]

/-- At time zero, the logarithm is zero. -/
@[simp]
lemma suzuki5Bch_zero (a b : A) (p : K) : suzuki5Bch a b p 0 = 0 := by
  simp [suzuki5Bch]

end Definitions

section NormBounds

variable {K A : Type*} [RCLike K] [NormedRing A]

/-- The source bound on the total norm of the eleven exponent arguments. -/
def suzuki5ArgNormBound (a b : A) (p t : K) : ℝ :=
  ‖t‖ * ((3 * ‖p‖ + ‖1 - 3 * p‖) * ‖a‖ + (4 * ‖p‖ + ‖1 - 4 * p‖) * ‖b‖)

/-- The argument-norm bound is nonnegative. -/
lemma suzuki5ArgNormBound_nonneg (a b : A) (p t : K) :
    0 ≤ suzuki5ArgNormBound a b p t := by
  unfold suzuki5ArgNormBound
  positivity

/-- The coefficient bound is unchanged by time reflection. -/
@[simp]
lemma suzuki5ArgNormBound_neg (a b : A) (p t : K) :
    suzuki5ArgNormBound a b p (-t) = suzuki5ArgNormBound a b p t := by
  simp [suzuki5ArgNormBound]

variable [NormedAlgebra K A]

/-- The argument norms sum to the source coefficient bound. -/
lemma sum_norm_suzuki5Arguments (a b : A) (p t : K) :
    ((suzuki5Arguments a b p t).map norm).sum = suzuki5ArgNormBound a b p t := by
  simp [suzuki5Arguments, suzuki5ArgNormBound, norm_smul, norm_mul, norm_div]
  ring

variable [CompleteSpace A]

private lemma exp_smul_mul_exp_smul_mul (a z : A) (x y : K) :
    exp (x • a) * (exp (y • a) * z) = exp ((x + y) • a) * z := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  rw [← mul_assoc, ← exp_add_of_commute (((Commute.refl a).smul_left x).smul_right y),
    ← add_smul]

/-- Five Strang blocks merge to the eleven-factor Suzuki product. -/
theorem suzuki5Product_eq_strangBlock_prod (a b : A) (p t : K) :
    suzuki5Product a b p t =
      strangBlock a b p t * strangBlock a b p t * strangBlock a b (1 - 4 * p) t *
      strangBlock a b p t * strangBlock a b p t := by
  have hpp : p * t / 2 + p * t / 2 = p * t := by ring
  have hpq : p * t / 2 + (1 - 4 * p) * t / 2 = (1 - 3 * p) / 2 * t := by ring
  have hqp : (1 - 4 * p) * t / 2 + p * t / 2 = (1 - 3 * p) / 2 * t := by ring
  simp only [suzuki5Product_eq, strangBlock, mul_assoc]
  rw [exp_smul_mul_exp_smul_mul a, hpp, exp_smul_mul_exp_smul_mul a, hpq,
    exp_smul_mul_exp_smul_mul a, hqp, exp_smul_mul_exp_smul_mul a, hpp]
  rw [div_mul_eq_mul_div]

/-- The product at reflected time is a right inverse, without smallness assumptions. -/
theorem suzuki5Product_mul_neg_eq_one (a b : A) (p t : K) :
    suzuki5Product a b p t * suzuki5Product a b p (-t) = 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  simpa only [suzuki5Product, suzuki5Arguments_neg, List.map_map,
    suzuki5Arguments_reverse, Function.comp_def] using
    prod_exp_mul_reverse_neg_eq_one (suzuki5Arguments a b p t)

/-- The product at reflected time is also a left inverse. -/
theorem suzuki5Product_neg_mul_eq_one (a b : A) (p t : K) :
    suzuki5Product a b p (-t) * suzuki5Product a b p t = 1 := by
  simpa only [neg_neg] using suzuki5Product_mul_neg_eq_one a b p (-t)

variable [NormOneClass A]

/-- A small Strang block has the same logarithm as the nested symmetric BCH element. -/
theorem log_strangBlock_eq_symmetricBch (a b : A) (c t : K)
    (h : ‖((2 : K)⁻¹ * (c * t)) • a‖ + ‖(c * t) • b‖ < Real.log 2) :
    letI : NormedAlgebra ℚ A := .restrictScalars ℚ K A
    log (strangBlock a b c t) = symmetricBch ((c * t) • a) ((c * t) • b) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hhalf : (2 : ℚ)⁻¹ • ((c * t) • a) = (c * t / 2) • a := by
    change (algebraMap ℚ K (2 : ℚ)⁻¹) • ((c * t) • a) = _
    norm_num
    rw [smul_smul]
    congr 1
    ring
  rw [symmetricBch_eq_log_exp_mul_exp_mul_exp]
  · rw [hhalf, strangBlock]
  · simpa only [hhalf, inv_mul_eq_div] using h

/-- The scalar majorant for the distance of the Suzuki product from one. -/
theorem norm_suzuki5Product_sub_one_le (a b : A) (p t : K) :
    ‖suzuki5Product a b p t - 1‖ ≤ Real.exp (suzuki5ArgNormBound a b p t) - 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  simpa only [suzuki5Product, sum_norm_suzuki5Arguments] using
    norm_prod_exp_sub_one_le (suzuki5Arguments a b p t)

/-- The source coefficient regime puts the Suzuki product inside the logarithm ball. -/
theorem norm_suzuki5Product_sub_one_lt_one (a b : A) (p t : K)
    (h : suzuki5ArgNormBound a b p t < Real.log 2) :
    ‖suzuki5Product a b p t - 1‖ < 1 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  exact norm_prod_exp_sub_one_lt_one _ (by rwa [sum_norm_suzuki5Arguments])

/-- The exponential of the Suzuki logarithm equals the product on the source domain. -/
theorem exp_suzuki5Bch (a b : A) (p t : K)
    (h : suzuki5ArgNormBound a b p t < Real.log 2) :
    exp (suzuki5Bch a b p t) = suzuki5Product a b p t := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  exact exp_log (norm_suzuki5Product_sub_one_lt_one a b p t h)

/-- The Suzuki logarithm is odd on the source local injectivity domain. -/
theorem suzuki5Bch_neg (a b : A) (p t : K)
    (h : suzuki5ArgNormBound a b p t < Real.log 2)
    (ht : ‖suzuki5Bch a b p t‖ < Real.log 2)
    (hnt : ‖suzuki5Bch a b p (-t)‖ < Real.log 2) :
    suzuki5Bch a b p (-t) = -suzuki5Bch a b p t := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hprod : exp (suzuki5Bch a b p t) * exp (suzuki5Bch a b p (-t)) = 1 := by
    rw [exp_suzuki5Bch a b p t h, exp_suzuki5Bch a b p (-t) (by simpa using h)]
    exact suzuki5Product_mul_neg_eq_one a b p t
  have heq : exp (suzuki5Bch a b p (-t)) = exp (-suzuki5Bch a b p t) := by
    calc
      _ = (exp (-suzuki5Bch a b p t) * exp (suzuki5Bch a b p t)) *
          exp (suzuki5Bch a b p (-t)) := by
        rw [TrotterError.exp_neg_mul_self, one_mul]
      _ = _ := by rw [mul_assoc, hprod, mul_one]
  calc
    _ = log (exp (suzuki5Bch a b p (-t))) := (log_exp_of_norm_lt _ hnt).symm
    _ = log (exp (-suzuki5Bch a b p t)) := congrArg log heq
    _ = _ := log_exp_of_norm_lt _ (by simpa only [norm_neg] using ht)

/-- A quarter-radius coefficient bound also puts the logarithm in its injectivity ball. -/
theorem norm_suzuki5Bch_lt_log_two (a b : A) (p t : K)
    (h : suzuki5ArgNormBound a b p t < 1 / 4) :
    ‖suzuki5Bch a b p t‖ < Real.log 2 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ K A
  have hd := eleven_sixteenths_le_two_sub_exp (suzuki5ArgNormBound_nonneg a b p t) h le_rfl
  have hb := norm_suzuki5Product_sub_one_le a b p t
  have hn : ‖suzuki5Product a b p t - 1‖ ≤ 5 / 16 := by linarith only [hd, hb]
  have hl := norm_log_one_add_le (suzuki5Product a b p t - 1)
    (by linarith only [hn] : ‖suzuki5Product a b p t - 1‖ < 1)
  rw [← add_sub_assoc, add_sub_cancel_left] at hl
  apply lt_of_le_of_lt (hl.trans ?_) half_lt_log_two
  apply (div_le_iff₀ (by linarith only [hn])).mpr
  linarith only [hn]

/-- On the quarter-radius coefficient domain the Suzuki logarithm is odd. -/
theorem suzuki5Bch_neg_of_lt_quarter (a b : A) (p t : K)
    (h : suzuki5ArgNormBound a b p t < 1 / 4) :
    suzuki5Bch a b p (-t) = -suzuki5Bch a b p t :=
  suzuki5Bch_neg a b p t (h.trans (by linarith only [half_lt_log_two]))
    (norm_suzuki5Bch_lt_log_two a b p t h)
    (norm_suzuki5Bch_lt_log_two a b p (-t) (by simpa only [suzuki5ArgNormBound_neg] using h))

end NormBounds

end FQFP.BCH
