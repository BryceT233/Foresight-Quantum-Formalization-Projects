/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Series
public import FQFP.BCH.DynkinReeSeptic
public import FQFP.BCH.DynkinReeOctic

/-!
# Finite BCH truncations

Specializations of the homogeneous exponential product and its logarithm.

## Main results

* `expMulTerm_two` through `expMulTerm_eight`: homogeneous term specializations.
* `sum_range_expMulTerm_three` through `sum_range_expMulTerm_nine`: finite truncations.
* `bch_quintic_truncation_eq`: the logarithm through total degree five.
* `bch_sextic_truncation_eq`: the logarithm through total degree six.
* `bch_septic_truncation_eq`: the logarithm through total degree seven.
* `bch_octic_truncation_eq`: the logarithm through total degree eight.
-/

@[expose] public noncomputable section
open Finset Finset.Nat
namespace FQFP.BCH

section ExponentialTerms

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The degree-2 specialization of the homogeneous exponential product. -/
lemma expMulTerm_two (a b : A) : expMulTerm a b 2 = bchT2 a b :=
  FQFP.expMulTerm_two a b

/-- The degree-3 specialization of the homogeneous exponential product. -/
lemma expMulTerm_three (a b : A) : expMulTerm a b 3 = bchT3 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ,
    Nat.factorial, smul_mul_smul_comm, bchT3]
  module

/-- The degree-4 specialization of the homogeneous exponential product. -/
lemma expMulTerm_four (a b : A) : expMulTerm a b 4 = bchT4 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ,
    Nat.factorial, smul_mul_smul_comm, bchT4]
  module

/-- The degree-5 specialization of the homogeneous exponential product. -/
lemma expMulTerm_five (a b : A) : expMulTerm a b 5 = bchT5 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ,
    Nat.factorial, smul_mul_smul_comm, bchT5]
  module

/-- The degree-6 specialization of the homogeneous exponential product. -/
lemma expMulTerm_six (a b : A) : expMulTerm a b 6 = bchT6 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm, bchT6]
  module

/-- The degree-7 specialization of the homogeneous exponential product. -/
lemma expMulTerm_seven (a b : A) : expMulTerm a b 7 = bchT7 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm, bchT7]
  module

/-- The degree-8 specialization of the homogeneous exponential product. -/
lemma expMulTerm_eight (a b : A) : expMulTerm a b 8 = bchT8 a b := by
  rw [expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, Nat.factorial, smul_mul_smul_comm, bchT8]
  module

/-- The exponential product truncated after its quadratic term. -/
lemma sum_range_expMulTerm_three (a b : A) :
    ∑ i ∈ range 3, expMulTerm a b i = 1 + bchZ a b + bchT2 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_two, expMulTerm_two, bchZ]

/-- The exponential product truncated after its cubic term. -/
lemma sum_range_expMulTerm_four (a b : A) :
    ∑ i ∈ range 4, expMulTerm a b i = 1 + bchZ a b + bchT2 a b + bchT3 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_three, expMulTerm_three]

/-- The exponential product truncated after its quartic term. -/
lemma sum_range_expMulTerm_five (a b : A) :
    ∑ i ∈ range 5, expMulTerm a b i =
      1 + bchZ a b + bchT2 a b + bchT3 a b + bchT4 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_four, expMulTerm_four]

/-- The exponential product truncated after its quintic term. -/
lemma sum_range_expMulTerm_six (a b : A) :
    ∑ i ∈ range 6, expMulTerm a b i =
      1 + bchZ a b + bchT2 a b + bchT3 a b + bchT4 a b + bchT5 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_five, expMulTerm_five]

/-- The exponential product truncated after its sextic term. -/
lemma sum_range_expMulTerm_seven (a b : A) :
    ∑ i ∈ range 7, expMulTerm a b i =
      1 + bchZ a b + bchT2 a b + bchT3 a b + bchT4 a b + bchT5 a b + bchT6 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_six, expMulTerm_six]

/-- The exponential product truncated after its septic term. -/
lemma sum_range_expMulTerm_eight (a b : A) :
    ∑ i ∈ range 8, expMulTerm a b i = 1 + bchZ a b + bchT2 a b + bchT3 a b +
      bchT4 a b + bchT5 a b + bchT6 a b + bchT7 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_seven, expMulTerm_seven]

/-- The exponential product truncated after its octic term. -/
lemma sum_range_expMulTerm_nine (a b : A) :
    ∑ i ∈ range 9, expMulTerm a b i = 1 + bchZ a b + bchT2 a b + bchT3 a b +
      bchT4 a b + bchT5 a b + bchT6 a b + bchT7 a b + bchT8 a b := by
  rw [sum_range_succ, sum_range_expMulTerm_eight, expMulTerm_eight]

end ExponentialTerms

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The logarithm of the exponential product, through total degree five. -/
theorem bch_quintic_truncation_eq (a b : A) :
    (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b +
      bchQuarticTerm a b + bchQuinticTerm a b =
    (bchZ a b + bchT2 a b + bchT3 a b + bchT4 a b + bchT5 a b) -
      (2 : ℚ)⁻¹ • (bchZ a b ^ 2 +
        (bchZ a b * bchT2 a b + bchT2 a b * bchZ a b) +
        (bchZ a b * bchT3 a b + bchT2 a b ^ 2 + bchT3 a b * bchZ a b) +
        (bchZ a b * bchT4 a b + bchT2 a b * bchT3 a b +
          bchT3 a b * bchT2 a b + bchT4 a b * bchZ a b)) +
      (3 : ℚ)⁻¹ • (bchZ a b ^ 3 +
        (bchZ a b ^ 2 * bchT2 a b + bchZ a b * bchT2 a b * bchZ a b +
          bchT2 a b * bchZ a b ^ 2) + bchY35 a b) -
      (4 : ℚ)⁻¹ • (bchZ a b ^ 4 + bchY45 a b) + (5 : ℚ)⁻¹ • bchZ a b ^ 5 := by
  rw [← sub_eq_zero.mp (sextic_pure_identity a b), ← sub_eq_zero.mp (quintic_pure_identity a b)]
  unfold bchW5 bchZ bchT2 bchT3 bchT4 bchT5 bchCubicTerm
  simp only [pow_succ, pow_zero, one_mul, mul_add, add_mul, mul_sub, sub_mul,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_add, smul_sub, smul_smul,
    ← mul_assoc]
  module

/-- The BCH truncation through degree six is the finite logarithm of homogeneous powers. -/
theorem bch_sextic_truncation_eq (a b : A) :
    (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b +
      bchQuarticTerm a b + bchQuinticTerm a b + bchSexticTerm a b =
      ∑ k ∈ range 7, logCoeff k • positivePowerTrunc (expMulTerm a b) k 7 := by
  rw [← sub_eq_zero.mp (septic_pure_identity a b), bch_quintic_truncation_eq]
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num only [positivePowerTrunc, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, logCoeff, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six]
  unfold bchW6 bchY36 bchY46 bchY56 bchY35 bchY45
  simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, smul_add, smul_sub,
    two_smul, ← mul_assoc]
  module

/-- The BCH truncation through degree seven is the finite logarithm of homogeneous powers. -/
theorem bch_septic_truncation_eq (a b : A) :
    (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b + bchQuarticTerm a b +
      bchQuinticTerm a b + bchSexticTerm a b + bchSepticTerm a b =
      ∑ k ∈ range 8, logCoeff k • positivePowerTrunc (expMulTerm a b) k 8 := by
  rw [← sub_eq_zero.mp (octic_pure_identity a b), bch_sextic_truncation_eq]
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num only [positivePowerTrunc, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, logCoeff, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven]
  unfold bchW7 bchY37 bchY47 bchY57 bchY67
  simp only [pow_succ, pow_zero, one_mul, mul_one, mul_add, smul_add, smul_sub,
    two_smul, ← mul_assoc]
  module

/-! ### The degree-eight logarithm increment -/

section PowerComponents

variable {B : Type*} [Semiring B] [Algebra ℚ B]

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^1`. -/
lemma positivePowerCoeff_one_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 1 8 = bchT8 a b := by
  rw [positivePowerCoeff_one, expMulTerm_eight]

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^2`. -/
lemma positivePowerCoeff_two_eight (a b : A) :
    positivePowerCoeff (expMulTerm a b) 2 8 = 2 • bchT8 a b - bchW8 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchW8
  simp only [pow_one]
  abel

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^3`. -/
lemma positivePowerCoeff_three_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 3 8 = bchY38 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchY38
  simp only [mul_add, pow_succ, pow_zero, one_mul, ← mul_assoc]
  ac_rfl

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^4`. -/
lemma positivePowerCoeff_four_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 4 8 = bchY48 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchY48
  simp only [mul_add, pow_succ, pow_zero, one_mul, ← mul_assoc]
  ac_rfl

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^5`. -/
lemma positivePowerCoeff_five_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 5 8 = bchY58 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchY58
  simp only [mul_add, pow_succ, pow_zero, one_mul, ← mul_assoc]
  ac_rfl

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^6`. -/
lemma positivePowerCoeff_six_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 6 8 = bchY68 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchY68
  simp only [mul_add, pow_succ, pow_zero, one_mul, ← mul_assoc]
  ac_rfl

/-- The degree-eight homogeneous component of `(exp a * exp b - 1)^7`. -/
lemma positivePowerCoeff_seven_eight (a b : B) :
    positivePowerCoeff (expMulTerm a b) 7 8 = bchY78 a b := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  norm_num only [positivePowerCoeff_add_two, sum_range_succ, sum_range_zero, add_zero, zero_add,
    ite_true, ite_false, Nat.reduceSub, Nat.reduceAdd, h₁,
    expMulTerm_two, expMulTerm_three, expMulTerm_four, expMulTerm_five, expMulTerm_six,
    expMulTerm_seven, expMulTerm_eight, positivePowerCoeff_one, positivePowerCoeff_self]
  unfold bchY78
  simp only [mul_add, pow_succ, pow_zero, one_mul, ← mul_assoc]

end PowerComponents

/-- The degree-eight logarithm component is the octic BCH polynomial. -/
lemma bchOcticTerm_eq_sum_positivePowerCoeff (a b : A) :
    bchOcticTerm a b = ∑ k ∈ range 9, logCoeff k • positivePowerCoeff (expMulTerm a b) k 8 := by
  have h₁ : expMulTerm a b 1 = bchZ a b := expMulTerm_one a b
  rw [bchOcticTerm_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [positivePowerCoeff_one_eight, positivePowerCoeff_two_eight,
    positivePowerCoeff_three_eight, positivePowerCoeff_four_eight,
    positivePowerCoeff_five_eight, positivePowerCoeff_six_eight,
    positivePowerCoeff_seven_eight, positivePowerCoeff_self, h₁]
  norm_num only [logCoeff, positivePowerCoeff, zero_smul, add_zero, zero_add, one_smul]
  module

/-- The BCH truncation through degree eight is the finite logarithm of homogeneous powers. -/
theorem bch_octic_truncation_eq (a b : A) :
    (a + b) + (2 : ℚ)⁻¹ • (a * b - b * a) + bchCubicTerm a b + bchQuarticTerm a b +
      bchQuinticTerm a b + bchSexticTerm a b + bchSepticTerm a b + bchOcticTerm a b =
      ∑ k ∈ range 9, logCoeff k • positivePowerTrunc (expMulTerm a b) k 9 := by
  rw [sum_smul_positivePowerTrunc_succ logCoeff (expMulTerm a b) 8,
    ← bch_septic_truncation_eq, ← bchOcticTerm_eq_sum_positivePowerCoeff]

end FQFP.BCH
