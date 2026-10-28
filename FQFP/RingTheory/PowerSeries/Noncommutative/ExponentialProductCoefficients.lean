/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.PowerSeries.Noncommutative.Coefficients

/-!
# Homogeneous coefficients of three exponential factors

The factorial convolution keeps the order of all three factors and needs no topology.

## Main definitions

* `FQFP.expMulMulTerm`: a homogeneous term of `exp a * exp b * exp c`.

## Main results

* `FQFP.expMulMulTerm_zero`, `FQFP.expMulMulTerm_one`: the first two coefficients.
-/

@[expose] public noncomputable section

open Finset Finset.Nat

namespace FQFP

variable {A : Type*} [Semiring A] [Algebra ℚ A]

/-- The total-degree coefficient of an ordered product of three exponentials. -/
def expMulMulTerm (a b c : A) (n : ℕ) : A :=
  ∑ ij ∈ antidiagonal n,
    expMulTerm a b ij.1 * ((Nat.factorial ij.2 : ℚ)⁻¹ • c ^ ij.2)

/-- The constant coefficient of a triple exponential product is one. -/
@[simp]
lemma expMulMulTerm_zero (a b c : A) : expMulMulTerm a b c 0 = 1 := by
  simp [expMulMulTerm]

/-- The linear coefficient of a triple exponential product is the sum of its inputs. -/
@[simp]
lemma expMulMulTerm_one (a b c : A) : expMulMulTerm a b c 1 = a + b + c := by
  rw [expMulMulTerm, sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ]
  ac_rfl

end FQFP
