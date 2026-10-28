/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.CommutatorFamily
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Norm sums of binary quintic commutators

The eight right-nested degree-five commutators are imported from the algebraic layer.
This file defines their unit-weight norm sum, the displayed two-summand weights from
Childs et al., Appendix J, Proposition J.1, and rational upper bounds for the absolute
Suzuki quintic coefficients at the standard parameter.

The family is redundant. With zero-based `Fin 8` indices, Jacobi identifies entries
`1` and `2`, and entries `5` and `6`. The reduced Suzuki representation sets coefficients
`2` and `6` to zero. These are a commutator family and bound weights, not a basis or
optimal coefficients.

The reference weights are stored as the exact rationals represented by the published
decimals. Their local-error inequality is distinct from the quintic logarithm estimates
proved using the coefficient upper bounds.
-/

@[expose] public section

open Finset

namespace FQFP.BCH

-- The associative-ring Lie bracket `⁅A, B⁆ = A * B - B * A`, so that the standard Lie-bracket
-- lemmas are available.
attribute [local instance] LieRing.ofAssociativeRing


variable {𝔸 : Type*} [NormedRing 𝔸]

/-! ### Weights and the unit-coefficient norm sum -/

/-- Sum of the norms of the eight binary quintic commutators, with unit weights. -/
def binaryQuinticCommutatorNormSum (A B : 𝔸) : ℝ :=
  ∑ i : Fin 8, ‖binaryQuinticCommutator A B i‖

lemma binaryQuinticCommutatorNormSum_nonneg (A B : 𝔸) : 0 ≤ binaryQuinticCommutatorNormSum A B :=
  sum_nonneg fun _ _ => norm_nonneg _

/-- The displayed rational weights of the two-summand fourth-order Suzuki bound in
Childs et al., Appendix J, Proposition J.1, in binary quintic commutator order. -/
def suzukiFourthOrderCommutatorBoundWeight : Fin 8 → ℝ :=
  ![0.0047, 0.0057, 0.0046, 0.0074, 0.0097, 0.0097, 0.0173, 0.0284]

lemma suzukiFourthOrderCommutatorBoundWeight_nonneg (i : Fin 8) :
    0 ≤ suzukiFourthOrderCommutatorBoundWeight i := by
  fin_cases i <;> norm_num [suzukiFourthOrderCommutatorBoundWeight]

/-- Rational upper bounds for the absolute Suzuki quintic coefficients at `suzukiP`.
The nonzero bounds round upward to the `1 / 10⁶` grid; indices `2` and `6` are zero.
Componentwise domination is proved in `SuzukiQuinticBounds`. No optimality is claimed. -/
noncomputable def suzukiQuinticCoeffUpperBound : Fin 8 → ℝ :=
  ![260 / 1000000, 663 / 1000000, 0, 132 / 1000000,
    376 / 1000000, 1128 / 1000000, 0, 442 / 1000000]

lemma suzukiQuinticCoeffUpperBound_nonneg (i : Fin 8) : 0 ≤ suzukiQuinticCoeffUpperBound i := by
  fin_cases i <;> norm_num [suzukiQuinticCoeffUpperBound]

/-! ### Weighted norm estimates -/

/-- A weighted sum of commutator norms with nonnegative weights is nonnegative. -/
theorem sum_mul_norm_binaryQuinticCommutator_nonneg {γ : Fin 8 → ℝ} (hγ : ∀ i, 0 ≤ γ i) (A B : 𝔸) :
    0 ≤ ∑ i : Fin 8, γ i * ‖binaryQuinticCommutator A B i‖ :=
  sum_nonneg fun i _ => mul_nonneg (hγ i) (norm_nonneg _)

/-- The coefficient upper bounds are at most one, so their weighted norm sum is bounded
by the unit-weight binary quintic commutator norm sum. -/
theorem suzukiQuinticCoeffUpperBound_sum_mul_norm_le_binaryQuinticCommutatorNormSum (A B : 𝔸) :
    ∑ i : Fin 8, suzukiQuinticCoeffUpperBound i * ‖binaryQuinticCommutator A B i‖ ≤
      binaryQuinticCommutatorNormSum A B :=
  sum_le_sum fun i _ => by
    have h1 : suzukiQuinticCoeffUpperBound i ≤ 1 := by
      fin_cases i <;> norm_num [suzukiQuinticCoeffUpperBound]
    calc suzukiQuinticCoeffUpperBound i * ‖binaryQuinticCommutator A B i‖
        ≤ 1 * ‖binaryQuinticCommutator A B i‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖binaryQuinticCommutator A B i‖ := one_mul _

end FQFP.BCH
