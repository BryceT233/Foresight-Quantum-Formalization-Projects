/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSeries
public import FQFP.RingTheory.PowerSeries.Noncommutative.Palindromic

/-!
# The sixth-order Suzuki jet

Palindromic symmetry removes the sixth logarithm coefficient. Formal
exponentiation then recovers the ordered product coefficients through degree six.

## Main results

* `expListLogCoeff_fiveStageStrang_through_six`: the complete logarithm jet.
* `expListTerm_fiveStageStrang_through_six`: the ordered product coefficients through degree six.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

open Finset PowerSeries

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]

/-- The logarithm jet through degree six, including all zero coefficients. -/
theorem expListLogCoeff_fiveStageStrang_through_six (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 7) :
    expListLogCoeff (fiveStageStrangArguments a b p 1) n =
      if n = 1 then a + b else if n = 5 then suzukiQuinticTerm a b p else 0 := by
  by_cases hn : (n : ℕ) < 6
  · simpa [Fin.ext_iff] using
      expListLogCoeff_fiveStageStrang_through_five a b p hp ⟨n, hn⟩
  · have hn6 : (n : ℕ) = 6 := by
      have := n.isLt
      lia
    simp only [Fin.ext_iff, hn6]
    exact expListLogCoeff_eq_zero_of_reverse_eq _
      (fiveStageStrangArguments_reverse a b p 1) 6 (by decide)

/-- The exponential product jet is determined by the linear and quintic logarithm terms. -/
theorem expListTerm_fiveStageStrang_through_six (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 7) :
    expListTerm (fiveStageStrangArguments a b p 1) n =
      (Nat.factorial n : ℚ)⁻¹ • (a + b) ^ (n : ℕ) +
        if n = 5 then suzukiQuinticTerm a b p else
        if n = 6 then (2 : ℚ)⁻¹ •
          ((a + b) * suzukiQuinticTerm a b p + suzukiQuinticTerm a b p * (a + b)) else 0 := by
  rw [expListTerm_eq_sum_log_powers]
  have hc (k : ℕ) :
      positivePowerCoeff (expListLogCoeff (fiveStageStrangArguments a b p 1)) k n =
        positivePowerCoeff
          (fun j ↦ if j = 1 then a + b else if j = 5 then suzukiQuinticTerm a b p else 0) k n := by
    apply positivePowerCoeff_congr
    intro i _ hi
    simpa [Fin.ext_iff] using
      expListLogCoeff_fiveStageStrang_through_six a b p hp
        ⟨i, by
          have := n.isLt
          lia⟩
  simp only [hc]
  generalize a + b = G
  generalize suzukiQuinticTerm a b p = L
  fin_cases n <;>
    norm_num only [positivePowerCoeff, sum_range_succ, sum_range_zero, Nat.factorial,
      Nat.reduceSub, Nat.reduceAdd, ite_true, ite_false, zero_mul, mul_zero,
      zero_smul, one_smul, add_zero, zero_add, mul_one, one_mul, smul_zero, pow_succ,
      smul_add, smul_smul, mul_add, add_mul]
  all_goals norm_num [Fin.ext_iff, mul_assoc]
  all_goals module

end FQFP.BCH
