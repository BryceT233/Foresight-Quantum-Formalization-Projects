/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.RingTheory.PowerSeries.Noncommutative.ExponentialCurve
public import FQFP.RingTheory.PowerSeries.Noncommutative.QuinticJet
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Centered seventh-degree coefficients from formal logarithms

A formal logarithm with linear, quintic, and septic terms determines the
product jet through degree seven. Centering adds one double commutator to the
septic logarithm coefficient.

## Main results

* `expListTerm_through_seven_of_log_jet`: the finite exponential jet.
* `coeff_centered_expListSeries_seven_of_log_jet`: the centered septic coefficient.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset PowerSeries

section Exponential

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The seventh exponential coefficient contains the septic logarithm term
and the three possible placements of its quintic term. -/
theorem expListTerm_seven_of_log_jet (l : List A) (G L K : A)
    (hlog : ∀ n : Fin 8, expListLogCoeff l n =
      if n = 1 then G else if n = 5 then L else if n = 7 then K else 0) :
    expListTerm l 7 = (1 / 5040 : ℚ) • G ^ 7 + K +
      (1 / 6 : ℚ) • (G ^ 2 * L + G * L * G + L * G ^ 2) := by
  rw [expListTerm_eq_sum_log_powers]
  have hc (k : ℕ) : positivePowerCoeff (expListLogCoeff l) k 7 =
      positivePowerCoeff
        (fun j ↦ if j = 1 then G else if j = 5 then L else if j = 7 then K else 0) k 7 := by
    apply positivePowerCoeff_congr
    intro i _ hi
    simpa [Fin.ext_iff] using hlog ⟨i, by lia⟩
  simp only [hc]
  norm_num only [positivePowerCoeff, sum_range_succ, sum_range_zero, Nat.factorial,
    Nat.reduceSub, Nat.reduceAdd, ite_true, ite_false, zero_mul, mul_zero,
    zero_smul, one_smul, add_zero, zero_add, mul_one, one_mul, smul_zero, pow_succ,
    smul_add, smul_smul, mul_add, add_mul]
  norm_num [mul_assoc]
  module

/-- Exponentiating a logarithm whose only terms through degree seven are
linear, quintic, and septic gives the complete product jet. -/
theorem expListTerm_through_seven_of_log_jet (l : List A) (G L K : A)
    (hlog : ∀ n : Fin 8, expListLogCoeff l n =
      if n = 1 then G else if n = 5 then L else if n = 7 then K else 0)
    (n : Fin 8) :
    expListTerm l n = (Nat.factorial n : ℚ)⁻¹ • G ^ (n : ℕ) +
      if n = 5 then L else if n = 6 then (1 / 2 : ℚ) • (G * L + L * G) else
      if n = 7 then K + (1 / 6 : ℚ) • (G ^ 2 * L + G * L * G + L * G ^ 2) else 0 := by
  by_cases hn : (n : ℕ) = 7
  · simpa [Fin.ext_iff, hn, Nat.factorial, add_assoc] using
      expListTerm_seven_of_log_jet l G L K hlog
  · have hn7 : (n : ℕ) < 7 := by
      have := n.isLt
      lia
    have hlow (i : Fin 7) : expListLogCoeff l i =
        if i = 1 then G else if i = 5 then L else 0 := by
      have hi : (i : ℕ) ≠ 7 := by
        have := i.isLt
        lia
      simpa [Fin.ext_iff, hi] using hlog ⟨i, by
        have := i.isLt
        lia⟩
    simpa [Fin.ext_iff, hn] using expListTerm_through_six_of_log_jet l G L hlow ⟨n, hn7⟩

end Exponential

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Centering the exponential product adds exactly the midpoint double
commutator to its seventh-degree logarithm coefficient. -/
theorem coeff_centered_expListSeries_seven_of_log_jet (l : List A) (G L K : A)
    (hlog : ∀ n : Fin 8, expListLogCoeff l n =
      if n = 1 then G else if n = 5 then L else if n = 7 then K else 0) :
    coeff 7 (exponentialCurve ((-1 / 2 : ℚ) • G) * expListSeries l *
      exponentialCurve ((-1 / 2 : ℚ) • G)) =
        K + (1 / 24 : ℚ) • ⁅G, ⁅G, L⁆⁆ := by
  have ht (i : ℕ) (hi : i < 8) : coeff i (expListSeries l) =
      (Nat.factorial i : ℚ)⁻¹ • G ^ i +
        if i = 5 then L else if i = 6 then (1 / 2 : ℚ) • (G * L + L * G) else
        if i = 7 then K + (1 / 6 : ℚ) • (G ^ 2 * L + G * L * G + L * G ^ 2) else 0 := by
    simpa [Fin.ext_iff] using
      expListTerm_through_seven_of_log_jet l G L K hlog ⟨i, hi⟩
  simp only [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero]
  simp (disch := decide) only [ht]
  norm_num [coeff_exponentialCurve, smul_pow, smul_smul, Nat.factorial]
  simp only [Ring.lie_def, pow_succ, pow_zero,
    smul_add, smul_sub, smul_smul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_neg,
    mul_assoc, one_mul]
  module

end FQFP
