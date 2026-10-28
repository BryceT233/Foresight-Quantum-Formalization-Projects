/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SuzukiGradedRecurrence
public import FQFP.RingTheory.PowerSeries.Noncommutative.FormalExpLog

/-!
# Formal semantics of the graded BCH update

The five-coordinate recurrence is interpreted as a formal logarithm in any
real associative algebra. The generators have weights one, three and five.

## Main definitions

* `SuzukiGradedCoeff.coeff`: the graded logarithm coefficient function.
* `SuzukiGradedCoeff.stage`: the logarithm coordinates of a scaled stage.

## Main results

* `SuzukiGradedCoeff.coeff_formalLog_mul_of_log_eq`: the semantic BCH update.
-/

@[expose] public noncomputable section

namespace FQFP.BCH.SuzukiGradedCoeff

open Finset Finset.Nat PowerSeries

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The weighted logarithm with generators of degrees one, three and five. -/
def coeff (s : SuzukiGradedCoeff) (G C D : A) : ℕ → A
  | 1 => s.a • G
  | 3 => s.b • C
  | 4 => s.c • (G * C - C * G)
  | 5 => s.d • D + s.e • (G * (G * C - C * G) - (G * C - C * G) * G)
  | _ => 0

/-- The logarithm coefficients of one stage of weight `q`. -/
def stage (q : ℝ) : SuzukiGradedCoeff := ⟨q, q ^ 3, 0, q ^ 5, 0⟩

/-- The exponential coefficients of a series with zero quadratic coefficient. -/
private lemma coeff_formalExp_sparse {B : Type*} [Ring B] [Algebra ℚ B]
    (W : PowerSeries B) (h2 : PowerSeries.coeff 2 W = 0) (n : Fin 6) :
    PowerSeries.coeff n (formalExp W) =
      (![1, PowerSeries.coeff 1 W,
        (1 / 2 : ℚ) • PowerSeries.coeff 1 W ^ 2,
        PowerSeries.coeff 3 W + (1 / 6 : ℚ) • PowerSeries.coeff 1 W ^ 3,
        PowerSeries.coeff 4 W + (1 / 2 : ℚ) •
          (PowerSeries.coeff 1 W * PowerSeries.coeff 3 W +
            PowerSeries.coeff 3 W * PowerSeries.coeff 1 W) +
          (1 / 24 : ℚ) • PowerSeries.coeff 1 W ^ 4,
        PowerSeries.coeff 5 W + (1 / 2 : ℚ) •
          (PowerSeries.coeff 1 W * PowerSeries.coeff 4 W +
            PowerSeries.coeff 4 W * PowerSeries.coeff 1 W) +
          (1 / 6 : ℚ) • (PowerSeries.coeff 1 W ^ 2 * PowerSeries.coeff 3 W +
            PowerSeries.coeff 1 W * PowerSeries.coeff 3 W * PowerSeries.coeff 1 W +
            PowerSeries.coeff 3 W * PowerSeries.coeff 1 W ^ 2) +
          (1 / 120 : ℚ) • PowerSeries.coeff 1 W ^ 5] : Fin 6 → B) n := by
  fin_cases n <;>
    norm_num only [coeff_formalExp, positivePowerCoeff, sum_range_succ, sum_range_zero,
      Nat.reduceSub, Nat.reduceAdd, ite_true, ite_false, zero_mul, mul_zero,
      zero_smul, one_smul, add_zero, zero_add, mul_one, one_mul, smul_zero,
      Nat.factorial, h2]
  all_goals
    norm_num [pow_succ, mul_assoc, smul_add, mul_add, add_mul]

/-- Multiplication of stage exponentials realizes the graded update through degree five. -/
lemma coeff_mul_formalExp (s : SuzukiGradedCoeff) (q : ℝ)
    (G C D : A) (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n
      (formalExp (PowerSeries.mk (s.coeff G C D)) *
        formalExp (PowerSeries.mk ((stage q).coeff G C D))) =
      PowerSeries.coeff n (formalExp (PowerSeries.mk ((s.append q).coeff G C D))) := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  have he (r : SuzukiGradedCoeff) (i : ℕ) (hi : i < 6) :=
    coeff_formalExp_sparse (PowerSeries.mk (r.coeff G C D)) (by simp [coeff]) ⟨i, hi⟩
  fin_cases n
  all_goals
    simp only [coeff_mul, sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ, sum_range_zero]
    simp (disch := decide) only [he]
    norm_num [coeff_mk, coeff, stage, append, ← Rat.cast_smul_eq_qsmul ℝ]
  all_goals
    simp only [pow_succ, pow_zero, one_mul,
      add_smul, sub_smul, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
    module

/-- The actual formal BCH product realizes the five-coordinate update. -/
theorem coeff_formalLog_mul_formalExp (s : SuzukiGradedCoeff) (q : ℝ)
    (G C D : A) (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n
      (formalLog (formalExp (PowerSeries.mk (s.coeff G C D)) *
        formalExp (PowerSeries.mk ((stage q).coeff G C D)))) = (s.append q).coeff G C D n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  calc
    _ = PowerSeries.coeff n
        (formalLog (formalExp (PowerSeries.mk ((s.append q).coeff G C D)))) := by
      apply coeff_formalLog_congr
      intro i _ hi
      exact coeff_mul_formalExp s q G C D ⟨i, by
        have := n.isLt
        lia⟩
    _ = _ := by
      rw [formalLog_formalExp _ (by simp [coeff, constantCoeff_mk]), coeff_mk]

/-- Appending any unit-constant series with the stage logarithm updates the actual logarithm. -/
theorem coeff_formalLog_mul_of_log_eq (s : SuzukiGradedCoeff) (q : ℝ)
    (G C D : A) (P Q : PowerSeries A)
    (hP : constantCoeff P = 1) (hQ : constantCoeff Q = 1)
    (hlogP : letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
      ∀ n : Fin 6, PowerSeries.coeff n (formalLog P) = s.coeff G C D n)
    (hlogQ : letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
      ∀ n : Fin 6, PowerSeries.coeff n (formalLog Q) = (stage q).coeff G C D n)
    (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n (formalLog (P * Q)) = (s.append q).coeff G C D n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  have hexp (R : PowerSeries A) (r : SuzukiGradedCoeff) (hR : constantCoeff R = 1)
      (hr : ∀ i : Fin 6, PowerSeries.coeff i (formalLog R) = r.coeff G C D i)
      (i : ℕ) (hi : i < 6) :
      PowerSeries.coeff i R =
        PowerSeries.coeff i (formalExp (PowerSeries.mk (r.coeff G C D))) := by
    calc
      _ = PowerSeries.coeff i (formalExp (formalLog R)) := by rw [formalExp_formalLog R hR]
      _ = _ := by
        apply coeff_formalExp_congr
        intro j _ hj
        simpa only [coeff_mk] using hr ⟨j, by lia⟩
  calc
    _ = PowerSeries.coeff n (formalLog
        (formalExp (PowerSeries.mk (s.coeff G C D)) *
          formalExp (PowerSeries.mk ((stage q).coeff G C D)))) := by
      apply coeff_formalLog_congr
      intro i _ hi
      simp only [coeff_mul]
      apply sum_congr rfl
      intro ij hij
      have hij' := mem_antidiagonal.mp hij
      have hn := n.isLt
      rw [hexp P s hP hlogP ij.1 (by lia), hexp Q (stage q) hQ hlogQ ij.2 (by lia)]
    _ = _ := coeff_formalLog_mul_formalExp s q G C D n

end FQFP.BCH.SuzukiGradedCoeff
