/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.GradedComposition
public import FQFP.Algebra.Lie.BCH.SuzukiHallBridge
public import FQFP.Algebra.Lie.BCH.Compatibility.SymmetricRecurrence
public import FQFP.Algebra.Lie.BCH.SymmetricCoefficients
public import FQFP.RingTheory.PowerSeries.Noncommutative.Palindromic

/-!
# The graded recurrence for actual Strang compositions

The cubic and quintic stage generators are the paper's Hall polynomials.
The scalar update therefore describes the formal logarithm of an actual
ordered product of Strang steps, and can be iterated over any weight list.

## Main results

* `expListLogCoeff_strang_eq_stage`: the logarithm of one actual Strang stage.
* `coeff_formalLog_strang_foldl`: semantic induction for the graded recurrence.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

open PowerSeries SuzukiGradedCoeff

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The paper's `C₃` and `D₅` are the coefficients of an actual scaled Strang logarithm. -/
theorem expListLogCoeff_strang_eq_stage (a b : A) (q : ℝ) (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    expListLogCoeff [(q / 2) • a, q • b, (q / 2) • a] n =
      (stage q).coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  have hargs : [(q / 2) • a, q • b, (q / 2) • a] =
      [((2 : ℚ)⁻¹ • a), b, ((2 : ℚ)⁻¹ • a)].map (fun x ↦ q • x) := by
    norm_num [← Rat.cast_smul_eq_qsmul ℝ, smul_smul, div_eq_mul_inv]
  rw [hargs, expListLogCoeff_smul, ← symmetricBchLieCoeff_eq_expListLogCoeff]
  fin_cases n
  · simp [SuzukiGradedCoeff.coeff]
  · simp [SuzukiGradedCoeff.coeff, stage, smul_add]
  · rw [symmetricBchLieCoeff_eq_zero_of_even a b 2 (by decide)]
    simp [SuzukiGradedCoeff.coeff]
  · rw [symmetricBchLieCoeff_three]
    norm_num only [zero_smul, add_zero, SuzukiGradedCoeff.coeff, stage,
      symmetricBchCubicLieTerm, suzukiStrangCubic,
      ← Rat.cast_smul_eq_qsmul ℝ]
  · rw [symmetricBchLieCoeff_eq_zero_of_even a b 4 (by decide)]
    simp [SuzukiGradedCoeff.coeff, stage]
  · rw [symmetricBchLieCoeff_five]
    norm_num only [zero_smul, add_zero, SuzukiGradedCoeff.coeff, stage,
      symmetricBchQuinticLieTerm, suzukiStrangQuintic,
      ← Rat.cast_smul_eq_qsmul ℝ]

/-- Appending a Strang step to any partial product implements the paper's BCH update. -/
theorem coeff_formalLog_mul_strang (a b : A) (s : SuzukiGradedCoeff) (q : ℝ)
    (P : PowerSeries A) (hP : constantCoeff P = 1)
    (hlogP : letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
      ∀ n : Fin 6, PowerSeries.coeff n (formalLog P) =
        s.coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n)
    (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n (formalLog (P *
      expListSeries [(q / 2) • a, q • b, (q / 2) • a])) =
      (s.append q).coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  apply coeff_formalLog_mul_of_log_eq s q _ _ _ P _ hP (by simp [expListSeries]) hlogP
  intro i
  rw [coeff_formalLog_expListSeries]
  exact expListLogCoeff_strang_eq_stage a b q i

/-- The recurrence describes the logarithm after any finite sequence of actual Strang stages. -/
theorem coeff_formalLog_strang_foldl (a b : A) (weights : List ℝ)
    (s : SuzukiGradedCoeff) (P : PowerSeries A) (hP : constantCoeff P = 1)
    (hlogP : letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
      ∀ n : Fin 6, PowerSeries.coeff n (formalLog P) =
        s.coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n)
    (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n (formalLog (weights.foldl (fun R q ↦
      R * expListSeries [(q / 2) • a, q • b, (q / 2) • a]) P)) =
      (weights.foldl append s).coeff (a + b)
        (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  induction weights generalizing s P with
  | nil => exact hlogP n
  | cons q weights ih =>
      apply ih (s.append q) _ (by simp [expListSeries, hP])
      exact coeff_formalLog_mul_strang a b s q P hP hlogP

/-- Starting at the identity, the scalar fold gives the actual composition logarithm. -/
theorem coeff_formalLog_strang_composition (a b : A) (weights : List ℝ) (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n (formalLog (weights.foldl (fun R q ↦
      R * expListSeries [(q / 2) • a, q • b, (q / 2) • a]) 1)) =
      (weights.foldl append SuzukiGradedCoeff.zero).coeff (a + b)
        (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  apply coeff_formalLog_strang_foldl a b weights SuzukiGradedCoeff.zero 1 (by simp)
  intro i
  fin_cases i <;> simp [SuzukiGradedCoeff.coeff, SuzukiGradedCoeff.zero]

/-- The actual five-stage Strang logarithm has the paper's terminal coefficient state. -/
theorem coeff_formalLog_fiveStrang (a b : A) (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) (n : Fin 6) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff n (formalLog ([u, u, 1 - 4 * u, u, u].foldl (fun R q ↦
      R * expListSeries [(q / 2) • a, q • b, (q / 2) • a]) 1)) =
      (target u).coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) n := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [coeff_formalLog_strang_composition]
  change (fiveStages u).coeff _ _ _ _ = _
  rw [fiveStages_eq_target u hu]

/-- Graded BCH and the independent word certificate yield the same quintic operator. -/
theorem coeff_formalLog_fiveStrang_five (a b : A) (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    PowerSeries.coeff 5 (formalLog ([u, u, 1 - 4 * u, u, u].foldl (fun R q ↦
      R * expListSeries [(q / 2) • a, q • b, (q / 2) • a]) 1)) =
      suzukiQuinticTerm a b u := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  calc
    _ = (target u).coeff (a + b) (suzukiStrangCubic a b) (suzukiStrangQuintic a b) 5 := by
      simpa using coeff_formalLog_fiveStrang a b u hu (5 : Fin 6)
    _ = _ := suzukiQuinticTerm_eq_hall a b u |>.symm

end FQFP.BCH
