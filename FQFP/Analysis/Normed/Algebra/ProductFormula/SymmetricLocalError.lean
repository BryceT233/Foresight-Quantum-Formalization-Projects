/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SymmetricDefect
import FQFP.Analysis.Normed.Ring.ContractionProduct
import FQFP.Analysis.SpecialFunctions.Integrals.Monomial

/-!
# Local error from an even symmetric defect

The symmetric Duhamel formula transports the middle defect without norm growth.
Integrating a fourth-degree leading term and a sixth-degree remainder gives the
fifth- and seventh-degree local error bound for every real step.

## Main results

* `norm_symmetricExpProduct_sub_exp_le`: integrate a bound for the middle defect.
* `norm_symmetricExpProduct_sub_exp_le_abs_integral`: integrate an arbitrary scalar majorant.
* `norm_halfDefect_add_sub_sum_le`: grouped remainder for the even middle defect.
* `norm_symmetricExpProduct_sub_exp_le_grouped`: the grouped seventh-degree constant.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory TrotterError Finset
open scoped RealScalar

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- A product of exponentials with two-sided contraction bounds acts isometrically on the left. -/
lemma norm_expListProduct_mul_eq_of_le_one (l : List A) (B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (t : ℝ) :
    ‖expListProduct l t * B‖ = ‖B‖ := by
  induction l with
  | nil => simp
  | cons Z l ih =>
      rw [expListProduct_cons, mul_assoc,
        norm_exp_smul_mul_eq_of_le_one Z _ (hZ Z (by simp)) t]
      exact ih (fun Z hmem ↦ hZ Z (by simp [hmem]))

/-- Under two-sided contraction bounds, an ordered exponential product has the norm of one. -/
lemma norm_expListProduct_eq_norm_one (l : List A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (t : ℝ) :
    ‖expListProduct l t‖ = ‖(1 : A)‖ := by
  simpa only [mul_one] using norm_expListProduct_mul_eq_of_le_one l 1 hZ t

/-- A product of exponentials with two-sided contraction bounds acts isometrically on the right. -/
lemma norm_mul_expListProduct_eq_of_le_one (l : List A) (B : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (t : ℝ) :
    ‖B * expListProduct l t‖ = ‖B‖ := by
  cases l with
  | nil => simp only [expListProduct_nil, mul_one]
  | cons Z l =>
    have h1 : ‖(1 : A)‖ ≤ 1 := by simpa only [zero_smul, exp_zero] using hZ Z List.mem_cons_self 0
    have hrev := norm_expListProduct_eq_norm_one (Z :: l).reverse
      (by simpa only [List.mem_reverse] using hZ) (-t)
    exact norm_mul_eq_norm_left_of_mul_eq_one (expListProduct_mul_reverse_neg (Z :: l) t)
      ((norm_expListProduct_eq_norm_one _ hZ t).le.trans h1) (hrev.le.trans h1) B

/-- The two exterior half-products preserve the norm of the middle defect. -/
lemma norm_symmetricDefect_eq_of_le_one (l : List A) (G : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (x : ℝ) :
    ‖symmetricDefect l G x‖ = ‖halfDefect l G x + halfDefect l G (-x)‖ := by
  rw [symmetricDefect_eq_halfDefect_add,
    norm_mul_expListProduct_eq_of_le_one l.reverse _
      (fun Z hmem ↦ hZ Z (by simpa using hmem)),
    norm_expListProduct_mul_eq_of_le_one l _ hZ]

/-- An integrable majorant for the middle defect bounds the local error for either sign of `h`. -/
theorem norm_symmetricExpProduct_sub_exp_le_abs_integral (l : List A) (G : A)
    (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1) (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h : ℝ) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 h)
    (hbound : ∀ x ∈ Set.uIoc 0 h, ‖halfDefect l G x + halfDefect l G (-x)‖ ≤ g x) :
    ‖symmetricExpProduct l h - exp (h • G)‖ ≤ |∫ x in 0..h, g x| := by
  rw [symmetricExpProduct_sub_exp_eq_integral]
  apply intervalIntegral.norm_integral_le_abs_of_norm_le _ hg
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards with x hx
  rw [norm_mul_exp_smul_eq_of_le_one G _ hG, norm_exp_smul_mul_eq_of_le_one G _ hG,
    norm_symmetricDefect_eq_of_le_one l G hZ]
  exact hbound x hx

/-- Integrating the positive even polynomial gives the two local error powers,
with an absolute value accounting for either interval orientation. -/
lemma abs_integral_localError_polynomial_le (N C : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (h : ℝ) :
    |∫ x in 0..h, 5 * |x| ^ 4 * N + 7 * C * |x| ^ 6| ≤ |h| ^ 5 * N + |h| ^ 7 * C := by
  have hpoly := abs_integral_sum_mul_abs_pow univ ![4, 6] ![N, C] (by
    intro i _
    fin_cases i <;> assumption) h
  norm_num [Fin.sum_univ_two] at hpoly
  simpa only [mul_right_comm 7 C] using hpoly.le

/-- **Local symmetric product error.** A fourth-degree middle defect with a
sixth-degree remainder gives the sharp unsplit fifth-degree coefficient. -/
theorem norm_symmetricExpProduct_sub_exp_le (l : List A) (G L : A) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ ≤
      7 * C * |x| ^ 6) (h : ℝ) :
    ‖symmetricExpProduct l h - exp (h • G)‖ ≤ |h| ^ 5 * ‖L‖ + |h| ^ 7 * C := by
  calc
    _ ≤ |∫ x in 0..h, 5 * |x| ^ 4 * ‖L‖ + 7 * C * |x| ^ 6| := by
      apply norm_symmetricExpProduct_sub_exp_le_abs_integral l G hZ hG h
      · apply Continuous.intervalIntegrable
        fun_prop
      intro x _
      calc
        _ ≤ ‖halfDefect l G x + halfDefect l G (-x) - (5 * x ^ 4) • L‖ +
            ‖(5 * x ^ 4) • L‖ := norm_le_norm_sub_add _ _
        _ ≤ 7 * C * |x| ^ 6 + ‖(5 * x ^ 4) • L‖ := add_le_add_left (hT x) _
        _ = _ := by simp [norm_smul, Real.norm_eq_abs, add_comm]
    _ ≤ _ := abs_integral_localError_polynomial_le ‖L‖ C (norm_nonneg _) hC h

/-- The grouped finite remainder controls the even middle defect without
splitting any recursively combined coefficient inside its norm. -/
theorem norm_halfDefect_add_sub_sum_le {s : ℕ} (Z : Fin s → A) (G : A)
    (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (p : ℕ) (hp : 1 ≤ p) (x : ℝ) :
    ‖halfDefect (List.ofFn Z) G x + halfDefect (List.ofFn Z) G (-x) -
      ∑ k ∈ range p, (x ^ k + (-x) ^ k) •
        groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) k‖ ≤
      2 * |x| ^ p * groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) p := by
  let c := groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G)
  let B := groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) p
  have hb (t : ℝ) :
      ‖halfDefect (List.ofFn Z) G t - ∑ k ∈ range p, t ^ k • c k‖ ≤ |t| ^ p * B := by
    rw [halfDefect_eq_groupedConj]
    exact norm_groupedConj_sub_sum_le _ _ _
      (fun i u ↦ by simpa only [smul_neg, neg_smul] using hZ i (-u)) p hp t
  change ‖_ + _ - ∑ k ∈ range p, (x ^ k + (-x) ^ k) • c k‖ ≤ 2 * |x| ^ p * B
  simpa only [add_smul, sum_add_distrib, add_sub_add_comm, abs_neg, two_mul, add_mul] using
    norm_add_le_of_le (hb x) (hb (-x))

/-- The even polynomial through degree five is determined by its three even coefficients. -/
lemma sum_even_pow_smul_eq_quartic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ℕ → E) (L : E)
    (h0 : c 0 = 0) (h2 : c 2 = 0) (h4 : c 4 = (5 / 2 : ℝ) • L) (x : ℝ) :
    (∑ k ∈ range 6, (x ^ k + (-x) ^ k) • c k) = (5 * x ^ 4) • L := by
  simp only [sum_range_succ, sum_range_zero, h0, h2, h4]
  module

/-- The grouped sixth-order defect remainder gives the local seventh-order
constant `2 * groupedConjBound / 7`, retaining the complete fifth-degree term. -/
theorem norm_symmetricExpProduct_sub_exp_le_grouped {s : ℕ} (Z : Fin s → A) (G L : A)
    (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h0 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 0 = 0)
    (h2 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 2 = 0)
    (h4 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 4 = (5 / 2 : ℝ) • L)
    (h : ℝ) :
    ‖symmetricExpProduct (List.ofFn Z) h - exp (h • G)‖ ≤
      |h| ^ 5 * ‖L‖ + |h| ^ 7 *
        (2 * groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 6 / 7) := by
  apply norm_symmetricExpProduct_sub_exp_le
  · exact div_nonneg (mul_nonneg (by norm_num) (groupedConjBound_nonneg ..)) (by norm_num)
  · intro z hz t
    rcases List.mem_ofFn.mp hz with ⟨i, rfl⟩
    exact hZ i t
  · exact hG
  · intro x
    have hb := norm_halfDefect_add_sub_sum_le Z G hZ 6 (by norm_num) x
    rw [sum_even_pow_smul_eq_quartic _ L h0 h2 h4] at hb
    convert hb using 1
    ring

end FQFP
