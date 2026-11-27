/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SymmetricCenteredLocalError
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SepticRemainder
import FQFP.Analysis.SpecialFunctions.Integrals.Monomial

/-!
# Ninth-order local bounds for symmetric products

The complete quartic and sextic middle-defect coefficients are integrated together.
The resulting bound holds for every real step under two-sided exponential control.

## Main results

* `sum_even_pow_smul_eq_quartic_add_sextic`: the even defect polynomial.
* `norm_halfDefect_add_sub_quartic_sub_sextic_le`: the grouped eighth-order tail.
* `norm_symmetricExpProduct_sub_exp_le_septic`: the all-real ninth-order local bound.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory TrotterError Finset
open scoped RealScalar

namespace FQFP

/-- The even polynomial through degree seven retains exactly its quartic and sextic terms. -/
lemma sum_even_pow_smul_eq_quartic_add_sextic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (c : ℕ → E) (L M : E) (h0 : c 0 = 0) (h2 : c 2 = 0)
    (h4 : c 4 = (5 / 2 : ℝ) • L) (h6 : c 6 = (7 / 2 : ℝ) • M) (x : ℝ) :
    (∑ k ∈ range 8, (x ^ k + (-x) ^ k) • c k) =
      (5 * x ^ 4) • L + (7 * x ^ 6) • M := by
  simp only [sum_range_succ, sum_range_zero, h0, h2, h4, h6]
  module

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The grouped eighth-order defect tail, with both leading coefficients kept whole. -/
theorem norm_halfDefect_add_sub_quartic_sub_sextic_le {s : ℕ} (Z : Fin s → A)
    (G L M : A) (hZ : ∀ (i : Fin s) (t : ℝ), ‖exp (t • Z i)‖ ≤ 1)
    (h0 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 0 = 0)
    (h2 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 2 = 0)
    (h4 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 4 = (5 / 2 : ℝ) • L)
    (h6 : groupedConjCoeff (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 6 = (7 / 2 : ℝ) • M)
    (x : ℝ) :
    ‖halfDefect (List.ofFn Z) G x + halfDefect (List.ofFn Z) G (-x) -
      (5 * x ^ 4) • L - (7 * x ^ 6) • M‖ ≤
        2 * |x| ^ 8 * groupedConjBound (fun i ↦ -Z i) Z (-(1 / 2 : ℝ) • G) 8 := by
  have hb := norm_halfDefect_add_sub_sum_le Z G hZ 8 (by norm_num) x
  rw [sum_even_pow_smul_eq_quartic_add_sextic _ L M h0 h2 h4 h6, sub_add_eq_sub_sub] at hb
  exact hb

/-- Integrating the three even defect powers gives their three odd local-error powers. -/
lemma abs_integral_septicError_polynomial_le (ℓ μ C h : ℝ) (hℓ : 0 ≤ ℓ)
    (hμ : 0 ≤ μ) (hC : 0 ≤ C) :
    |∫ x in 0..h, 5 * |x| ^ 4 * ℓ + 7 * |x| ^ 6 * μ + 9 * C * |x| ^ 8| ≤
      septicStepBound ℓ μ C |h| := by
  have hpoly := abs_integral_sum_mul_abs_pow univ ![4, 6, 8] ![ℓ, μ, C] (by
    intro i _
    fin_cases i <;> assumption) h
  norm_num [Fin.sum_univ_three] at hpoly
  simpa only [septicStepBound, add_assoc, mul_right_comm 9 C] using hpoly.le

/-- **Ninth-order local symmetric product bound**, valid for every real step. -/
theorem norm_symmetricExpProduct_sub_exp_le_septic (l : List A) (G L M : A) (C : ℝ)
    (hC : 0 ≤ C) (hZ : ∀ Z ∈ l, ∀ t : ℝ, ‖exp (t • Z)‖ ≤ 1)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (hT : ∀ x : ℝ, ‖halfDefect l G x + halfDefect l G (-x) -
      (5 * x ^ 4) • L - (7 * x ^ 6) • M‖ ≤ 9 * C * |x| ^ 8) (h : ℝ) :
    ‖symmetricExpProduct l h - exp (h • G)‖ ≤ septicStepBound ‖L‖ ‖M‖ C |h| := by
  calc
    _ ≤ |∫ x in 0..h, 5 * |x| ^ 4 * ‖L‖ + 7 * |x| ^ 6 * ‖M‖ +
        9 * C * |x| ^ 8| := by
      apply norm_symmetricExpProduct_sub_exp_le_abs_integral l G hZ hG h
      · apply Continuous.intervalIntegrable
        fun_prop
      intro x _
      calc
        _ ≤ ‖halfDefect l G x + halfDefect l G (-x) -
              ((5 * x ^ 4) • L + (7 * x ^ 6) • M)‖ +
            ‖(5 * x ^ 4) • L + (7 * x ^ 6) • M‖ := norm_le_norm_sub_add _ _
        _ ≤ 9 * C * |x| ^ 8 + (5 * |x| ^ 4 * ‖L‖ + 7 * |x| ^ 6 * ‖M‖) := by
          apply add_le_add
          · simpa only [sub_add_eq_sub_sub] using hT x
          · exact (norm_add_le _ _).trans_eq (by simp [norm_smul, Real.norm_eq_abs])
        _ = _ := add_comm _ _
    _ ≤ _ := abs_integral_septicError_polynomial_le _ _ _ _ (norm_nonneg _) (norm_nonneg _) hC

end FQFP
