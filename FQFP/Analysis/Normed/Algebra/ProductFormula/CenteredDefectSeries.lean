/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SymmetricDefectSeries

/-!
# Formal centered Duhamel identity

Differentiating the centered symmetric product factors its derivative through
the same even half-defect used in the analytic Duhamel formula.

## Main results

* `seriesDerivative_centered_expListSeries`: the exact centered derivative identity.
-/

@[expose] public noncomputable section

open PowerSeries

namespace FQFP

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]

/-- The exact centered derivative factors through the reflected half-defect. -/
theorem seriesDerivative_centered_expListSeries (l : List A) (G : A) :
    seriesDerivative (exponentialCurve (-(1 / 2 : ℝ) • G) *
      (expListSeries l * expListSeries l.reverse) *
        exponentialCurve (-(1 / 2 : ℝ) • G)) =
      (exponentialCurve (-(1 / 2 : ℝ) • G) * expListSeries l) *
        (halfDefectSeries l G - halfDefectSeries (l.map Neg.neg) (-G)) *
          (expListSeries l.reverse * exponentialCurve (-(1 / 2 : ℝ) • G)) := by
  have hC : C (-(1 / 2 : ℝ) • G) = -(1 / 2 : ℝ) • C G := by
    ext n
    by_cases hn : n = 0 <;> simp [coeff_C, hn]
  rw [show (exponentialCurve (-(1 / 2 : ℝ) • G) * expListSeries l) *
        (halfDefectSeries l G - halfDefectSeries (l.map Neg.neg) (-G)) *
          (expListSeries l.reverse * exponentialCurve (-(1 / 2 : ℝ) • G)) =
      exponentialCurve (-(1 / 2 : ℝ) • G) *
        (expListSeries l *
          (halfDefectSeries l G - halfDefectSeries (l.map Neg.neg) (-G)) *
            expListSeries l.reverse) * exponentialCurve (-(1 / 2 : ℝ) • G) by
      noncomm_ring,
    ← symmetricResidualSeries_eq_halfDefect]
  rw [seriesDerivative_mul, seriesDerivative_mul]
  simp only [seriesDerivative_exponentialCurve]
  nth_rw 1 [← exponentialCurve_mul_C]
  simp only [hC, mul_add, add_mul, mul_sub, sub_mul,
    smul_mul_assoc, mul_smul_comm, smul_add, ← mul_assoc]
  module

end FQFP
