/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticCoefficients
public import FQFP.Analysis.Normed.Algebra.ProductFormula.CenteredDefectSeries
public import FQFP.RingTheory.PowerSeries.Noncommutative.SepticJet

/-!
# The formal centered seventh-degree Suzuki coefficient

The full product logarithm and the half-defect recurrence describe the same
centered coefficient. All coefficient comparisons use finite Cauchy sums.

## Main results

* `expListLogCoeff_suzukiHalf_through_seven`: the formal logarithm jet.
* `coeff_suzuki_centered_seven`: the same centered product has septic coefficient `N₇`.
* `suzukiCenteredSepticTerm_eq_bch`: the exact relation between the centered and BCH terms.
-/

@[expose] public noncomputable section

open FQFP TrotterError Finset PowerSeries
open scoped RealScalar

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- The full symmetric product has its certified logarithm jet through degree seven. -/
theorem expListLogCoeff_suzukiHalf_through_seven (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 8) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    expListLogCoeff (l ++ l.reverse) n =
      if n = 1 then a + b else if n = 5 then suzukiQuinticTerm a b p else
        if n = 7 then suzukiBchSepticTerm a b p else 0 := by
  dsimp only
  have hq : Algebra.restrictScalars ℚ ℝ A = (inferInstance : Algebra ℚ A) :=
    Subsingleton.elim _ _
  by_cases hn : (n : ℕ) < 6
  · have he : expListLogCoeff
        (List.ofFn (fiveStageStrangHalfGenerator a b p) ++
          (List.ofFn (fiveStageStrangHalfGenerator a b p)).reverse) n =
        expListLogCoeff (fiveStageStrangArguments a b p 1) n := by
      unfold expListLogCoeff
      apply sum_congr rfl
      intro k hk
      congr 1
      apply positivePowerCoeff_congr
      intro j hj hjn
      rw [← coeff_expListSeries, expListSeries_append,
        coeff_symmetricHalfSeries_fiveStageStrang a b p hp ⟨j, by lia⟩,
        expListTerm_fiveStageStrang_through_six a b p hp ⟨j, by lia⟩]
      have hj6 : j ≠ 6 := by lia
      simp [Fin.ext_iff, hj6]
    rw [he, expListLogCoeff_fiveStageStrang_through_five a b p hp ⟨n, hn⟩]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | lia
  · have hn' : (n : ℕ) = 6 ∨ (n : ℕ) = 7 := by
      have := n.isLt
      lia
    rcases hn' with h6 | h7
    · have he := expListLogCoeff_suzuki_even a b p 6 (by decide)
      rw [hq] at he
      simpa [Fin.ext_iff, h6] using he
    · simp only [Fin.ext_iff, h7]
      unfold suzukiBchSepticTerm
      rw [hq]
      norm_num

/-- The complete even half-defect jet through the septic coefficient. -/
theorem coeff_suzuki_evenHalfDefect_through_six (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (n : Fin 7) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    coeff n (halfDefectSeries l (a + b) -
      halfDefectSeries (l.map Neg.neg) (-(a + b))) =
        if n = 4 then (5 : ℝ) • suzukiQuinticTerm a b p else
          if n = 6 then (7 : ℝ) • suzukiDefectSepticTerm a b p else 0 := by
  dsimp only
  rw [map_sub, coeff_halfDefectSeries_neg, coeff_halfDefectSeries]
  have h0 := groupedConjCoeff_fiveStageStrang_even a b p hp 0
  have h2 := groupedConjCoeff_fiveStageStrang_even a b p hp 1
  have h4 := groupedConjCoeff_fiveStageStrang_even a b p hp 2
  norm_num only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Nat.reduceMul, Fin.reduceEq, ite_false, ite_true] at h0 h2 h4
  simp only [smul_add, neg_smul] at h0 h2 h4
  fin_cases n <;> norm_num [Fin.ext_iff, h0, h2, h4,
    suzukiDefectSepticTerm, smul_smul]
  all_goals module

/-- The complete centered polynomial is the actual seventh formal product coefficient. -/
theorem coeff_suzuki_centered_seven (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
    coeff 7 (exponentialCurve (-(1 / 2 : ℝ) • (a + b)) *
      (expListSeries l * expListSeries l.reverse) *
        exponentialCurve (-(1 / 2 : ℝ) • (a + b))) =
      suzukiCenteredSepticTerm a b p := by
  let l := List.ofFn (fiveStageStrangHalfGenerator a b p)
  let H := -(1 / 2 : ℝ) • (a + b) :: l
  let U := expListSeries H
  let V := expListSeries H.reverse
  let T := halfDefectSeries l (a + b) - halfDefectSeries (l.map Neg.neg) (-(a + b))
  let J := exponentialCurve (-(1 / 2 : ℝ) • (a + b)) *
    (expListSeries l * expListSeries l.reverse) *
      exponentialCurve (-(1 / 2 : ℝ) • (a + b))
  have hq : Algebra.restrictScalars ℚ ℝ A = (inferInstance : Algebra ℚ A) :=
    Subsingleton.elim _ _
  have hU0 : coeff 0 U = 1 := by simp [U, expListSeries]
  have hV0 : coeff 0 V = 1 := by simp [V, expListSeries]
  have hU1 : coeff 1 U = 0 := by
    have h := expListTerm_suzukiCenteredHalf_one a b p
    rw [hq] at h
    simpa only [U, H, l, coeff_expListSeries] using h
  have hU2 : coeff 2 U = suzukiHalfQuadraticTerm a b p := by
    have h := expListTerm_suzukiCenteredHalf_two a b p
    rw [hq] at h
    simpa only [U, H, l, coeff_expListSeries, suzukiHalfQuadraticTerm_eq] using h
  have hV1 : coeff 1 V = 0 := by
    simpa only [V, U, coeff_expListSeries, expListTerm_one, List.sum_reverse] using hU1
  have hV2 : coeff 2 V = -suzukiHalfQuadraticTerm a b p := by
    simpa only [V, ← hU2] using coeff_expListSeries_reverse_two_of_one_eq_zero H hU1
  have hTc (k : Fin 7) : coeff k T =
      if k = 4 then (5 : ℝ) • suzukiQuinticTerm a b p else
        if k = 6 then (7 : ℝ) • suzukiDefectSepticTerm a b p else 0 :=
    coeff_suzuki_evenHalfDefect_through_six a b p hp k
  have ht0 := hTc 0
  have ht1 := hTc 1
  have ht2 := hTc 2
  have ht3 := hTc 3
  have ht4 := hTc 4
  have ht5 := hTc 5
  have ht6 := hTc 6
  norm_num only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Fin.reduceEq, ite_false, ite_true] at ht0 ht1 ht2 ht3 ht4 ht5 ht6
  have hd : seriesDerivative J = U * T * V := by
    simpa only [J, U, V, H, expListSeries_cons_eq_exponentialCurve,
      List.reverse_cons, expListSeries_append, expListSeries_nil, mul_one, mul_assoc] using
        seriesDerivative_centered_expListSeries l (a + b)
  have hc := congrArg (coeff 6) hd
  norm_num only [coeff_seriesDerivative, ← Rat.cast_smul_eq_qsmul ℝ,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ, sum_range_zero, Nat.reduceSub,
    hU0, hU1, hU2, hV0, hV1, hV2,
    ht0, ht1, ht2, ht3, ht4, ht5, ht6,
    mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at hc
  apply (smul_right_injective A (by norm_num : (7 : ℝ) ≠ 0))
  change (7 : ℝ) • coeff 7 J = (7 : ℝ) • suzukiCenteredSepticTerm a b p
  rw [hc]
  simp only [suzukiCenteredSepticTerm, Ring.lie_def,
    smul_add, smul_smul, smul_mul_assoc, mul_smul_comm, mul_neg]
  module

/-- The centered and BCH septic coefficients differ by the midpoint double commutator. -/
theorem suzukiCenteredSepticTerm_eq_bch (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) :
    suzukiCenteredSepticTerm a b p = suzukiBchSepticTerm a b p +
      (1 / 24 : ℝ) • ⁅a + b, ⁅a + b, suzukiQuinticTerm a b p⁆⁆ := by
  rw [← coeff_suzuki_centered_seven a b p hp]
  have h := coeff_centered_expListSeries_seven_of_log_jet
    (List.ofFn (fiveStageStrangHalfGenerator a b p) ++
      (List.ofFn (fiveStageStrangHalfGenerator a b p)).reverse)
    (a + b) (suzukiQuinticTerm a b p) (suzukiBchSepticTerm a b p)
    (expListLogCoeff_suzukiHalf_through_seven a b p hp)
  simpa only [← expListSeries_append, ← Rat.cast_smul_eq_qsmul ℝ,
    Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div] using h

end FQFP.BCH
