/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.RealScalar
public import FQFP.Analysis.Normed.Algebra.ExponentialListSeries
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSeries
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiQuinticBounds

/-!
# The quintic Suzuki logarithm and its rational coefficient bound

The finite homogeneous logarithm identifies the quintic Suzuki coefficient under
cubic cancellation. The analytic tail has order six on the quarter-radius
coefficient domain, giving the source local existence statements for arbitrary
real cancellation parameters and the coefficient bound at the standard Suzuki value.

## Main results

* `norm_fiveStageStrangLog_sub_smul_sub_quintic_le_of_lt_quarter`: the explicit local remainder.
* `norm_fiveStageStrangLog_sub_smul_sub_quintic_le`: the source sixth-order local tail.
* `norm_fiveStageStrangLog_sub_smul_le`: the unit-weight commutator bound.
* `norm_fiveStageStrangLog_sub_smul_le_at_suzukiP`: the source rational coefficient bound.
-/

@[expose] public noncomputable section

open scoped RealScalar

open Finset NormedSpace

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] [NormOneClass A]

/-- The quintic Suzuki coefficient leaves a sixth-order tail on the quarter-radius domain. -/
theorem norm_fiveStageStrangLog_sub_smul_sub_quintic_le_of_lt_quarter (a b : A) (p t : ℝ)
    (hp : IsSuzukiCubic p) (h : fiveStageStrangArgNormBound a b p t < 1 / 4) :
    ‖fiveStageStrangLog a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ ≤
      320 * fiveStageStrangArgNormBound a b p t ^ 6 := by
  have htail := norm_log_prod_exp_sub_sum_le (fiveStageStrangArguments a b p t)
    (by rwa [sum_norm_fiveStageStrangArguments]) 6
  rw [sum_expListLogCoeff_fiveStageStrang_eq a b p t hp, sum_norm_fiveStageStrangArguments] at htail
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.reducePow] at htail
  simpa only [fiveStageStrangLog, fiveStageStrangProduct, sub_add_eq_sub_sub] using htail

/-- Under cubic cancellation the source quintic coefficient has a local sixth-order tail. -/
theorem norm_fiveStageStrangLog_sub_smul_sub_quintic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, ‖t‖ < δ →
      ‖fiveStageStrangLog a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ ≤
        K * ‖t‖ ^ 6 := by
  let C := fiveStageStrangArgNormBound a b p 1
  have hC : 0 ≤ C := fiveStageStrangArgNormBound_nonneg a b p 1
  have hC1 : 0 < C + 1 := by linarith only [hC]
  refine ⟨1 / (4 * (C + 1)), by positivity, 320 * C ^ 6, by positivity, ?_⟩
  intro t ht
  have hscale : fiveStageStrangArgNormBound a b p t = ‖t‖ * C := by
    simp [fiveStageStrangArgNormBound, C]
  have htC : ‖t‖ * (4 * (C + 1)) < 1 := (lt_div_iff₀ (by positivity)).mp ht
  have hsmall : fiveStageStrangArgNormBound a b p t < 1 / 4 := by
    rw [hscale]
    have ht0 := norm_nonneg t
    nlinarith only [htC, ht0]
  calc
    _ ≤ 320 * (‖t‖ * C) ^ 6 := by
      simpa only [hscale] using
        norm_fiveStageStrangLog_sub_smul_sub_quintic_le_of_lt_quarter a b p t hp hsmall
    _ = _ := by ring

/-- A norm bound on the quintic coefficient transfers to the local Suzuki logarithm error. -/
theorem norm_fiveStageStrangLog_sub_smul_le_of_quintic_bound (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (C : ℝ) (hC : ‖suzukiQuinticTerm a b p‖ ≤ C) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖fiveStageStrangLog a b p t - t • (a + b)‖ ≤ t ^ 5 * C + K * t ^ 6 := by
  obtain ⟨δ, hδ, K, hK, hbound⟩ := norm_fiveStageStrangLog_sub_smul_sub_quintic_le a b p hp
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht htd
  have hres := hbound t (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using htd)
  have hterm : ‖(t ^ 5) • suzukiQuinticTerm a b p‖ ≤ t ^ 5 * C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 5)]
    exact mul_le_mul_of_nonneg_left hC (pow_nonneg ht 5)
  calc
    _ ≤ ‖fiveStageStrangLog a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ +
        ‖t ^ 5 • suzukiQuinticTerm a b p‖ := norm_le_norm_sub_add _ _
    _ ≤ K * ‖t‖ ^ 6 + t ^ 5 * C := add_le_add hres hterm
    _ = _ := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht]
      ring

/-- Cubic cancellation gives the source quintic-magnitude bound with unit commutator weights. -/
theorem norm_fiveStageStrangLog_sub_smul_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖fiveStageStrangLog a b p t - t • (a + b)‖ ≤
        t ^ 5 * binaryQuinticCommutatorNormSum a b + K * t ^ 6 :=
  norm_fiveStageStrangLog_sub_smul_le_of_quintic_bound a b p hp (binaryQuinticCommutatorNormSum a b)
    (norm_suzukiQuinticTerm_le_binaryQuinticCommutatorNormSum a b p hp)

/-- The rational-coefficient quintic Suzuki bound at the standard real cancellation parameter. -/
theorem norm_fiveStageStrangLog_sub_smul_le_at_suzukiP (a b : A) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖fiveStageStrangLog a b suzukiP t - t • (a + b)‖ ≤
        t ^ 5 * (∑ i : Fin 8, suzukiQuinticCoeffUpperBound i *
          ‖binaryQuinticCommutator a b i‖) + K * t ^ 6 :=
  norm_fiveStageStrangLog_sub_smul_le_of_quintic_bound a b suzukiP isSuzukiCubic_suzukiP
    (∑ i : Fin 8, suzukiQuinticCoeffUpperBound i * ‖binaryQuinticCommutator a b i‖)
    (norm_suzukiQuinticTerm_suzukiP_le a b)

end FQFP.BCH
