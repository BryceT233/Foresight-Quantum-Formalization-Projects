/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Analysis.ExponentialListSeries
public import FQFP.BCH.SuzukiSeries
public import FQFP.BCH.SuzukiQuinticBounds

/-!
# The quintic Suzuki logarithm and its tight Childs bound

The finite homogeneous logarithm identifies the quintic Childs coefficient under
cubic cancellation. The analytic tail has order six on the quarter-radius
coefficient domain, giving the source local existence statements for arbitrary
real cancellation parameters and the tight bound at the standard Suzuki value.

## Main results

* `norm_suzuki5Bch_sub_smul_sub_quintic_le_of_lt_quarter`: the explicit local remainder.
* `norm_suzuki5Bch_sub_smul_sub_quintic_le`: the source sixth-order local tail.
* `suzuki5_log_product_quintic_of_IsSuzukiCubic`: the unit-weight Childs bound.
* `suzuki5_log_product_quintic_tight_at_suzukiP`: the source tight Childs bound.
-/

@[expose] public noncomputable section

open Finset NormedSpace

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- The quintic Suzuki coefficient leaves a sixth-order tail on the quarter-radius domain. -/
theorem norm_suzuki5Bch_sub_smul_sub_quintic_le_of_lt_quarter (a b : A) (p t : ℝ)
    (hp : IsSuzukiCubic p) (h : suzuki5ArgNormBound a b p t < 1 / 4) :
    ‖suzuki5Bch a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ ≤
      320 * suzuki5ArgNormBound a b p t ^ 6 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have htail := norm_log_prod_exp_sub_sum_le (suzuki5Arguments a b p t)
    (by rwa [sum_norm_suzuki5Arguments]) 6
  rw [sum_expListLogCoeff_suzuki5_eq a b p t hp, sum_norm_suzuki5Arguments] at htail
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.reducePow] at htail
  simpa only [suzuki5Bch, suzuki5Product, sub_add_eq_sub_sub] using htail

/-- Under cubic cancellation the source quintic coefficient has a local sixth-order tail. -/
theorem norm_suzuki5Bch_sub_smul_sub_quintic_le (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, ‖t‖ < δ →
      ‖suzuki5Bch a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ ≤
        K * ‖t‖ ^ 6 := by
  let C := suzuki5ArgNormBound a b p 1
  have hC : 0 ≤ C := suzuki5ArgNormBound_nonneg a b p 1
  have hC1 : 0 < C + 1 := by linarith only [hC]
  refine ⟨1 / (4 * (C + 1)), by positivity, 320 * C ^ 6, by positivity, ?_⟩
  intro t ht
  have hscale : suzuki5ArgNormBound a b p t = ‖t‖ * C := by
    simp [suzuki5ArgNormBound, C]
  have htC : ‖t‖ * (4 * (C + 1)) < 1 := (lt_div_iff₀ (by positivity)).mp ht
  have hsmall : suzuki5ArgNormBound a b p t < 1 / 4 := by
    rw [hscale]
    have ht0 := norm_nonneg t
    nlinarith only [htC, ht0]
  calc
    _ ≤ 320 * (‖t‖ * C) ^ 6 := by
      simpa only [hscale] using
        norm_suzuki5Bch_sub_smul_sub_quintic_le_of_lt_quarter a b p t hp hsmall
    _ = _ := by ring

/-- A norm bound on the quintic coefficient transfers to the local Suzuki logarithm error. -/
theorem norm_suzuki5Bch_sub_smul_le_of_quintic_bound (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (C : ℝ) (hC : ‖suzukiQuinticTerm a b p‖ ≤ C) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖suzuki5Bch a b p t - t • (a + b)‖ ≤ t ^ 5 * C + K * t ^ 6 := by
  obtain ⟨δ, hδ, K, hK, hbound⟩ := norm_suzuki5Bch_sub_smul_sub_quintic_le a b p hp
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht htd
  have hres := hbound t (by simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using htd)
  have hterm : ‖(t ^ 5) • suzukiQuinticTerm a b p‖ ≤ t ^ 5 * C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht 5)]
    exact mul_le_mul_of_nonneg_left hC (pow_nonneg ht 5)
  calc
    _ ≤ ‖suzuki5Bch a b p t - t • (a + b) - t ^ 5 • suzukiQuinticTerm a b p‖ +
        ‖t ^ 5 • suzukiQuinticTerm a b p‖ := norm_le_norm_sub_add _ _
    _ ≤ K * ‖t‖ ^ 6 + t ^ 5 * C := add_le_add hres hterm
    _ = _ := by
      rw [Real.norm_eq_abs, abs_of_nonneg ht]
      ring

/-- Cubic cancellation gives the source quintic-magnitude bound with unit Childs weights. -/
theorem suzuki5_log_product_quintic_of_IsSuzukiCubic (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖suzuki5Bch a b p t - t • (a + b)‖ ≤ t ^ 5 * bchFourFoldSum a b + K * t ^ 6 :=
  norm_suzuki5Bch_sub_smul_le_of_quintic_bound a b p hp (bchFourFoldSum a b)
    (norm_suzukiQuinticTerm_le_bchFourFoldSum a b p hp)

/-- **The tight quintic Suzuki bound** at the standard real cancellation parameter. -/
theorem suzuki5_log_product_quintic_tight_at_suzukiP (a b : A) :
    ∃ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ t : ℝ, 0 ≤ t → t < δ →
      ‖suzuki5Bch a b suzukiP t - t • (a + b)‖ ≤
        t ^ 5 * (∑ i : Fin 8, bchTightPrefactors i * ‖childsComm a b i‖) + K * t ^ 6 :=
  norm_suzuki5Bch_sub_smul_le_of_quintic_bound a b suzukiP isSuzukiCubic_suzukiP
    (∑ i : Fin 8, bchTightPrefactors i * ‖childsComm a b i‖)
    (norm_suzukiQuinticTerm_suzukiP_le a b)

end FQFP.BCH
