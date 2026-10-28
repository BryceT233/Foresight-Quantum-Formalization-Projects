/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Grönwall bounds for forced linear evolution

## Main results

* `gronwallBound_zero_le_mul_exp`: a division-free scalar budget for nonnegative growth.
* `ContinuousLinearMap.norm_le_gronwallBound_of_forced`: the forced linear estimate.
* `ContinuousLinearMap.norm_le_mul_exp_of_forced_zero_initial`: its zero-initial-data form.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

/-- A convenient zero-initial-data bound, also valid when the growth rate is zero. -/
lemma gronwallBound_zero_le_mul_exp (K ε t : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε t ≤ ε * t * Real.exp (K * t) := by
  by_cases hKzero : K = 0
  · simp [gronwallBound, hKzero]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    rw [gronwallBound_of_K_ne_0 hKzero]
    simp only [zero_mul, zero_add]
    have hexp : Real.exp (K * t) - 1 ≤ (K * t) * Real.exp (K * t) := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K * t)))
        (Real.exp_nonneg (K * t))
      rw [← Real.exp_add] at h
      simp only [neg_add_cancel, Real.exp_zero] at h
      nlinarith
    calc
      _ ≤ ε / K * ((K * t) * Real.exp (K * t)) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg hε hK)
      _ = ε * t * Real.exp (K * t) := by field_simp

namespace ContinuousLinearMap
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Grönwall's estimate for a bounded linear generator with additive forcing.
Only right derivatives on the half-open interval and continuity on its closure are needed. -/
lemma norm_le_gronwallBound_of_forced
    (A : V →L[ℝ] V) (E r : ℝ → V) (a b δ K ε : ℝ)
    (hE : ContinuousOn E (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ico a b, HasDerivWithinAt E (A (E s) + r s) (Set.Ici s) s)
    (hinit : ‖E a‖ ≤ δ) (hA : ‖A‖ ≤ K)
    (hr : ∀ s ∈ Set.Ico a b, ‖r s‖ ≤ ε) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖E t‖ ≤ gronwallBound δ K ε (t - a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le hE hode hinit _ t ht
  intro s hs
  calc
    ‖A (E s) + r s‖ ≤ ‖A (E s)‖ + ‖r s‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖E s‖ + ε := add_le_add (A.le_opNorm _) (hr s hs)
    _ ≤ K * ‖E s‖ + ε := add_le_add
      (mul_le_mul_of_nonneg_right hA (norm_nonneg (E s))) le_rfl

/-- A bound without division by the growth rate, for zero initial error. -/
lemma norm_le_mul_exp_of_forced_zero_initial
    (A : V →L[ℝ] V) (E r : ℝ → V) (a b K ε : ℝ)
    (hE : ContinuousOn E (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ico a b, HasDerivWithinAt E (A (E s) + r s) (Set.Ici s) s)
    (hinit : E a = 0) (hA : ‖A‖ ≤ K) (hε : 0 ≤ ε)
    (hr : ∀ s ∈ Set.Ico a b, ‖r s‖ ≤ ε) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖E t‖ ≤ ε * (t - a) * Real.exp (K * (t - a)) := by
  exact (A.norm_le_gronwallBound_of_forced E r a b 0 K ε hE hode
    (by simp [hinit]) hA hr t ht).trans
      (gronwallBound_zero_le_mul_exp K ε (t - a) ((norm_nonneg A).trans hA) hε)

end ContinuousLinearMap
