/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.RealScalar
public import FQFP.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Differentiation and integration of vanishing orders

Smooth power bounds are equivalent to vanishing derivatives and transform under integration.

## Main results

* `TrotterError.isBigO_norm_iff_iteratedDeriv_lt_eq_zero`.
* `TrotterError.orderCond_deriv_iff`.
* `TrotterError.contDiff_integral_of_contDiff`.
* `TrotterError.orderCond_integral_iff`.
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open NormedSpace Asymptotics Finset
open scoped Topology BigOperators ContDiff algebraMap

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- `lem:order_cond_deriv` in the `O(τ^p)` form: a smooth `F` satisfies `F = O(τ^p)` iff all its
iterated derivatives of order `< p` vanish at `0`. For `p = 0` both sides hold automatically. -/
lemma isBigO_norm_iff_iteratedDeriv_lt_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      ∀ j : ℕ, j < p → iteratedDeriv j F 0 = 0 := by
  by_cases hp : p = 0
  · subst p
    constructor
    · intro _ j hj
      exact (Nat.not_lt_zero j hj).elim
    · intro _
      exact (hF.continuous.norm.continuousAt).isBigO_one (F := ℝ)
  · have hsub : (p - 1) + 1 = p := Nat.sub_add_cancel (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hp))
    constructor
    · intro hbig
      have hmain : ∀ j ≤ p - 1, iteratedDeriv j F 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_eq_zero F (p - 1) hF).mp (by
          simpa [hsub] using hbig)
      intro j hj
      exact hmain j (Nat.lt_succ_iff.mp (by simpa [hsub] using hj))
    · intro h
      simpa [hsub] using
        (isBigO_norm_iff_iteratedDeriv_eq_zero F (p - 1) hF).mpr (fun j hj =>
          h j (by simpa [hsub] using (Nat.lt_succ_iff.mpr hj)))

/-- Differentiation rule (order.tex:82): `F = O(τ^{p+1})` iff `F 0 = 0` and `F' = O(τ^p)`. -/
theorem orderCond_deriv_iff [NormedAlgebra ℝ 𝔸]
    (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ (p + 1)) ↔
      F 0 = 0 ∧ (fun τ => ‖deriv F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  have hFderiv : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  constructor
  · intro hbig
    have hvan : ∀ j ≤ p, iteratedDeriv j F 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF).mp hbig
    refine ⟨?_, ?_⟩
    · simpa using hvan 0 (Nat.zero_le p)
    · exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (deriv F) p hFderiv).mpr
        (fun j hj => by
          simpa [iteratedDeriv_succ'] using hvan (j + 1) (Nat.succ_le_iff.mpr hj))
  · rintro ⟨hF0, hderiv_big⟩
    have hderiv_van : ∀ j < p, iteratedDeriv j (deriv F) 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (deriv F) p hFderiv).mp hderiv_big
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero F p hF).mpr (fun j hj => by
      cases j with
      | zero => simpa using hF0
      | succ k => simpa [iteratedDeriv_succ'] using hderiv_van k (by lia))

/-- For smooth `F`, the function `t ↦ ∫₀ᵗ F` is smooth. -/
lemma contDiff_integral_of_contDiff
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (F : ℝ → 𝔸) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun t => ∫ τ in 0..t, F τ) := by
  let IF : ℝ → 𝔸 := fun t => ∫ τ in 0..t, F τ
  have hcont : Continuous F := hF.continuous
  have hHasDeriv : ∀ t, HasDerivAt IF (F t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hderiv : deriv IF = F := by
    funext t
    exact (hHasDeriv t).deriv
  have hdiff : Differentiable ℝ IF := fun t => (hHasDeriv t).differentiableAt
  exact (contDiff_infty_iff_deriv (f := IF)).mpr ⟨hdiff, by simpa [hderiv] using hF⟩

/-- Integration rule (order.tex:83): `F = O(τ^p)` iff `∫₀ᵗ F = O(t^{p+1})`. -/
theorem orderCond_integral_iff
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] (F : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) :
    (fun τ => ‖F τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      (fun t => ‖∫ τ in 0..t, F τ‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1)) := by
  let IF : ℝ → 𝔸 := fun t => ∫ τ in 0..t, F τ
  have hIF : ContDiff ℝ ∞ IF := contDiff_integral_of_contDiff F hF
  have hderiv : deriv IF = F := by
    funext t
    exact intervalIntegral.deriv_integral_right (hF.continuous.intervalIntegrable 0 t)
      hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
  have hiter : ∀ j, iteratedDeriv (j + 1) IF 0 = iteratedDeriv j F 0 := by
    intro j
    rw [iteratedDeriv_succ', hderiv]
  constructor
  · intro hFbig
    have hvan : ∀ j < p, iteratedDeriv j F 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_lt_eq_zero F p hF).mp hFbig
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero IF p hIF).mpr (fun j hj => by
      cases j with
      | zero => simp [IF]
      | succ k =>
          have hk : k < p := Nat.lt_of_succ_le hj
          rw [hiter k]
          exact hvan k hk)
  · intro hIFbig
    have hvan : ∀ j ≤ p, iteratedDeriv j IF 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_eq_zero IF p hIF).mp hIFbig
    exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero F p hF).mpr (fun j hj => by
      have hle : j + 1 ≤ p := Nat.succ_le_iff.mpr hj
      simpa [hiter j] using hvan (j + 1) hle)

end TrotterError
