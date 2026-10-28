/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.ODE.TimeOrderedExp
public import FQFP.Analysis.Calculus.IteratedDeriv.Asymptotics
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Higher derivatives and comparison of time-ordered evolution

Smoothness and power-order comparison depend on evolution itself, not on product formulas.

## Main results

* `TrotterError.contDiff_timeOrderedExp_of_contDiff`.
* `TrotterError.iteratedDeriv_timeOrderedExp_succ`.
* `TrotterError.timeOrderedExp_iteratedDeriv_eq_iff`.
* `TrotterError.orderCond_exp_iff`.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open scoped Topology BigOperators ContDiff algebraMap

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- For smooth `H`, the solution `t ↦ exp_T(∫₀ᵗ H)` is smooth. -/
lemma contDiff_timeOrderedExp_of_contDiff [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun t => timeOrderedExp H 0 t) := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H 0 t
  have hcont : Continuous H := hH.continuous
  have hHasDeriv : ∀ t, HasDerivAt U (H t * U t) t := fun t =>
    timeOrderedExp_hasDerivAt H hcont 0 t
  have hU : ∀ n : ℕ, ContDiff ℝ n U := by
    intro n
    induction n with
    | zero => exact contDiff_zero.mpr (continuous_timeOrderedExp H hcont 0)
    | succ n ih =>
        have hHn : ContDiff ℝ n H := hH.of_le (mod_cast le_top)
        have hfn : ContDiff ℝ n (fun t => H t * U t) := hHn.mul ih
        have hspan : ContDiff ℝ n
            (fun t => (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸))
              (H t * U t)) :=
          (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸)).contDiff.comp hfn
        exact (contDiff_succ_iff_hasFDerivAt (f := U) (n := n)).mpr
          ⟨fun t => (ContinuousLinearMap.toSpanSingletonCLE : 𝔸 ≃L[ℝ] (ℝ →L[ℝ] 𝔸)) (H t * U t),
            hspan, fun t => (hHasDeriv t).hasFDerivAt⟩
  rwa [contDiff_infty]

/-- The recurrence for iterated derivatives of `t ↦ exp_T(∫₀ᵗ H)` at `0`: the `(j+1)`-st
iterated derivative is `iteratedDeriv j H 0` plus terms built from strictly lower derivatives of
`H` and lower iterated derivatives of the time-ordered exponential. -/
lemma iteratedDeriv_timeOrderedExp_succ [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (H : ℝ → 𝔸) (hH : ContDiff ℝ ∞ H) (j : ℕ) :
    iteratedDeriv (j + 1) (fun t => timeOrderedExp H 0 t) 0 =
      (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
        iteratedDeriv (j - i) (fun t => timeOrderedExp H 0 t) 0) + iteratedDeriv j H 0 := by
  let U : ℝ → 𝔸 := fun t => timeOrderedExp H 0 t
  have hU : ContDiff ℝ ∞ U := contDiff_timeOrderedExp_of_contDiff H hH
  have hderiv : deriv U = fun t => H t * U t := by
    funext t
    exact (timeOrderedExp_hasDerivAt H hH.continuous 0 t).deriv
  calc
    iteratedDeriv (j + 1) U 0
        = iteratedDeriv j (deriv U) 0 := by rw [iteratedDeriv_succ']
    _ = iteratedDeriv j (fun t => H t * U t) 0 := by rw [hderiv]
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0 := by
            change iteratedDeriv j (H * U) 0 =
              ∑ i ∈ Finset.range (j + 1), (j.choose i : 𝔸) * iteratedDeriv i H 0 *
                iteratedDeriv (j - i) U 0
            rw [iteratedDeriv_mul (hH.contDiffAt.of_le (mod_cast le_top))
              (hU.contDiffAt.of_le (mod_cast le_top))]
    _ = (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0) + (j.choose j : 𝔸) * iteratedDeriv j H 0 *
          iteratedDeriv 0 U 0 := by
            rw [Finset.sum_range_succ, Nat.sub_self]
    _ = (∑ i ∈ Finset.range j, (j.choose i : 𝔸) * iteratedDeriv i H 0 *
          iteratedDeriv (j - i) U 0) + iteratedDeriv j H 0 := by
            rw [Nat.choose_self]
            simp [U, timeOrderedExp_initial]

/-- The derivative-comparison heart of the exponentiation rule: the generators agree to order
`p - 1` (all iterated derivatives of order `< p` coincide at `0`) iff the associated time-ordered
exponentials agree to order `p` (all iterated derivatives of order `≤ p` coincide at `0`). -/
lemma timeOrderedExp_iteratedDeriv_eq_iff [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (F G : ℝ → 𝔸) (p : ℕ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (∀ j, j < p → iteratedDeriv j F 0 = iteratedDeriv j G 0) ↔
      (∀ j, j ≤ p → iteratedDeriv j (fun t => timeOrderedExp F 0 t) 0 =
        iteratedDeriv j (fun t => timeOrderedExp G 0 t) 0) := by
  by_cases hp : p = 0
  · subst p; constructor
    · intro _ j hj
      replace hj : j = 0 := by lia
      subst j; simp [timeOrderedExp_initial]
    · intros; contradiction
  · constructor
    · intro hD j hj
      induction j using Nat.strong_induction_on with
      | h j ih =>
        cases j with
        | zero => simp [timeOrderedExp_initial]
        | succ k =>
            have hk : k < p := Nat.lt_of_succ_le hj
            rw [iteratedDeriv_timeOrderedExp_succ F hF k,
              iteratedDeriv_timeOrderedExp_succ G hG k]
            apply congrArg₂ (fun x y => x + y)
            · apply Finset.sum_congr rfl
              intro i hi
              have hi_lt : i < k := Finset.mem_range.mp hi
              have hDF : iteratedDeriv i F 0 = iteratedDeriv i G 0 :=
                hD i (Nat.lt_trans hi_lt hk)
              have hDU : iteratedDeriv (k - i) (fun t => timeOrderedExp F 0 t) 0 =
                  iteratedDeriv (k - i) (fun t => timeOrderedExp G 0 t) 0 :=
                ih (k - i) (Nat.lt_of_le_of_lt (Nat.sub_le k i) (Nat.lt_succ_self k))
                  (Nat.le_trans (Nat.sub_le k i) (Nat.le_of_lt hk))
              rw [hDF, hDU]
            · exact hD k hk
    · intro hDU j hj
      induction j using Nat.strong_induction_on with
      | h j ih =>
        cases j with
        | zero =>
            have h1 : iteratedDeriv 1 (fun t => timeOrderedExp F 0 t) 0 =
                iteratedDeriv 1 (fun t => timeOrderedExp G 0 t) 0 :=
              hDU 1 (Nat.succ_le_iff.mpr hj)
            have hF1 : iteratedDeriv 1 (fun t => timeOrderedExp F 0 t) 0 = iteratedDeriv 0 F 0 := by
              simpa using iteratedDeriv_timeOrderedExp_succ F hF 0
            have hG1 : iteratedDeriv 1 (fun t => timeOrderedExp G 0 t) 0 = iteratedDeriv 0 G 0 := by
              simpa using iteratedDeriv_timeOrderedExp_succ G hG 0
            rwa [hF1, hG1] at h1
        | succ k =>
            have hfull : iteratedDeriv (k + 2) (fun t => timeOrderedExp F 0 t) 0 =
                iteratedDeriv (k + 2) (fun t => timeOrderedExp G 0 t) 0 := hDU (k + 2) (by lia)
            rw [iteratedDeriv_timeOrderedExp_succ F hF (k + 1),
              iteratedDeriv_timeOrderedExp_succ G hG (k + 1)] at hfull
            have hsum : (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i F 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp F 0 t) 0) =
                ∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi_le : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              have hDF : iteratedDeriv i F 0 = iteratedDeriv i G 0 :=
                ih i (Nat.lt_of_le_of_lt hi_le (Nat.lt_succ_self k))
                  (Nat.lt_of_le_of_lt hi_le (Nat.lt_of_succ_lt hj))
              have hDUi : iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp F 0 t) 0 =
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0 :=
                hDU (k + 1 - i) (Nat.le_trans (Nat.sub_le (k + 1) i) (Nat.le_of_lt hj))
              rw [hDF, hDUi]
            have hfull' : (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0) +
                    iteratedDeriv (k + 1) F 0 =
                (∑ i ∈ Finset.range (k + 1), ((k + 1).choose i : 𝔸) *
                  iteratedDeriv i G 0 *
                  iteratedDeriv (k + 1 - i) (fun t => timeOrderedExp G 0 t) 0) +
                    iteratedDeriv (k + 1) G 0 := by
              simpa [hsum] using hfull
            exact add_left_cancel hfull'

/-- Exponentiation rule (order.tex:84): `F = G + O(τ^p)` iff
`exp_T(∫₀ᵗ F) = exp_T(∫₀ᵗ G) + O(t^{p+1})`. -/
theorem orderCond_exp_iff [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (F G : ℝ → 𝔸) (p : ℕ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (fun τ => ‖F τ - G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      (fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖) =O[𝓝 (0 : ℝ)]
        (fun t => t ^ (p + 1)) := by
  let UF : ℝ → 𝔸 := fun t => timeOrderedExp F 0 t
  let UG : ℝ → 𝔸 := fun t => timeOrderedExp G 0 t
  have hUF : ContDiff ℝ ∞ UF := contDiff_timeOrderedExp_of_contDiff F hF
  have hUG : ContDiff ℝ ∞ UG := contDiff_timeOrderedExp_of_contDiff G hG
  have hdiff : ContDiff ℝ ∞ (UF - UG) := hUF.sub hUG
  have hcore := timeOrderedExp_iteratedDeriv_eq_iff F G p hF hG
  constructor
  · intro hbig
    have hD : ∀ j < p, iteratedDeriv j F 0 = iteratedDeriv j G 0 := by
      intro j hj
      have hzero : iteratedDeriv j (F - G) 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (F - G) p (hF.sub hG)).mp hbig j hj
      rw [iteratedDeriv_sub (hF.contDiffAt.of_le (mod_cast le_top))
        (hG.contDiffAt.of_le (mod_cast le_top))] at hzero
      exact sub_eq_zero.mp hzero
    have hDU : ∀ j ≤ p, iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := hcore.mp hD
    exact (isBigO_norm_iff_iteratedDeriv_eq_zero (UF - UG) p hdiff).mpr (fun j hj => by
      have heq : iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := hDU j hj
      rw [iteratedDeriv_sub (hUF.contDiffAt.of_le (mod_cast le_top))
        (hUG.contDiffAt.of_le (mod_cast le_top))]
      exact sub_eq_zero.mpr heq)
  · intro hbig
    have hDU : ∀ j ≤ p, iteratedDeriv j UF 0 = iteratedDeriv j UG 0 := by
      intro j hj
      have hzero : iteratedDeriv j (UF - UG) 0 = 0 :=
        (isBigO_norm_iff_iteratedDeriv_eq_zero (UF - UG) p hdiff).mp hbig j hj
      rw [iteratedDeriv_sub (hUF.contDiffAt.of_le (mod_cast le_top))
        (hUG.contDiffAt.of_le (mod_cast le_top))] at hzero
      exact sub_eq_zero.mp hzero
    have hD : ∀ j < p, iteratedDeriv j F 0 = iteratedDeriv j G 0 := hcore.mpr hDU
    exact (isBigO_norm_iff_iteratedDeriv_lt_eq_zero (F - G) p (hF.sub hG)).mpr (fun j hj => by
      rw [iteratedDeriv_sub (hF.contDiffAt.of_le (mod_cast le_top))
        (hG.contDiffAt.of_le (mod_cast le_top))]
      exact sub_eq_zero.mpr (hD j hj))

end TrotterError
