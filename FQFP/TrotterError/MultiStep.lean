/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.MainTheorem
public import FQFP.BCH.RealScalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit multi-step Trotter error and sufficient step counts

For anti-Hermitian summands, the single-step commutator bound and the telescoping
estimate give an explicit bound proportional to `αComm p H * t^(p+1) / r^p`.
Taking a real `p`-th root and rounding up gives a sufficient positive integer step
count for any accuracy `ε > 0`. This makes the parameter dependence in
`cor:trotter_number_comm_scaling` of *A Theory of Trotter Error* explicit.

The order condition is an input: this file does not prove the order of a particular
product-formula construction.

Real scalar multiplication uses the canonical extension from the complete normed `ℚ`-algebra
(`open scoped RealScalar`). No separate real-algebra structure is required.
-/

@[expose] public section

namespace TrotterError

open NormedSpace ProductFormulaData
open scoped BigOperators RealScalar

variable {Υ Γ : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
variable [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-- Explicit commutator-scaling error bound after any positive number of equal steps. -/
theorem trotter_error_bound_comm_scaling_pow
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) {r : ℕ} (hr : 0 < r) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤
      (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
        αComm p H * t ^ (p + 1) / (r : ℝ) ^ p := by
  let C := 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H
  have hstep := trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp
    h_order hΥ (t / (r : ℝ)) (div_nonneg ht (Nat.cast_nonneg r))
  calc
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖
        ≤ (r : ℝ) * ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • ∑ γ, H γ)‖ :=
          norm_eval_pow_sub_exp_le_of_skewAdjoint P H h_skew t hr
    _ ≤ (r : ℝ) * (C * (t / (r : ℝ)) ^ (p + 1)) :=
          mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg r)
    _ = C * t ^ (p + 1) / (r : ℝ) ^ p := by
          rw [mul_left_comm (r : ℝ) C, natCast_mul_pow_div_pow_succ t r p (by positivity)]
          simp only [div_eq_mul_inv, mul_assoc]

/-- A real `p`-th root of the explicit commutator bound gives a sufficient step threshold
for accuracy `ε`. The dependence on the summands, time, stages, and accuracy is explicit. -/
theorem trotter_error_le_of_comm_scaling_rpow_le
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) {r : ℕ} (hr : 0 < r)
    (hsteps : ((2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
      αComm p H * t ^ (p + 1) / ε) ^ (1 / (p : ℝ)) ≤ (r : ℝ)) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤ ε := by
  let D := (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) * αComm p H * t ^ (p + 1)
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (by positivity) (αComm_nonneg p H)) (pow_nonneg ht _)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by lia)
  have hpow : D / ε ≤ (r : ℝ) ^ p := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_inv_le_iff_of_pos (div_nonneg hD hε.le) (Nat.cast_nonneg r) hp').mp
      (by simpa only [one_div] using hsteps)
  refine (trotter_error_bound_comm_scaling_pow P H h_skew p hp h_order hΥ t ht hr).trans ?_
  change D / (r : ℝ) ^ p ≤ ε
  apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) ^ p)).mpr
  simpa only [mul_comm] using (div_le_iff₀ hε).mp hpow

/-- Rounding the real threshold up and taking at least one step ensures accuracy `ε`.
Every larger integer step count also works, including when `t = 0` or `αComm p H = 0`. -/
theorem trotter_error_le_of_comm_scaling_ceil_le
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) {r : ℕ}
    (hsteps : max 1 ⌈((2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
      αComm p H * t ^ (p + 1) / ε) ^ (1 / (p : ℝ))⌉₊ ≤ r) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤ ε := by
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hsteps)
  apply trotter_error_le_of_comm_scaling_rpow_le P H h_skew p hp h_order hΥ t ht ε hε hr
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hsteps)

end TrotterError
