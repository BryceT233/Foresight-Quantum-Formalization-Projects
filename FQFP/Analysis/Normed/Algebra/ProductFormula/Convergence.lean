/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.Power
public import FQFP.Analysis.Normed.Algebra.ProductFormula.OneNormScaling

/-!
# Fixed-time convergence of exponential product formulas

An exponential growth bound on a single step gives uniform stability of its
powers at fixed time. A local error of order `p + 1` then gives a global error
of order `r⁻ᵖ` for arbitrary generators in a complete normed algebra.
-/

public section

open NormedSpace Asymptotics Filter
open scoped RealScalar Topology

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- Exponential growth and local order control the total error at any fixed signed time. -/
theorem isBigO_pow_sub_exp_of_local_error (S : ℝ → A) (H : A) {K : ℝ}
    (hgrowth : ∀ h, ‖S h‖ ≤ Real.exp (‖h‖ * K)) {p : ℕ}
    (hlocal : (fun h ↦ S h - exp (h • H)) =O[𝓝 0] (fun h ↦ h ^ (p + 1))) (t : ℝ) :
    (fun r : ℕ ↦ S (t / r) ^ r - exp (t • H)) =O[atTop] (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ p) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let M := max K ‖H‖
  have hM : 0 ≤ M := (norm_nonneg H).trans (le_max_right ..)
  obtain ⟨C, hC⟩ := (hlocal.comp_tendsto (tendsto_const_div_atTop_nhds_zero_nat t)).bound
  refine IsBigO.of_bound (Real.exp (‖t‖ * M) * C * ‖t‖ ^ (p + 1)) ?_
  filter_upwards [hC, eventually_ge_atTop 1] with r hstep hr
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let h := t / (r : ℝ)
  have hS : ‖S h‖ ≤ Real.exp (‖h‖ * M) :=
    (hgrowth h).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (le_max_left ..) (norm_nonneg h)))
  have hE : ‖exp (h • H)‖ ≤ Real.exp (‖h‖ * M) := by
    refine (FQFP.norm_exp_le _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (le_max_right ..) (norm_nonneg h)
  have hstable : Real.exp (‖h‖ * M) ^ (r - 1) ≤ Real.exp (‖t‖ * M) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    calc
      _ ≤ (r : ℝ) * (‖h‖ * M) := by
        gcongr
        exact Nat.sub_le ..
      _ = _ := by
        rw [show ‖h‖ = ‖t‖ / r by simp [h, norm_div]]
        field_simp
  change ‖S h - exp (h • H)‖ ≤ C * ‖h ^ (p + 1)‖ at hstep
  calc
    _ ≤ (r : ℝ) * Real.exp (‖h‖ * M) ^ (r - 1) * ‖S h - exp (h • H)‖ := by
      rw [exp_smul_eq_pow_of_div H t hr]
      exact FQFP.norm_pow_sub_pow_le_of_common_bound _ _ hS hE r
    _ ≤ (r : ℝ) * Real.exp (‖t‖ * M) * (C * ‖h ^ (p + 1)‖) := by gcongr
    _ = _ := by
      simp only [h, norm_pow, norm_div, norm_inv, Real.norm_natCast]
      rw [div_pow, pow_succ (r : ℝ), inv_pow]
      field_simp

/-- The native order condition gives a fixed-time global convergence rate for arbitrary
generators of a finite product formula. -/
theorem ProductFormulaData.IsOrderOf.isBigO_eval_pow_sub_exp {Υ Γ p : ℕ}
    {P : ProductFormulaData Υ Γ} {H : Fin Γ → A} (hP : P.IsOrderOf p H) (t : ℝ) :
    (fun r : ℕ ↦ P.eval H (t / r) ^ r - exp (t • ∑ i, H i)) =O[atTop]
      (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ p) := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  apply isBigO_pow_sub_exp_of_local_error (P.eval H) (∑ i, H i) (K := Υ * ∑ i, ‖H i‖)
  · intro h
    simpa only [Real.norm_eq_abs, mul_assoc] using norm_eval_le P H h
  · exact isBigO_norm_left.mp hP

/-- Positive approximation order implies convergence to the exact exponential at fixed time. -/
theorem ProductFormulaData.IsOrderOf.tendsto_eval_pow {Υ Γ p : ℕ}
    {P : ProductFormulaData Υ Γ} {H : Fin Γ → A} (hP : P.IsOrderOf p H) (hp : 0 < p) (t : ℝ) :
    Tendsto (fun r : ℕ ↦ P.eval H (t / r) ^ r) atTop (𝓝 (exp (t • ∑ i, H i))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply (hP.isBigO_eval_pow_sub_exp t).trans_tendsto
  simpa [hp.ne'] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow p

end TrotterError
