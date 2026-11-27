/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.RealScalar
public import FQFP.Analysis.ODE.TimeOrderedExpDeriv
public import FQFP.Analysis.Normed.Algebra.InverseAsymptotics
public import FQFP.Analysis.SpecialFunctions.Integrals.Monomial
public import FQFP.Analysis.Calculus.IteratedDeriv.Polynomial
public import FQFP.Analysis.Calculus.IteratedDeriv.Asymptotics
public import FQFP.Analysis.Asymptotics.Pow
public import FQFP.Analysis.Normed.Algebra.ProductFormula.Basic
public import FQFP.Analysis.Normed.Algebra.ExponentialCalculus
public import FQFP.Analysis.ODE.TimeOrderedExp
public import FQFP.Analysis.Normed.Algebra.ProductFormula.ErrorTypes

import FQFP.Analysis.Calculus.ListProd

/-!
# Product-formula error order conditions

Additive, exponentiated and multiplicative error conditions are equivalent to approximation order.
The general power-order, Taylor and evolution calculus is supplied by independent modules.

## Main results

* `errorOrderCond_iff`: equivalence of the three error order conditions.
* `eval_sub_exp_eq_exp_mul_integral`: the additive-error factorization.
-/

@[expose] public section

open scoped RealScalar

namespace TrotterError

open Asymptotics
open TrotterError.List
open ProductFormulaData
open scoped Topology ContDiff algebraMap

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-! ### The error order condition (`thm:error_order_cond`) -/

section ErrorOrderCond

open NormedSpace

private theorem isTheta_exp_mul [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] {S : ℝ → 𝔸}
    (hS : Continuous S) (F : ℝ → 𝔸) :
    (fun t => exp (S t) * F t) =Θ[𝓝 (0 : ℝ)] F :=
  isTheta_mul_left_of_continuousAt_isUnit F
    (NormedSpace.exp_continuous.comp hS).continuousAt (isUnit_exp (S 0))

/-- Every value of the product formula `𝒮(τ)` is a unit (a product of unit exponentials). -/
lemma isUnit_eval [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (τ : ℝ) :
    IsUnit (P.eval H τ) := by
  unfold ProductFormulaData.eval
  induction evalIndexList Υ Γ with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (isUnit_exp (τ • P.generator H i)).mul ih

/-- The additive error, factored: `𝒮(t) − e^{tH} = e^{tH} ∫₀ᵗ e^{−τH} 𝒮(τ) 𝒯(τ) dτ`. -/
lemma eval_sub_exp_eq_exp_mul_integral [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (t : ℝ) :
    P.eval H t - exp (t • ∑ γ, H γ) =
      exp (t • ∑ γ, H γ) * ∫ τ in 0..t,
        (exp ((-τ) • ∑ γ, H γ) * P.eval H τ) * additiveKernel P H τ := by
  have hsub : P.eval H t - exp (t • ∑ γ, H γ) =
      ∫ τ in 0..t, exp ((t - τ) • ∑ γ, H γ) * P.eval H τ * additiveKernel P H τ := by
    rw [errorType_additive P H t, add_sub_cancel_left]
  have hfactor : ∀ τ, exp ((t - τ) • ∑ γ, H γ) =
      exp (t • ∑ γ, H γ) * exp ((-τ) • ∑ γ, H γ) := by
    intro τ
    rw [exp_smul_mul_exp_smul, sub_eq_add_neg]
  simp_rw [hsub, hfactor, mul_assoc]
  exact integral_mul_left (exp (t • ∑ γ, H γ))
    (fun τ => exp ((-τ) • ∑ γ, H γ) * (P.eval H τ * additiveKernel P H τ))
    (by fun_prop) 0 t

/-- `thm:error_order_cond`, additive part: the additive-kernel order condition `𝒯 = O(τ^p)` is
equivalent to the `p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})`. -/
lemma errorOrderCond_additive_iff [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (p : ℕ) (H : Fin Γ → 𝔸) :
    P.IsOrderOf p H ↔
      (fun τ => ‖additiveKernel P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  let K : ℝ → 𝔸 := fun τ => exp ((-τ) • ∑ γ, H γ) * (P.eval H τ * additiveKernel P H τ)
  have hK_contDiff : ContDiff ℝ ∞ K :=
    ((contDiff_exp_smul_const (∑ γ, H γ)).comp contDiff_neg).mul
      ((contDiff_eval P H).mul (contDiff_additiveKernel P H))
  have hIntegral := isTheta_exp_mul (S := fun t => t • ∑ γ, H γ) (by fun_prop)
    (fun t => ∫ τ in 0..t, K τ)
  have hEval := isTheta_mul_left_of_continuousAt_isUnit (x := (0 : ℝ)) (additiveKernel P H)
    (continuous_eval P H).continuousAt (by simp only [ProductFormulaData.eval_zero, isUnit_one])
  have hK : K =Θ[𝓝 (0 : ℝ)] additiveKernel P H :=
    (isTheta_exp_mul (S := fun t => (-t) • ∑ γ, H γ) (by fun_prop) _).trans hEval
  simp_rw [ProductFormulaData.IsOrderOf, eval_sub_exp_eq_exp_mul_integral, mul_assoc]
  change (fun t => ‖exp (t • ∑ γ, H γ) * ∫ τ in 0..t, K τ‖) =O[𝓝 (0 : ℝ)]
    (fun t => t ^ (p + 1)) ↔ _
  rw [hIntegral.norm_left.norm_right.isBigO_congr_left, ← orderCond_integral_iff K p hK_contDiff]
  exact hK.norm_left.norm_right.isBigO_congr_left

/-- `thm:error_order_cond`, exponentiated part: the exponentiated-error order condition
`ℰ = O(τ^p)` is equivalent to the `p`-th order condition. -/
lemma errorOrderCond_exponentiated_iff [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (p : ℕ) (H : Fin Γ → 𝔸) :
    P.IsOrderOf p H ↔
      (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
  let F : ℝ → 𝔸 := fun τ => (∑ γ, H γ) + exponentiatedError P H τ
  let G : ℝ → 𝔸 := fun _ => ∑ γ, H γ
  have hF : ContDiff ℝ ∞ F := contDiff_const.add (contDiff_exponentiatedError P H)
  have hG : ContDiff ℝ ∞ G := contDiff_const
  have hiff := orderCond_exp_iff F G p hF hG
  have h1 : P.IsOrderOf p H ↔
      (fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖) =O[𝓝 (0 : ℝ)]
        (fun t => t ^ (p + 1)) := by
    have hfun : (fun t => ‖P.eval H t - exp (t • ∑ γ, H γ)‖) =
        fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖ := by
      funext t
      have heval : P.eval H t = timeOrderedExp F 0 t := by
        simpa [F] using errorType_exponentiated P H t
      have hexp : exp (t • ∑ γ, H γ) = timeOrderedExp G 0 t := by
        simpa [G] using (timeOrderedExp_const (∑ γ, H γ) 0 t).symm
      rw [heval, hexp]
    simp [ProductFormulaData.IsOrderOf, hfun]
  have h3 : (fun τ => ‖F τ - G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) ↔
      (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := by
    have hfun : (fun τ => ‖F τ - G τ‖) = fun τ => ‖exponentiatedError P H τ‖ := by
      funext τ
      exact congrArg (norm : 𝔸 → ℝ) (by
        dsimp [F, G]
        abel)
    simp [hfun]
  calc
    P.IsOrderOf p H ↔
        (fun t => ‖timeOrderedExp F 0 t - timeOrderedExp G 0 t‖) =O[𝓝 (0 : ℝ)]
          (fun t => t ^ (p + 1)) := h1
    _ ↔ (fun τ => ‖F τ - G τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := hiff.symm
    _ ↔ (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p) := h3

/-- `thm:error_order_cond`, multiplicative part: the multiplicative-error order condition
`ℳ = O(t^{p+1})` is equivalent to the `p`-th order condition. -/
lemma errorOrderCond_multiplicative_iff [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (p : ℕ) (H : Fin Γ → 𝔸) :
    P.IsOrderOf p H ↔
      (fun t => ‖multiplicativeError P H t‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1)) := by
  have hmul : ∀ t, P.eval H t - exp (t • ∑ γ, H γ) =
      exp (t • ∑ γ, H γ) * multiplicativeError P H t := by
    intro t
    rw [errorType_multiplicative P H t, mul_add, mul_one, add_sub_cancel_left]
  simp_rw [ProductFormulaData.IsOrderOf, hmul]
  exact (isTheta_exp_mul (S := fun t => t • ∑ γ, H γ) (by fun_prop)
    (multiplicativeError P H)).norm_left.norm_right.isBigO_congr_left

/-- `thm:error_order_cond` (order.tex:124): the additive (`𝒯 = O(τ^p)`), exponentiated
(`ℰ = O(τ^p)`), and multiplicative (`ℳ = O(t^{p+1})`) order conditions are all equivalent to the
`p`-th order condition `𝒮(t) = e^{tH} + O(t^{p+1})`. -/
theorem errorOrderCond_iff [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (p : ℕ) (H : Fin Γ → 𝔸) :
    List.TFAE [P.IsOrderOf p H,
      (fun τ => ‖additiveKernel P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p),
      (fun τ => ‖exponentiatedError P H τ‖) =O[𝓝 (0 : ℝ)] (fun τ => τ ^ p),
      (fun t => ‖multiplicativeError P H t‖) =O[𝓝 (0 : ℝ)] (fun t => t ^ (p + 1))] := by
  tfae_have 1 ↔ 2 := errorOrderCond_additive_iff P p H
  tfae_have 1 ↔ 3 := errorOrderCond_exponentiated_iff P p H
  tfae_have 1 ↔ 4 := errorOrderCond_multiplicative_iff P p H
  tfae_finish

end ErrorOrderCond

end TrotterError
