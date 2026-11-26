/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.Convergence
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiLocalAsymptotics

/-!
# Fourth-order Suzuki convergence in a Banach algebra

The local quintic expansion and the exponential growth of the eleven-factor
product give a quartic rate at every fixed real time.
-/

public section

open NormedSpace Asymptotics Filter
open scoped RealScalar Topology

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

/-- Under cubic cancellation the repeated Suzuki product has fourth-order global error. -/
theorem isBigO_fiveStageStrangProduct_pow_sub_exp (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) (t : ℝ) :
    (fun r : ℕ ↦ fiveStageStrangProduct a b p (t / r) ^ r - exp (t • (a + b))) =O[atTop]
      (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 4) := by
  apply TrotterError.isBigO_pow_sub_exp_of_local_error _ _
    (K := fiveStageStrangArgNormBound a b p 1)
  · intro h
    have hprod := norm_le_norm_sub_add (fiveStageStrangProduct a b p h) 1
    have hbound := norm_fiveStageStrangProduct_sub_one_le a b p h
    rw [norm_one] at hprod
    simpa [fiveStageStrangArgNormBound] using (show
      ‖fiveStageStrangProduct a b p h‖ ≤ Real.exp (fiveStageStrangArgNormBound a b p h) by
        linarith only [hprod, hbound])
  · let L := suzukiQuinticTerm a b p
    have hterm : (fun h : ℝ ↦ h ^ 5 • L) =O[𝓝 0] (fun h ↦ h ^ 5) := by
      apply IsBigO.of_bound ‖L‖
      filter_upwards with h
      rw [norm_smul, mul_comm]
    let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
    have hlocal := isLittleO_fiveStageStrangProduct_sub_exp_sub_quintic a b p hp
    rw [show normedAlgebraReal A = ‹NormedAlgebra ℝ A› from Subsingleton.elim _ _] at hlocal
    simpa only [Pi.add_apply, L, sub_add_cancel] using hlocal.isBigO.add hterm

/-- Repeating the five-stage Suzuki formula at step size `t / r`
converges to the exact exponential for any real simulation time. -/
theorem tendsto_fiveStageStrangProduct_pow (a b : A) (p : ℝ) (hp : IsSuzukiCubic p) (t : ℝ) :
    Tendsto (fun r : ℕ ↦ fiveStageStrangProduct a b p (t / r) ^ r) atTop
      (𝓝 (exp (t • (a + b)))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply (isBigO_fiveStageStrangProduct_pow_sub_exp a b p hp t).trans_tendsto
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4

end FQFP.BCH
