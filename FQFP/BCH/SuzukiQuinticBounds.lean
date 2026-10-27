/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.SuzukiTerms
public import FQFP.BCH.SuzukiParameter

/-!
# The quintic Suzuki coefficients in the Childs basis

The eight quadratic coefficient polynomials use the source projection with zero
coefficients at indices two and six. Their values at the standard Suzuki parameter
are bounded by the existing tight rational prefactors.

## Main definitions

* `suzukiQuinticCoeff`: the eight signed coefficient polynomials.
* `suzukiQuinticTerm`: their linear combination of the Childs commutators.

## Main results

* `abs_suzukiQuinticCoeff_suzukiP_le`: the tight componentwise bounds.
* `norm_suzukiQuinticTerm_suzukiP_le`: the tight weighted Childs norm bound.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP.BCH

/-- The source tight rational prefactors bound every coefficient at the standard parameter. -/
theorem abs_suzukiQuinticCoeff_suzukiP_le (i : Fin 8) :
    |suzukiQuinticCoeff suzukiP i| ≤ bchTightPrefactors i := by
  obtain ⟨hlo, hhi⟩ := suzukiP_mem_rational_interval
  fin_cases i <;> norm_num [suzukiQuinticCoeff, bchTightPrefactors]
  all_goals
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg suzukiP, sq_nonneg (suzukiP - 41449 / 100000),
        sq_nonneg (suzukiP - 41450 / 100000)]

section Norm

variable {K A : Type*} [NormedField K] [NormedRing A] [NormedAlgebra K A]

/-- Coefficient bounds give a weighted Childs norm bound for the quintic combination. -/
theorem norm_suzukiQuinticTerm_le_of_coeff_le (a b : A) (p : K) (c : Fin 8 → ℝ)
    (hc : ∀ i, ‖suzukiQuinticCoeff p i‖ ≤ c i) :
    ‖suzukiQuinticTerm a b p‖ ≤ ∑ i : Fin 8, c i * ‖childsComm a b i‖ := by
  unfold suzukiQuinticTerm
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ ?_)
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))

end Norm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The quintic coefficient at the standard parameter has the source tight Childs norm bound. -/
theorem norm_suzukiQuinticTerm_suzukiP_le (a b : A) :
    ‖suzukiQuinticTerm a b suzukiP‖ ≤
      ∑ i : Fin 8, bchTightPrefactors i * ‖childsComm a b i‖ :=
  norm_suzukiQuinticTerm_le_of_coeff_le a b suzukiP bchTightPrefactors
    (fun i ↦ by simpa only [Real.norm_eq_abs] using abs_suzukiQuinticCoeff_suzukiP_le i)

/-- Under real cubic cancellation, every signed quintic coefficient is bounded by one. -/
theorem abs_suzukiQuinticCoeff_le_one (p : ℝ) (hp : IsSuzukiCubic p) (i : Fin 8) :
    |suzukiQuinticCoeff p i| ≤ 1 := by
  rw [(isSuzukiCubic_iff_eq_suzukiP p).mp hp]
  exact (abs_suzukiQuinticCoeff_suzukiP_le i).trans (by
    fin_cases i <;> norm_num [bchTightPrefactors])

/-- Cubic cancellation gives the source unit-weight Childs norm bound. -/
theorem norm_suzukiQuinticTerm_le_bchFourFoldSum (a b : A) (p : ℝ)
    (hp : IsSuzukiCubic p) : ‖suzukiQuinticTerm a b p‖ ≤ bchFourFoldSum a b := by
  rw [(isSuzukiCubic_iff_eq_suzukiP p).mp hp]
  exact (norm_suzukiQuinticTerm_suzukiP_le a b).trans
    (bchTightPrefactors_sum_mul_norm_le_bchFourFoldSum a b)

end FQFP.BCH
