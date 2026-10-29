/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.InteractionPicture
public import FQFP.Analysis.Normed.Algebra.ProductFormula.QuinticGlobalAsymptotics

/-!
# Global operator errors retaining quintic cancellation

The finite interaction product and midpoint quadrature combine to give the
continuous operator remainder, retaining the complete integral as its main term.

## Main results

* `norm_interactionProduct_sub_integral_le`: the global operator bound.
* `norm_pow_sub_exp_eq_interaction`: equality of the two error norms.
* `two_sided_norm_of_norm_sub_le`: the corresponding scalar enclosure.
-/

@[expose] public noncomputable section

open NormedSpace TrotterError
open scoped RealScalar

namespace FQFP

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Global operator remainder.** Centered local control and the original
local norm bound imply the continuous cancellation estimate at every step size. -/
theorem norm_interactionProduct_sub_integral_le (G S L : A) (C alpha : ℝ)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (h : ℝ) (hh : 0 ≤ h)
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ quinticCenteredRemainder ‖L‖ C alpha h)
    (hstep : ‖S - exp (h • G)‖ ≤ h ^ 5 * ‖L‖ + h ^ 7 * C) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
      h ^ 4 • conjugationIntegral G L ((r : ℝ) * h)‖ ≤
        quinticGlobalRemainder ‖L‖ C alpha ‖⁅G, ⁅G, L⁆⁆‖ ((r : ℝ) * h) h r := by
  have hcap : ‖S - exp (h • G)‖ ≤ quinticStepBound ‖L‖ C h := by
    apply le_min _ hstep
    exact (norm_sub_le S _).trans (by linarith [hG h])
  have hd := norm_interactionProduct_sub_midpoint_le G S L hG hS h hlocal hcap r
  have hq := norm_midpointConjugationIntegral_sub_conjugationIntegral_le G L hG r h hh
  rw [quinticGlobalRemainder_eq _ _ _ _ _ _ _ rfl]
  calc
    _ = ‖(exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
          h ^ 4 • midpointConjugationIntegral G L r h) +
        h ^ 4 • (midpointConjugationIntegral G L r h -
          conjugationIntegral G L ((r : ℝ) * h))‖ := by
      congr 1
      module
    _ ≤ ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
          h ^ 4 • midpointConjugationIntegral G L r h‖ +
        ‖h ^ 4 • (midpointConjugationIntegral G L r h -
          conjugationIntegral G L ((r : ℝ) * h))‖ := norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add hd
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh 4)]
      exact mul_le_mul_of_nonneg_left hq (pow_nonneg hh 4)

/-- Multiplication by the inverse exact evolution identifies the physical
global error norm with the interaction-picture error norm. -/
theorem norm_pow_sub_exp_eq_interaction (G S : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (t : ℝ) (r : ℕ) :
    ‖S ^ r - exp (t • G)‖ = ‖exp ((-t) • G) * S ^ r - 1‖ := by
  rw [← norm_exp_smul_mul_eq_of_le_one G (S ^ r - exp (t • G)) hG (-t), mul_sub,
    TrotterError.exp_smul_mul_exp_smul]
  simp

end FQFP

namespace FQFP

variable {E : Type*} [NormedAddCommGroup E]

/-- An operator remainder bounds the norm from both sides. -/
theorem two_sided_norm_of_norm_sub_le (x y : E) {R : ℝ} (h : ‖x - y‖ ≤ R) :
    max 0 (‖y‖ - R) ≤ ‖x‖ ∧ ‖x‖ ≤ ‖y‖ + R := by
  constructor
  · apply max_le (norm_nonneg _)
    have hy := norm_sub_norm_le y x
    rw [norm_sub_rev] at hy
    linarith
  · linarith [norm_sub_norm_le x y]

end FQFP
