/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Ring.ContractionProduct
public import FQFP.Analysis.Normed.Algebra.ConjugationIntegral

/-!
# Interaction picture products

The exact interaction picture for a repeated splitting is an ordered product
of conjugated single-step increments. Finite contraction bounds retain the
operator sum as the leading term.

## Main definitions

* `TrotterError.interactionIncrement`: a transported single-step increment.

## Main results

* `TrotterError.interactionProduct_eq_contractionProduct`: the exact finite product.
* `TrotterError.norm_interactionProduct_sub_midpoint_le`: the discrete operator bound.
-/

@[expose] public noncomputable section

open NormedSpace Finset FQFP
open scoped RealScalar

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- A single-step error transported to the `k`-th interaction picture. -/
def interactionIncrement (G S : A) (h : ℝ) (k : ℕ) : A :=
  exp (-((k : ℝ) * h) • G) * (exp ((-h) • G) * S - 1) * exp (((k : ℝ) * h) • G)

/-- Adding the transported increment to the identity leaves a transported splitting factor. -/
lemma one_add_interactionIncrement (G S : A) (h : ℝ) (k : ℕ) :
    1 + interactionIncrement G S h k =
      exp (-(((k : ℝ) + 1) * h) • G) * S * exp (((k : ℝ) * h) • G) := by
  have hi : exp (-((k : ℝ) * h) • G) * exp (((k : ℝ) * h) • G) = 1 := by
    rw [exp_smul_mul_exp_smul]
    simp
  unfold interactionIncrement
  rw [mul_sub, sub_mul, mul_one, hi]
  rw [add_sub_cancel]
  rw [← mul_assoc, exp_smul_mul_exp_smul]
  rw [show -((k : ℝ) * h) + -h = -(((k : ℝ) + 1) * h) by ring]

/-- The interaction-picture splitting power is precisely the ordered finite product. -/
theorem interactionProduct_eq_contractionProduct (G S : A) (h : ℝ) (r : ℕ) :
    exp (-((r : ℝ) * h) • G) * S ^ r = contractionProduct (interactionIncrement G S h) r := by
  apply eq_contractionProduct_of_recurrence (interactionIncrement G S h)
    (fun k ↦ exp (-((k : ℝ) * h) • G) * S ^ k)
  · simp
  · intro k
    rw [one_add_interactionIncrement]
    simp only [Nat.cast_add, Nat.cast_one]
    have hi : exp (((k : ℝ) * h) • G) * exp (-((k : ℝ) * h) • G) = 1 := by
      rw [exp_smul_mul_exp_smul]
      simp
    rw [mul_assoc, mul_assoc, ← mul_assoc (exp (((k : ℝ) * h) • G)), hi, one_mul,
      ← mul_assoc, pow_succ', mul_assoc]

/-- Exponential norm bounds transfer the single-step norm to every transported increment. -/
lemma norm_interactionIncrement_eq (G S : A) (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1)
    (h : ℝ) (k : ℕ) :
    ‖interactionIncrement G S h k‖ = ‖S - exp (h • G)‖ := by
  unfold interactionIncrement
  rw [norm_mul_exp_smul_eq_of_le_one G _ hG, norm_exp_smul_mul_eq_of_le_one G _ hG]
  have hi : exp ((-h) • G) * exp (h • G) = 1 := by
    rw [exp_smul_mul_exp_smul]
    simp
  rw [show exp ((-h) • G) * S - 1 = exp ((-h) • G) * (S - exp (h • G)) by
    rw [mul_sub, hi]]
  exact norm_exp_smul_mul_eq_of_le_one G _ hG _

/-- A contraction splitting and two-sided exponential controls make every factor contractive. -/
lemma norm_one_add_interactionIncrement_le_one (G S : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1) (h : ℝ) (k : ℕ) :
    ‖1 + interactionIncrement G S h k‖ ≤ 1 := by
  rw [one_add_interactionIncrement, norm_mul_exp_smul_eq_of_le_one G _ hG,
    norm_exp_smul_mul_eq_of_le_one G _ hG]
  exact hS

/-- The centered single-step error transported to a midpoint is the interaction increment. -/
lemma interactionIncrement_eq_midpoint_conj (G S : A) (h : ℝ) (k : ℕ) :
    interactionIncrement G S h k =
      expSMulConj (-G)
        (exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G))
        (((k : ℝ) + 1 / 2) * h) := by
  have hleft : -(((k : ℝ) + 1 / 2) * h) + -h / 2 = -(((k : ℝ) + 1) * h) := by ring
  have hright : -h / 2 + ((k : ℝ) + 1 / 2) * h = (k : ℝ) * h := by ring
  have hcenter : exp ((-h / 2) • G) * exp (h • G) * exp ((-h / 2) • G) = 1 := by
    rw [exp_smul_mul_exp_smul, exp_smul_mul_exp_smul]
    rw [show -h / 2 + h + -h / 2 = 0 by ring]
    simp
  apply add_left_cancel (a := (1 : A))
  rw [one_add_interactionIncrement]
  simp only [expSMulConj, smul_neg, ← neg_smul, neg_neg]
  rw [mul_sub, sub_mul, hcenter, mul_sub, sub_mul, mul_one]
  rw [show exp (-(((k : ℝ) + 1 / 2) * h) • G) *
      exp ((((k : ℝ) + 1 / 2) * h) • G) = 1 by
    rw [exp_smul_mul_exp_smul]
    simp]
  rw [add_sub_cancel]
  simp only [← mul_assoc]
  rw [exp_smul_mul_exp_smul, hleft]
  rw [mul_assoc _ S, mul_assoc _ (exp ((-h / 2) • G)), exp_smul_mul_exp_smul, hright, mul_assoc]

/-- A centered local estimate transports unchanged to each interaction increment. -/
theorem norm_interactionIncrement_sub_midpoint_le (G S L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (h : ℝ) {η : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ η) (k : ℕ) :
    ‖interactionIncrement G S h k -
      h ^ 5 • expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h)‖ ≤ η := by
  rw [interactionIncrement_eq_midpoint_conj]
  have heq : ∀ X Y : A, ∀ c t : ℝ,
      expSMulConj (-G) X t - c • expSMulConj (-G) Y t =
        expSMulConj (-G) (X - c • Y) t := by
    intro X Y c t
    change (expSMulConjLin (-G) t) X - c • (expSMulConjLin (-G) t) Y =
      (expSMulConjLin (-G) t) (X - c • Y)
    rw [map_sub, map_smul]
  rw [heq]
  exact (norm_expSMulConj_eq_of_le_one (-G) _ (fun t ↦ by
    simpa only [smul_neg, ← neg_smul] using hG (-t)) _).le.trans hlocal

/-- **Discrete operator remainder.** Finite contraction products retain the full midpoint
operator sum, with a quadratic rather than exponential accumulation remainder. -/
theorem norm_interactionProduct_sub_midpoint_le (G S L : A)
    (hG : ∀ t : ℝ, ‖exp (t • G)‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (h : ℝ) {η δ : ℝ}
    (hlocal : ‖exp ((-h / 2) • G) * (S - exp (h • G)) * exp ((-h / 2) • G) -
      h ^ 5 • L‖ ≤ η)
    (hδ : ‖S - exp (h • G)‖ ≤ δ) (r : ℕ) :
    ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
      h ^ 4 • midpointConjugationIntegral G L r h‖ ≤
        (r : ℝ) * η + (r : ℝ) * ((r : ℝ) - 1) / 2 * δ ^ 2 := by
  have hsum : h ^ 4 • midpointConjugationIntegral G L r h =
      ∑ k ∈ range r, h ^ 5 • expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h) := by
    rw [midpointConjugationIntegral, smul_smul, ← pow_succ, smul_sum]
  have hrem := norm_contractionProduct_sub_one_sub_sum_le
    (interactionIncrement G S h)
    (norm_one_add_interactionIncrement_le_one G S hG hS h)
    (fun k ↦ (norm_interactionIncrement_eq G S hG h k).le.trans hδ) r
  rw [← interactionProduct_eq_contractionProduct G S h r] at hrem
  rw [hsum]
  calc
    _ = ‖(exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
          ∑ k ∈ range r, interactionIncrement G S h k) +
        ∑ k ∈ range r, (interactionIncrement G S h k -
          h ^ 5 • expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h))‖ := by
      rw [sum_sub_distrib]
      congr 1
      abel
    _ ≤ ‖exp (-((r : ℝ) * h) • G) * S ^ r - 1 -
          ∑ k ∈ range r, interactionIncrement G S h k‖ +
        ‖∑ k ∈ range r, (interactionIncrement G S h k -
          h ^ 5 • expSMulConj (-G) L (((k : ℝ) + 1 / 2) * h))‖ := norm_add_le _ _
    _ ≤ (r : ℝ) * ((r : ℝ) - 1) / 2 * δ ^ 2 + ∑ _k ∈ range r, η := by
      apply add_le_add hrem
      exact (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦
        norm_interactionIncrement_sub_midpoint_le G S L hG h hlocal k)
    _ = _ := by
      simp
      ring

end TrotterError
