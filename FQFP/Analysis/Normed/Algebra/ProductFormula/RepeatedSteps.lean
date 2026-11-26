/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.Prefactor
public import FQFP.Analysis.Normed.Algebra.ProductFormula.Convergence
public import FQFP.Analysis.Normed.Algebra.ProductFormula.LowOrder

/-!
# Fixed-time error of repeated Lie–Trotter and Strang steps

The first- and second-order rates apply to any finite family of generators.
For skew-adjoint generators, telescoping preserves the local commutator constants.
-/

public section

namespace TrotterError

open NormedSpace LieAlgebra Asymptotics Filter
open scoped RealScalar

attribute [local instance] LieRing.ofAssociativeRing

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {Γ : ℕ}

/-- For arbitrary generators the repeated Lie–Trotter error is first order at fixed time. -/
theorem isBigO_lieTrotter_pow_sub_exp [NormedAlgebra ℚ A] [NormOneClass A]
    (H : Fin Γ → A) (t : ℝ) :
    (fun r : ℕ ↦ lieTrotter H (t / r) ^ r - exp (t • ∑ i, H i)) =O[atTop]
      (fun r : ℕ ↦ (r : ℝ)⁻¹) := by
  obtain rfl : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  simpa only [lieTrotter_eq_eval, pow_one] using
    (isOrderOf_lieTrotterData H).isBigO_eval_pow_sub_exp t

/-- For arbitrary generators the repeated Strang error is second order at fixed time. -/
theorem isBigO_suzuki2_pow_sub_exp [NormOneClass A] (H : Fin Γ → A) (t : ℝ) :
    (fun r : ℕ ↦ suzuki2 H (t / r) ^ r - exp (t • ∑ i, H i)) =O[atTop]
      (fun r : ℕ ↦ ((r : ℝ)⁻¹) ^ 2) := by
  simpa only [suzuki2_eq_eval] using (isOrderOf_suzuki2Data H).isBigO_eval_pow_sub_exp t

variable [StarRing A] [CStarRing A] [Nontrivial A] [StarModule ℝ A]

/-- The first-order commutator bound after any positive number of equal Lie–Trotter steps. -/
theorem norm_lieTrotter_pow_sub_exp_le [NormedAlgebra ℚ A] (K : Fin Γ → A)
    (hK : ∀ i, star (K i) = -K i)
    {t : ℝ} (ht : 0 ≤ t) {r : ℕ} (hr : 0 < r) :
    ‖lieTrotter K (t / r) ^ r - exp (t • ∑ i, K i)‖ ≤
      (t ^ 2 / 2) * (∑ i, ‖⁅upperSum K i, K i⁆‖) / r := by
  obtain rfl : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  calc
    _ ≤ (r : ℝ) * ‖lieTrotter K (t / r) - exp ((t / r) • ∑ i, K i)‖ := by
      simpa only [lieTrotter_eq_eval] using
        norm_eval_pow_sub_exp_le_of_skewAdjoint (lieTrotterData Γ) K hK t hr
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (firstOrder_bound Γ K hK (t / r) (div_nonneg ht (Nat.cast_nonneg r)))
      (Nat.cast_nonneg r)).trans_eq (by field_simp)

/-- The ordered exponential product satisfies the first-order bound for either sign of time. -/
theorem norm_ordered_exp_pow_sub_exp_le [NormedAlgebra ℚ A] (K : Fin Γ → A)
    (hK : ∀ i, star (K i) = -K i) (t : ℝ) {r : ℕ} (hr : 0 < r) :
    ‖((List.finRange Γ).reverse.map fun i => exp ((t / r) • K i)).prod ^ r -
      exp (t • ∑ i, K i)‖ ≤ (t ^ 2 / 2) * (∑ i, ‖⁅upperSum K i, K i⁆‖) / r := by
  obtain rfl : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  by_cases ht : 0 ≤ t
  · simpa only [← lieTrotter_eq_prod] using norm_lieTrotter_pow_sub_exp_le K hK ht hr
  · have hneg (i : Fin Γ) : star (-K i) = -(-K i) := by rw [star_neg, hK]
    have h := norm_lieTrotter_pow_sub_exp_le (fun i => -K i) hneg (t := -t) (by linarith) hr
    simpa only [lieTrotter_eq_prod, neg_div, neg_smul, smul_neg, neg_neg, upperSum,
      Finset.sum_neg_distrib, neg_lie, lie_neg, neg_sq] using h

/-- The repeated Strang bound retains the constants `1/12` and `1/24` of the two
double commutators and decreases quadratically with the step count. -/
theorem norm_suzuki2_pow_sub_exp_le (K : Fin Γ → A) (hK : ∀ i, star (K i) = -K i)
    {t : ℝ} (ht : 0 ≤ t) {r : ℕ} (hr : 0 < r) :
    ‖suzuki2 K (t / r) ^ r - exp (t • ∑ i, K i)‖ ≤
      ((t ^ 3 / 12) * (∑ i, ‖adPow (upperSum K i) 2 (K i)‖) +
        (t ^ 3 / 24) * (∑ i, ‖adPow (K i) 2 (upperSum K i)‖)) / (r : ℝ) ^ 2 := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hreal : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  have : letI := normedAlgebraReal A; StarModule ℝ A := by rw [hreal]; infer_instance
  have hstep := secondOrder_bound Γ K hK
  rw [hreal] at hstep
  calc
    _ ≤ (r : ℝ) * ‖suzuki2 K (t / r) - exp ((t / r) • ∑ i, K i)‖ := by
      simpa only [suzuki2_eq_eval] using
        norm_eval_pow_sub_exp_le_of_skewAdjoint (suzuki2Data Γ) K hK t hr
    _ ≤ _ := (mul_le_mul_of_nonneg_left
      (hstep (t / r) (div_nonneg ht (Nat.cast_nonneg r)))
      (Nat.cast_nonneg r)).trans_eq (by field_simp)

end TrotterError
