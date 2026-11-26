/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ExponentialListTaylor
public import FQFP.Analysis.Normed.Algebra.ProductFormula.Basic
public import FQFP.Analysis.Calculus.Taylor
public import FQFP.RingTheory.PowerSeries.Noncommutative.Palindromic

/-!
# Lie–Trotter and Strang order conditions

The linear coefficient of an exponential product is the sum of its arguments.
For Strang splitting, reflection symmetry also determines the quadratic coefficient.
-/

public section

open NormedSpace FQFP
open scoped ContDiff RealScalar

namespace TrotterError

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {Υ Γ : ℕ} {P : ProductFormulaData Υ Γ}

/-- Taylor coefficient agreement through degree `p` certifies the native order condition. -/
theorem isOrderOf_of_expListTerm [NormedAlgebra ℚ A] (H : Fin Γ → A) (l : List A) (p : ℕ)
    (heval : ∀ t, P.eval H t = (l.map fun x ↦ exp (t • x)).prod)
    (hcoeff : ∀ k ≤ p, expListTerm l k = (k.factorial : ℚ)⁻¹ • (∑ i, H i) ^ k) :
    P.IsOrderOf p H := by
  obtain rfl : normedAlgebraReal A = ‹NormedAlgebra ℝ A› := Subsingleton.elim _ _
  unfold ProductFormulaData.IsOrderOf
  simp_rw [heval]
  refine (isBigO_norm_iff_iteratedDeriv_eq_zero _ p ((contDiff_prod_exp_smul l).sub
    (contDiff_exp_smul_const (∑ i, H i)))).mpr ?_
  intro k hk
  rw [iteratedDeriv_fun_sub
    ((contDiff_prod_exp_smul l).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_exp_smul_const (∑ i, H i)).contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedDeriv_prod_exp_smul_zero, iteratedDeriv_exp_smul_const, hcoeff k hk]
  simp [← Rat.cast_smul_eq_qsmul ℝ, smul_smul, Nat.factorial_ne_zero]

/-- Lie–Trotter splitting has order one for any finite family of generators. -/
theorem isOrderOf_lieTrotterData (H : Fin Γ → A) : (lieTrotterData Γ).IsOrderOf 1 H := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let l := (List.finRange Γ).reverse.map H
  apply isOrderOf_of_expListTerm H l
  · intro t
    rw [lieTrotterData_eval_eq]
    simp [l, List.map_map, Function.comp_def]
  · intro k hk
    interval_cases k <;> simp [l, List.map_reverse, List.finRange, List.sum_ofFn]

/-- Strang splitting has order two for any finite family of generators. -/
theorem isOrderOf_suzuki2Data (H : Fin Γ → A) : (suzuki2Data Γ).IsOrderOf 2 H := by
  let : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let half := (List.finRange Γ).map fun i ↦ (2 : ℝ)⁻¹ • H i
  let l := half ++ half.reverse
  have hsum : l.sum = ∑ i, H i := by
    simp only [l, List.sum_append, List.sum_reverse, half, List.finRange, List.map_ofFn,
      Function.comp_def, List.sum_ofFn, ← Finset.smul_sum, ← add_smul]
    norm_num
  apply isOrderOf_of_expListTerm H l
  · intro t
    rw [← suzuki2_eq_eval, suzuki2_eq_prod]
    simp [l, half, List.map_map, List.map_reverse, Function.comp_def, smul_smul, div_eq_mul_inv]
  · intro k hk
    have hrev : l.reverse = l := by simp [l]
    interval_cases k <;> simp [expListTerm_two_of_reverse_eq l hrev, hsum, Nat.factorial]

end TrotterError
