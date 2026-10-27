/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.ExponentialList
public import FQFP.BCH.Analysis.ExponentialList
public import FQFP.BCH.Analysis.ExponentialProduct

/-!
# Homogeneous tails of finite exponential products

The sum of exponent-argument norms bounds the factorial Cauchy coefficients of
any finite ordered exponential product. Its logarithm admits a homogeneous
approximation of every order on the quarter-radius input ball.

## Main results

* `norm_expListTerm_le`: the scalar factorial coefficient majorant.
* `hasSum_expListTerm`: the coefficients sum to the ordered exponential product.
* `norm_prod_exp_sub_sum_le`: scalar exponential control of every product tail.
* `norm_log_prod_exp_sub_sum_le`: the uniform homogeneous logarithm tail bound.
-/

@[expose] public noncomputable section

open Finset Finset.Nat NormedSpace

namespace FQFP

/-- A finite sum of norms is nonnegative. -/
lemma list_sum_norm_nonneg {B : Type*} [SeminormedAddGroup B] (l : List B) :
    0 ≤ (l.map norm).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg a

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [NormOneClass A]

/-- Every list coefficient is bounded by the corresponding scalar exponential coefficient. -/
lemma norm_expListTerm_le (l : List A) (n : ℕ) :
    ‖expListTerm l n‖ ≤ (l.map norm).sum ^ n / Nat.factorial n := by
  induction l generalizing n with
  | nil => by_cases hn : n = 0 <;> simp [expListTerm, hn]
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, expListTerm]
      refine (norm_sum_le _ _).trans ?_
      rw [← factorial_convolution]
      exact sum_le_sum fun ij _ ↦ norm_mul_le_of_le (norm_exp_term_le a ij.1) (ih ij.2)

/-- Dropping the factorial gives a homogeneous power bound. -/
lemma norm_expListTerm_le_pow (l : List A) (n : ℕ) :
    ‖expListTerm l n‖ ≤ (l.map norm).sum ^ n := by
  have hf : (1 : ℝ) ≤ Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  exact (norm_expListTerm_le l n).trans (div_le_self (pow_nonneg (list_sum_norm_nonneg l) n) hf)

variable [CompleteSpace A]

/-- The factorial convolution coefficients sum to the ordered exponential product. -/
lemma hasSum_expListTerm (l : List A) :
    HasSum (expListTerm l) (l.map exp).prod := by
  induction l with
  | nil =>
      simpa only [expListTerm, List.map_nil, List.prod_nil] using
        (hasSum_ite_eq (0 : ℕ) (1 : A))
  | cons a l ih =>
      have ha : Summable fun i : ℕ ↦ ‖(Nat.factorial i : ℚ)⁻¹ • a ^ i‖ :=
        (Real.summable_pow_div_factorial ‖a‖).of_nonneg_of_le
          (fun _ ↦ norm_nonneg _) (norm_exp_term_le a)
      have hl : Summable fun i : ℕ ↦ ‖expListTerm l i‖ :=
        (Real.summable_pow_div_factorial ((l.map norm).sum)).of_nonneg_of_le
          (fun _ ↦ norm_nonneg _) (norm_expListTerm_le l)
      have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hl
      simp only [List.map_cons, List.prod_cons]
      change HasSum (fun n ↦ ∑ ij ∈ antidiagonal n,
        ((Nat.factorial ij.1 : ℚ)⁻¹ • a ^ ij.1) * expListTerm l ij.2) _
      rw [hs.of_norm.hasSum_iff]
      exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hl).symm.trans
        (by
          rw [ih.tsum_eq]
          simp only [exp_eq_tsum_rat])

/-- Every product tail is bounded by the corresponding real exponential tail. -/
lemma norm_prod_exp_sub_sum_le (l : List A) (n : ℕ) :
    ‖(l.map exp).prod - ∑ i ∈ range n, expListTerm l i‖ ≤
      Real.exp ((l.map norm).sum) -
        ∑ i ∈ range n, (l.map norm).sum ^ i / Nat.factorial i :=
  norm_sub_sum_le_real_exp_tail _ _ _ (hasSum_expListTerm l) (norm_expListTerm_le l) n

/-- Every tail of degree at least two is bounded by its scale power on the quarter ball. -/
lemma norm_prod_exp_sub_sum_le_pow (l : List A) (n : ℕ) (hn : 2 ≤ n)
    (hl : (l.map norm).sum < 1 / 4) :
    ‖(l.map exp).prod - ∑ i ∈ range n, expListTerm l i‖ ≤ (l.map norm).sum ^ n := by
  exact (norm_prod_exp_sub_sum_le l n).trans
    (real_exp_sub_sum_le_pow (list_sum_norm_nonneg l) (by linarith only [hl]) n hn)

/-- The positive product part has norm at most twice the total argument norm. -/
lemma norm_prod_exp_sub_one_le_two_mul (l : List A)
    (hl : (l.map norm).sum < 1 / 4) :
    ‖(l.map exp).prod - 1‖ ≤ 2 * (l.map norm).sum := by
  let s := (l.map norm).sum
  have hs : 0 ≤ s := list_sum_norm_nonneg l
  have ht := norm_prod_exp_sub_one_le l
  have he := real_exp_sub_one_sub_id_le_sq hs (show s ≤ 1 by linarith only [hl])
  have hs2 : s ^ 2 ≤ s := by nlinarith only [hs, hl]
  linarith only [ht, he, hs2]

/-- Every power of the positive product has the common homogeneous tail bound. -/
lemma norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (k n : ℕ) (hkn : k < n) :
    ‖((l.map exp).prod - 1) ^ k - positivePowerTrunc (expListTerm l) k n‖ ≤
      (2 : ℝ) ^ (n - 1) * (l.map norm).sum ^ n := by
  apply norm_pow_sub_positivePowerTrunc_le _ _ (list_sum_norm_nonneg l)
    (norm_prod_exp_sub_one_le_two_mul l hl) k n hkn
    (fun i _ _ ↦ norm_expListTerm_le_pow l i)
  intro j hj _
  have hsum : (∑ i ∈ range j, expListTerm l i) =
      1 + ∑ i ∈ range (j - 1), expListTerm l (i + 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by lia]
    rw [sum_range_succ', expListTerm_zero, add_comm]
  have h := norm_prod_exp_sub_sum_le_pow l j hj hl
  simpa only [hsum, sub_add_eq_sub_sub] using h

private lemma norm_logPartialSum_prod_exp_sub_sum_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖logPartialSum A n ((l.map exp).prod - 1) -
      ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n‖ ≤
      (n : ℝ) * 2 ^ (n - 1) * (l.map norm).sum ^ n := by
  have h := norm_logPartialSum_sub_sum_positivePowerTrunc_le_of_pow
    ((l.map exp).prod - 1) (expListTerm l) n
    (fun k hk ↦ norm_prod_exp_sub_one_pow_sub_positivePowerTrunc_le l hl k n hk)
  have hs := list_sum_norm_nonneg l
  exact h.trans (le_trans
    (mul_le_mul_of_nonneg_right (sum_norm_logCoeff_le n) (by positivity))
    (by rw [mul_assoc]))

/-- Every small finite exponential product has a uniform homogeneous logarithm approximation. -/
theorem norm_log_prod_exp_sub_sum_le (l : List A)
    (hl : (l.map norm).sum < 1 / 4) (n : ℕ) :
    ‖log ((l.map exp).prod) - ∑ d ∈ range n, expListLogCoeff l d‖ ≤
      ((n : ℝ) * 2 ^ (n - 1) + 2 ^ (n + 1)) * (l.map norm).sum ^ n := by
  rw [sum_expListLogCoeff]
  let s := (l.map norm).sum
  let y := (l.map exp).prod - 1
  have hs : 0 ≤ s := list_sum_norm_nonneg l
  have hy : ‖y‖ ≤ 2 * s := norm_prod_exp_sub_one_le_two_mul l hl
  have hden : 1 / 2 ≤ 1 - ‖y‖ := by linarith only [hy, hl]
  have hy1 : ‖y‖ < 1 := by linarith only [hy, hl]
  have htail : ‖log ((l.map exp).prod) - logPartialSum A n y‖ ≤
      2 ^ (n + 1) * s ^ n := by
    rw [show (l.map exp).prod = 1 + y by
      dsimp [y]
      abel]
    calc
      _ ≤ ‖y‖ ^ n * (1 - ‖y‖)⁻¹ := norm_log_one_add_sub_logPartialSum_le y n hy1
      _ ≤ (2 * s) ^ n * (2 : ℝ) := by
        apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg y) hy n) ?_
          (by positivity) (by positivity)
        simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
      _ = _ := by
        rw [mul_pow, pow_succ]
        ring
  have hfinite := norm_logPartialSum_prod_exp_sub_sum_le l hl n
  calc
    _ ≤ ‖log ((l.map exp).prod) - logPartialSum A n y‖ +
        ‖logPartialSum A n y -
          ∑ k ∈ range n, logCoeff k • positivePowerTrunc (expListTerm l) k n‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 ^ (n + 1) * s ^ n + (n : ℝ) * 2 ^ (n - 1) * s ^ n :=
      add_le_add htail hfinite
    _ = _ := by ring

end FQFP
