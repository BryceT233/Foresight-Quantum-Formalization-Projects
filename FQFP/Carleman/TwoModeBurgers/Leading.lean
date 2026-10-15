/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Monomials

/-!
# Leading coefficients of two-mode Lie iterates

The coefficient recurrences in this file isolate the highest-degree terms
without expanding the full iterated polynomial.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

private lemma index_succ_zero (i j : ℕ) :
    Finsupp.single (0 : Fin 2) (i + 1) + Finsupp.single 1 j =
      Finsupp.single 0 1 +
        (Finsupp.single 0 i + Finsupp.single 1 j) := by
  ext k
  fin_cases k <;> simp [Nat.add_comm]

private lemma index_succ_one (i j : ℕ) :
    Finsupp.single (0 : Fin 2) i + Finsupp.single 1 (j + 1) =
      Finsupp.single 1 1 +
        (Finsupp.single 0 i + Finsupp.single 1 j) := by
  ext k
  fin_cases k <;> simp [Nat.add_comm]

private lemma coefficient_first_mul (p : MvPolynomial (Fin 2) ℝ) (i j : ℕ) :
    (X 0 * p).coeff (Finsupp.single 0 (i + 1) + Finsupp.single 1 j) =
      p.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  simp only [index_succ_zero, coeff_X_mul]

private lemma coefficient_second_mul (p : MvPolynomial (Fin 2) ℝ) (i j : ℕ) :
    (X 1 * p).coeff (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) =
      p.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  simp only [index_succ_one, coeff_X_mul]

private lemma coefficient_first_sq_mul_zero (p : MvPolynomial (Fin 2) ℝ) (j : ℕ) :
    (X 0 ^ 2 * p).coeff (Finsupp.single 0 1 + Finsupp.single 1 j) = 0 := by
  have h : ¬ Finsupp.single (0 : Fin 2) 2 ≤ (Finsupp.single 0 1 + Finsupp.single 1 j) := by
    intro hle
    have hzero := Finsupp.le_def.mp hle 0
    simp at hzero
  simp only [X_pow_eq_monomial, coeff_monomial_mul',
    h, ↓reduceIte]

private lemma coefficient_zero_first_mul (p : MvPolynomial (Fin 2) ℝ) (j : ℕ) :
    (X 0 * p).coeff (Finsupp.single 0 0 + Finsupp.single 1 j) = 0 := by
  simp [coeff_X_mul']

private lemma coefficient_zero_first_sq_mul (p : MvPolynomial (Fin 2) ℝ) (j : ℕ) :
    (X 0 ^ 2 * p).coeff (Finsupp.single 0 0 + Finsupp.single 1 j) = 0 := by
  rw [pow_two, mul_assoc, coefficient_zero_first_mul]

private lemma coefficient_first_sq_mul_two (p : MvPolynomial (Fin 2) ℝ) (j : ℕ) :
    (X 0 ^ 2 * p).coeff (Finsupp.single 0 2 + Finsupp.single 1 j) =
      p.coeff (Finsupp.single 0 0 + Finsupp.single 1 j) := by
  rw [pow_two, mul_assoc]
  simpa only [Nat.reduceAdd] using
    (coefficient_first_mul (X 0 * p) 1 j).trans (coefficient_first_mul p 0 j)

private lemma coefficient_pderiv_first (p : MvPolynomial (Fin 2) ℝ) (i j : ℕ) :
    (pderiv 0 p).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      (i + 1 : ℝ) * p.coeff (Finsupp.single 0 (i + 1) + Finsupp.single 1 j) := by
  simp only [coeff_pderiv]
  rw [add_comm (Finsupp.single 0 i + Finsupp.single 1 j) (Finsupp.single 0 1),
    ← index_succ_zero]
  simp
  ring

private lemma coefficient_pderiv_second (p : MvPolynomial (Fin 2) ℝ) (i j : ℕ) :
    (pderiv 1 p).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      (j + 1 : ℝ) * p.coeff (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) := by
  simp only [coeff_pderiv]
  rw [add_comm (Finsupp.single 0 i + Finsupp.single 1 j) (Finsupp.single 1 1),
    ← index_succ_one]
  simp
  ring

private lemma lieDerivation_eq_pderiv (α γ β : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    (mkDerivation ℝ (vectorField α γ β)) p =
      C (-α) * X 0 * pderiv 0 p + C β * X 0 * X 1 * pderiv 0 p +
        C (-γ) * X 1 * pderiv 1 p + C (-β) * X 0 ^ 2 * pderiv 1 p := by
  calc
    (mkDerivation ℝ (vectorField α γ β)) p =
        vectorField α γ β 0 * pderiv 0 p +
          vectorField α γ β 1 * pderiv 1 p := by
      rw [mkDerivation_eq_sum_pderiv]
      simp [Fin.sum_univ_two, Derivation.smul_apply, smul_eq_mul]
    _ = _ := by
      simp only [vectorField, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

/-- The `a b^(j+1)` coefficient obeys a triangular recurrence. -/
theorem coefficient_one_lieDerivation (α γ β : ℝ) (j : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) p).coeff
        (Finsupp.single 0 1 + Finsupp.single 1 (j + 1)) =
      -(α + γ * (j + 1 : ℝ)) *
          p.coeff (Finsupp.single 0 1 + Finsupp.single 1 (j + 1)) +
        β * p.coeff (Finsupp.single 0 1 + Finsupp.single 1 j) := by
  rw [lieDerivation_eq_pderiv]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_assoc, coeff_C_mul]
  rw [coefficient_first_mul, coefficient_first_mul, coefficient_second_mul,
    coefficient_second_mul, coefficient_first_sq_mul_zero,
    coefficient_pderiv_first, coefficient_pderiv_first, coefficient_pderiv_second]
  ring

/-- The `a² b^(j+1)` coefficient has two incoming nonlinear terms. -/
theorem coefficient_two_lieDerivation (α γ β : ℝ) (j : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) p).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (j + 1)) =
      -(2 * α + γ * (j + 1 : ℝ)) *
          p.coeff (Finsupp.single 0 2 + Finsupp.single 1 (j + 1)) +
        2 * β * p.coeff (Finsupp.single 0 2 + Finsupp.single 1 j) -
          β * (j + 2 : ℝ) * p.coeff (Finsupp.single 0 0 + Finsupp.single 1 (j + 2)) := by
  rw [lieDerivation_eq_pderiv]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_assoc, coeff_C_mul]
  simp only [coefficient_first_mul, coefficient_second_mul, coefficient_first_sq_mul_two,
    coefficient_pderiv_first, coefficient_pderiv_second]
  push_cast
  ring

/-- Pure powers of `b` only undergo the linear damping term. -/
theorem coefficient_zero_lieDerivation (α γ β : ℝ) (j : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) p).coeff
        (Finsupp.single 0 0 + Finsupp.single 1 (j + 1)) =
      -(γ * (j + 1 : ℝ)) *
        p.coeff (Finsupp.single 0 0 + Finsupp.single 1 (j + 1)) := by
  rw [lieDerivation_eq_pderiv]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_assoc, coeff_C_mul,
    coefficient_zero_first_mul, coefficient_zero_first_sq_mul]
  rw [coefficient_second_mul, coefficient_pderiv_second]
  ring

/-- Coefficients above the total degree vanish. -/
lemma coefficient_eq_zero_of_totalDegree_lt (p : MvPolynomial (Fin 2) ℝ) (i j : ℕ)
    (h : p.totalDegree < i + j) : p.coeff ((Finsupp.single 0 i + Finsupp.single 1 j)) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  simpa only [← Finsupp.degree_apply, map_add, Finsupp.degree_single] using h

/-- The coefficient of `a bⁿ` in the `n`th Lie derivative of `a` is `βⁿ`. -/
theorem coefficient_lieIterate_first (α γ β : ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n]) (X 0)).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 n) = β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coefficient_one_lieDerivation]
    have hdeg := (lieIterate_coordinate_totalDegree_le α γ β n).1
    have hzero : (((mkDerivation ℝ (vectorField α γ β))^[n]) (X 0)).coeff
        (Finsupp.single 0 1 + Finsupp.single 1 (n + 1)) = 0 :=
      coefficient_eq_zero_of_totalDegree_lt _ _ _ (by lia)
    rw [hzero, ih]
    simp [pow_succ, mul_comm]

/-- For nonzero coupling, the `n`th coordinate iterate has degree exactly `n + 1`. -/
theorem lieIterate_first_totalDegree (α γ β : ℝ) (hβ : β ≠ 0) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n]) (X 0)).totalDegree = n + 1 := by
  have hcoeff : (((mkDerivation ℝ (vectorField α γ β))^[n]) (X 0)).coeff
      (Finsupp.single 0 1 + Finsupp.single 1 n) ≠ 0 := by
    rw [coefficient_lieIterate_first]
    exact pow_ne_zero n hβ
  have hlow := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hhigh := (lieIterate_coordinate_totalDegree_le α γ β n).1
  simp [Finsupp.sum_fintype, Fin.sum_univ_two] at hlow
  lia

private lemma coefficient_lieDerivation_second_base (α γ β : ℝ) :
    ((mkDerivation ℝ (vectorField α γ β))
      (X 1)).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 0) = -β := by
  rw [mkDerivation_X]
  simp only [vectorField, Matrix.cons_val_one]
  simp [X_pow_eq_monomial]

private lemma coefficient_zero_lieIterate_second_high (α γ β : ℝ) (n k : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n]) (X 1)).coeff
      (Finsupp.single 0 0 + Finsupp.single 1 (k + 2)) = 0 := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    simp [coeff_X, Finsupp.ext_iff, Fin.forall_fin_two]
  | succ n ih =>
    rw [Function.iterate_succ_apply', show k + 2 = (k + 1) + 1 by lia,
      coefficient_zero_lieDerivation]
    simp only [show (k + 1) + 1 = k + 2 by lia, ih, mul_zero]

/-- The coefficient of `a² bⁿ` in the `(n+1)`st iterate of `b`. -/
theorem coefficient_lieIterate_second (α γ β : ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (X 1)).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 n) =
      -(2 ^ n * β ^ (n + 1)) := by
  induction n with
  | zero =>
    simpa using coefficient_lieDerivation_second_base α γ β
  | succ n ih =>
    rw [Function.iterate_succ_apply', coefficient_two_lieDerivation]
    have hdeg := (lieIterate_coordinate_totalDegree_le α γ β (n + 1)).2
    have hzero₁ : (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (X 1)).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (n + 1)) = 0 :=
      coefficient_eq_zero_of_totalDegree_lt _ _ _ (by lia)
    have hzero₂ : (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (X 1)).coeff
        (Finsupp.single 0 0 + Finsupp.single 1 (n + 2)) = 0 :=
      coefficient_zero_lieIterate_second_high α γ β (n + 1) n
    rw [hzero₁, hzero₂, ih]
    ring

/-- For nonzero coupling, the second coordinate iterates also have exact degree. -/
theorem lieIterate_second_totalDegree (α γ β : ℝ) (hβ : β ≠ 0) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (X 1)).totalDegree = n + 2 := by
  have hcoeff : (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (X 1)).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 n) ≠ 0 := by
    rw [coefficient_lieIterate_second]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero n (by norm_num))
      (pow_ne_zero (n + 1) hβ))
  have hlow := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hhigh := (lieIterate_coordinate_totalDegree_le α γ β (n + 1)).2
  have hlow' : 2 + n ≤
      (((mkDerivation ℝ (vectorField α γ β))^[n + 1])
        (X 1)).totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hlow
  lia

end TwoModeBurgers
