/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# Contractions and their finite products

Multiplication by a contraction preserves the norm when it has a contractive
inverse on the appropriate side. Ordered products of contractions also have a
quadratic remainder after subtracting their linear part.

## Main definitions

* `FQFP.contractionProduct`: partial products with later factors on the left.

## Main results

* `FQFP.norm_mul_eq_norm_right_of_mul_eq_one`: left multiplication by a contraction
  with a contractive left inverse preserves the norm.
* `FQFP.norm_contractionProduct_sub_one_le`: the linear telescoping bound.
* `FQFP.norm_contractionProduct_sub_one_sub_sum_le`: the quadratic remainder bound.
-/

@[expose] public section

open Finset

namespace FQFP

variable {A : Type*}

section Algebra

variable [NonAssocSemiring A]

/-- Ordered partial products, with later increments multiplying on the left. -/
def contractionProduct (D : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => (1 + D n) * contractionProduct D n

@[simp]
lemma contractionProduct_zero (D : ℕ → A) : contractionProduct D 0 = 1 := rfl

@[simp]
lemma contractionProduct_succ (D : ℕ → A) (n : ℕ) :
    contractionProduct D (n + 1) = (1 + D n) * contractionProduct D n := rfl

/-- A recursively specified product agrees with the ordered partial product. -/
lemma eq_contractionProduct_of_recurrence (D P : ℕ → A) (h0 : P 0 = 1)
    (hs : ∀ k, P (k + 1) = (1 + D k) * P k) (n : ℕ) :
    P n = contractionProduct D n := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs, ih, contractionProduct_succ]

end Algebra

variable [NormedRing A]

/-- Left multiplication by a contraction with a contractive left inverse preserves the norm. -/
lemma norm_mul_eq_norm_right_of_mul_eq_one {a b : A} (h : b * a = 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x : A) : ‖a * x‖ = ‖x‖ := by
  apply le_antisymm
  · simpa only [one_mul] using norm_mul_le_of_le ha (le_refl ‖x‖)
  · simpa only [← mul_assoc, h, one_mul] using norm_mul_le_of_le hb (le_refl ‖a * x‖)

/-- Right multiplication by a contraction with a contractive right inverse preserves the norm. -/
lemma norm_mul_eq_norm_left_of_mul_eq_one {a b : A} (h : a * b = 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x : A) : ‖x * a‖ = ‖x‖ :=
  norm_mul_eq_norm_right_of_mul_eq_one (congrArg MulOpposite.op h) ha hb (MulOpposite.op x)

/-- Two elements in the closed unit ball have distance at most two. -/
lemma norm_sub_le_two_of_le_one {E : Type*} [SeminormedAddCommGroup E] {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 2 :=
  (norm_sub_le x y).trans ((add_le_add hx hy).trans_eq (one_add_one_eq_two : (1 : ℝ) + 1 = 2))

/-- Telescoping bounds the distance of a product of contractions from the identity. -/
theorem norm_contractionProduct_sub_one_le (D : ℕ → A) {δ : ℝ}
    (hf : ∀ k, ‖1 + D k‖ ≤ 1) (hD : ∀ k, ‖D k‖ ≤ δ) (n : ℕ) :
    ‖contractionProduct D n - 1‖ ≤ (n : ℝ) * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(1 + D n) * (contractionProduct D n - 1) + D n‖ := by
        congr 1
        rw [contractionProduct_succ]
        noncomm_ring
      _ ≤ ‖(1 + D n) * (contractionProduct D n - 1)‖ + ‖D n‖ := norm_add_le _ _
      _ ≤ 1 * ((n : ℝ) * δ) + δ :=
        add_le_add (norm_mul_le_of_le (hf n) ih) (hD n)
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

/-- The nonlinear part of a finite contraction product is at most a quadratic binomial bound. -/
theorem norm_contractionProduct_sub_one_sub_sum_le (D : ℕ → A) {δ : ℝ}
    (hf : ∀ k, ‖1 + D k‖ ≤ 1) (hD : ∀ k, ‖D k‖ ≤ δ) (n : ℕ) :
    ‖contractionProduct D n - 1 - ∑ k ∈ range n, D k‖ ≤
      (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ‖(contractionProduct D n - 1 - ∑ k ∈ range n, D k) +
          D n * (contractionProduct D n - 1)‖ := by
        congr 1
        rw [contractionProduct_succ, sum_range_succ]
        noncomm_ring
      _ ≤ ‖contractionProduct D n - 1 - ∑ k ∈ range n, D k‖ +
          ‖D n * (contractionProduct D n - 1)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 + δ * ((n : ℝ) * δ) :=
        add_le_add ih (norm_mul_le_of_le (hD n)
          (norm_contractionProduct_sub_one_le D hf hD n))
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring

end FQFP
