/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.Commutator

/-!
# Nonnegative weights of binary commutator norm sums

Normalize the innermost two letters of a binary nested commutator to `[Y,X]`,
and group the remaining letters by their word. Equal innermost letters vanish.
The weights are finite sums of absolute scalar factors and multinomial weights;
they are remainder-bound weights, rather than BCH coefficients.

## Main definitions

* `binaryCommutatorWord`: right-nested commutators indexed from outside to inside.
* `binaryConjugationWordWeight`: nonnegative weights obtained from multiplicity vectors.

## Main results

* `αCommConj_eq_sum_binaryWordWeight`: exact regrouping of the original norm sum.
-/

@[expose] public noncomputable section

open Finset

namespace TrotterError

attribute [local instance] LieRing.ofAssociativeRing

/-- The word `w` lists its adjoint operators from outermost to innermost. -/
def binaryCommutatorWord {A : Type*} [Ring A] {p : ℕ} (H : Fin 2 → A)
    (w : Fin p → Fin 2) : A :=
  nestedCommOfList ⁅H 1, H 0⁆ (List.ofFn (fun i ↦ H (w (Fin.rev i))))

/-- Nested commutators of a zero seed vanish. -/
lemma nestedCommOfList_zero {A : Type*} [Ring A] (l : List A) :
    nestedCommOfList 0 l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      change nestedCommOfList ⁅a, 0⁆ l = 0
      simpa only [lie_zero] using ih

/-- Negating the seed negates the resulting nested commutator. -/
lemma nestedCommOfList_neg {A : Type*} [Ring A] (B : A) (l : List A) :
    nestedCommOfList (-B) l = -nestedCommOfList B l := by
  induction l generalizing B with
  | nil => rfl
  | cons a l ih =>
      change nestedCommOfList ⁅a, -B⁆ l = -nestedCommOfList ⁅a, B⁆ l
      rw [lie_neg, ih]

/-- The first two tuple entries form the seed bracket, with the remaining entries as adjoints. -/
lemma nestedComm_eq_nestedCommOfList_pair {A : Type*} [Ring A] {p : ℕ}
    (γ : Fin (p + 2) → A) :
    nestedComm γ = nestedCommOfList ⁅γ 1, γ 0⁆
      (List.ofFn (fun i : Fin p ↦ γ i.succ.succ)) := by
  induction p with
  | zero => simp [nestedComm, nestedCommOfList]
  | succ p ih =>
      rw [nestedComm, ih, List.ofFn_succ', List.concat_eq_append,
        nestedCommOfList_append]
      rfl

/-- Orienting a binary innermost bracket changes at most its sign. -/
lemma norm_nestedCommOfList_binary_pair {A : Type*} [NormedRing A]
    (H : Fin 2 → A) (a b : Fin 2) (l : List A) :
    ‖nestedCommOfList ⁅H a, H b⁆ l‖ =
      if a = b then 0 else ‖nestedCommOfList ⁅H 1, H 0⁆ l‖ := by
  fin_cases a <;> fin_cases b
  · simp [lie_self, nestedCommOfList_zero]
  · change ‖nestedCommOfList ⁅H 0, H 1⁆ l‖ = _
    rw [show ⁅H 0, H 1⁆ = -⁅H 1, H 0⁆ from (lie_skew _ _).symm]
    rw [nestedCommOfList_neg, norm_neg]
    simp
  · simp
  · simp [lie_self, nestedCommOfList_zero]

/-- The outside-to-inside word obtained by dropping the two innermost tuple entries. -/
def binaryOuterWord {p : ℕ} (γ : Fin (p + 2) → Fin 2) : Fin p → Fin 2 :=
  fun i ↦ γ (Fin.rev i).succ.succ

/-- A binary nested-commutator norm is either zero or the norm of its normalized word. -/
lemma norm_nestedComm_binary {A : Type*} [NormedRing A] {p : ℕ}
    (H : Fin 2 → A) (γ : Fin (p + 2) → Fin 2) :
    ‖nestedComm (H ∘ γ)‖ =
      if γ 1 = γ 0 then 0 else ‖binaryCommutatorWord H (binaryOuterWord γ)‖ := by
  rw [nestedComm_eq_nestedCommOfList_pair]
  simp only [Function.comp_apply]
  rw [norm_nestedCommOfList_binary_pair]
  simp only [binaryCommutatorWord, binaryOuterWord, Fin.rev_rev]

/-- The expanded binary tuple of an antidiagonal multiplicity vector, including its seed. -/
def binaryMultiplicityTuple {s p : ℕ} (labels : Fin s → Fin 2) (seed : Fin 2)
    (q : ↥(finAntidiagonal s (p + 1))) : Fin (p + 2) → Fin 2 :=
  expandTuple labels q.1 seed ∘
    Fin.cast (congrArg (· + 1) (mem_finAntidiagonal.mp q.2).symm)

/-- Multiplicities expand to the tuple with the prescribed binary labels. -/
lemma adSequence_binary_eq_nestedComm {A : Type*} [Ring A] [Algebra ℝ A]
    {s p : ℕ} (H : Fin 2 → A) (labels : Fin s → Fin 2) (seed : Fin 2)
    (q : ↥(finAntidiagonal s (p + 1))) :
    adSequence (H ∘ labels) q.1 (H seed) =
      nestedComm (H ∘ binaryMultiplicityTuple labels seed q) := by
  rw [adSequence_eq_nestedComm_expandTuple, expandTuple_nat]
  exact (nestedComm_cast (mem_finAntidiagonal.mp q.2).symm
    (H ∘ expandTuple labels q.1 seed)).symm

/-- A nonnegative remainder weight: scalar absolute values are summed over all
multiplicity vectors producing the chosen outside-to-inside word. -/
def binaryConjugationWordWeight {s p : ℕ} (labels : Fin s → Fin 2)
    (c : Fin s → ℝ) (seed : Fin 2) (d : ℝ) (w : Fin p → Fin 2) : ℝ :=
  ∑ q : ↥(finAntidiagonal s (p + 1)),
    if (binaryMultiplicityTuple labels seed q) 1 ≠ (binaryMultiplicityTuple labels seed q) 0 ∧
        binaryOuterWord (binaryMultiplicityTuple labels seed q) = w then
      (Nat.multinomial (univ : Finset (Fin s)) q.1 : ℝ) * |d| *
        ∏ i, |c i| ^ q.1 i
    else 0

/-- Every binary remainder weight is nonnegative. -/
lemma binaryConjugationWordWeight_nonneg {s p : ℕ} (labels : Fin s → Fin 2)
    (c : Fin s → ℝ) (seed : Fin 2) (d : ℝ) (w : Fin p → Fin 2) :
    0 ≤ binaryConjugationWordWeight labels c seed d w := by
  unfold binaryConjugationWordWeight
  positivity

/-- Expanding one scalar-weighted binary commutator and orienting its innermost bracket. -/
lemma norm_adSequence_binary_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {s p : ℕ} (H : Fin 2 → A) (labels : Fin s → Fin 2) (c : Fin s → ℝ)
    (seed : Fin 2) (d : ℝ) (q : ↥(finAntidiagonal s (p + 1))) :
    ‖adSequence (fun i ↦ c i • H (labels i)) q.1 (d • H seed)‖ =
      |d| * (∏ i, |c i| ^ q.1 i) *
        if (binaryMultiplicityTuple labels seed q) 1 =
            (binaryMultiplicityTuple labels seed q) 0 then 0
    else ‖binaryCommutatorWord H (binaryOuterWord (binaryMultiplicityTuple labels seed q))‖ := by
  rw [adSequence_smul, adSequence_smul_fun, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_prod]
  simp_rw [abs_pow]
  rw [show (fun i ↦ H (labels i)) = H ∘ labels from rfl,
    adSequence_binary_eq_nestedComm, norm_nestedComm_binary]
  ring

/-- **Binary remainder weights.** The original multinomial commutator norm sum
is exactly a nonnegative weighted sum of the normalized right-nested words. -/
theorem αCommConj_eq_sum_binaryWordWeight {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {s p : ℕ} (H : Fin 2 → A) (labels : Fin s → Fin 2) (c : Fin s → ℝ)
    (seed : Fin 2) (d : ℝ) :
    αCommConj (fun i ↦ c i • H (labels i)) (d • H seed) (p + 1) =
      ∑ w : Fin p → Fin 2, binaryConjugationWordWeight labels c seed d w *
        ‖binaryCommutatorWord H w‖ := by
  classical
  rw [αCommConj, ← sum_coe_sort]
  simp_rw [binaryConjugationWordWeight, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [norm_adSequence_binary_smul]
  by_cases h : (binaryMultiplicityTuple labels seed q) 1 =
      (binaryMultiplicityTuple labels seed q) 0
  · simp [h]
  · simp [Ne, h, mul_assoc]

end TrotterError
