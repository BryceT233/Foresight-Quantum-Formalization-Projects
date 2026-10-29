/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.BinaryCommutatorWeights
public import FQFP.Analysis.Normed.Algebra.ProductFormula.HalfDefectConjugation
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiLocalError

/-!
# Exact nonnegative weights of the Suzuki seventh-order remainder

The original finite conjugation constant is regrouped by its binary right-nested
words. All weights are defined by finite sums of absolute stage coefficients.

## Main definitions

* `binaryHalfDefectWordWeight`: normalized weights for a binary half-list.
* `FQFP.BCH.suzukiSepticWordWeight`: the 32 weights for the Suzuki half-list.

## Main results

* `FQFP.BCH.suzukiSepticConstant_eq_sum_wordWeight`: the original constant as a 32-word sum.
-/

@[expose] public noncomputable section

open Finset TrotterError
open scoped RealScalar

namespace FQFP

/-- Evaluation of a binary letter with its real scalar coefficient. -/
def binaryStageValue {A : Type*} [AddCommGroup A] [Module ℝ A]
    (H : Fin 2 → A) (a : Fin 2 × ℝ) : A := a.2 • H a.1

/-- The binary conjugation weight associated with a scalar-labeled generator list and seed. -/
def binaryListConjugationWordWeight {p : ℕ} (l : List (Fin 2 × ℝ))
    (seed : Fin 2 × ℝ) (w : Fin p → Fin 2) : ℝ :=
  binaryConjugationWordWeight (fun i : Fin l.length ↦ (l.get i).1)
    (fun i ↦ (l.get i).2) seed.1 seed.2 w

/-- Normalized word weights of the original half-defect constant, with its two seed terms. -/
def binaryHalfDefectWordWeight {p : ℕ} (l : List (Fin 2 × ℝ)) (w : Fin p → Fin 2) : ℝ :=
  (2 * ((logDerivConjugationTerms l).map fun q ↦
    binaryListConjugationWordWeight q.1 q.2 w).sum +
    binaryListConjugationWordWeight l (0, 1) w +
    binaryListConjugationWordWeight l (1, 1) w) / (Nat.factorial (p + 2) : ℝ)

/-- Half-defect word weights are nonnegative, for arbitrary signed stage coefficients. -/
lemma binaryHalfDefectWordWeight_nonneg {p : ℕ} (l : List (Fin 2 × ℝ))
    (w : Fin p → Fin 2) : 0 ≤ binaryHalfDefectWordWeight l w := by
  have hweight (m : List (Fin 2 × ℝ)) (seed : Fin 2 × ℝ) :
      0 ≤ binaryListConjugationWordWeight m seed w := binaryConjugationWordWeight_nonneg ..
  have hsum : 0 ≤ ((logDerivConjugationTerms l).map fun q ↦
      binaryListConjugationWordWeight q.1 q.2 w).sum :=
    List.sum_nonneg fun x hx ↦ by
      rcases List.mem_map.mp hx with ⟨q, _, rfl⟩
      exact hweight q.1 q.2
  exact div_nonneg (by linarith [hweight l (0, 1), hweight l (1, 1)]) (by positivity)

/-- Suffix-generator pairs commute with mapping a half-list into an algebra. -/
lemma logDerivConjugationTerms_map {A B : Type*} (f : A → B) (l : List A) :
    logDerivConjugationTerms (l.map f) =
      (logDerivConjugationTerms l).map (fun q ↦ (q.1.map f, f q.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [logDerivConjugationTerms, ih]

section NormedAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The binary word regrouping is unchanged by using list indices. -/
lemma αCommConj_binaryStageList_eq_sum {p : ℕ} (H : Fin 2 → A)
    (l : List (Fin 2 × ℝ)) (seed : Fin 2 × ℝ) :
    αCommConj (fun i : Fin (l.map (binaryStageValue H)).length ↦
        -(l.map (binaryStageValue H)).get i) (binaryStageValue H seed) (p + 1) =
      ∑ w : Fin p → Fin 2, binaryListConjugationWordWeight l seed w *
        ‖binaryCommutatorWord H w‖ := by
  rw [αCommConj_neg_eq, ← αCommConj_cast (List.length_map (binaryStageValue H))]
  simp only [List.get_eq_getElem, List.getElem_map]
  exact αCommConj_eq_sum_binaryWordWeight H _ _ _ _

/-- **Exact half-defect word expansion.** The original remainder constant equals
the nonnegative weighted sum of the binary right-nested commutator norms. -/
theorem halfDefectCommutatorConstant_eq_sum_binaryWordWeight {p : ℕ}
    (H : Fin 2 → A) (l : List (Fin 2 × ℝ)) :
    halfDefectCommutatorConstant (l.map (binaryStageValue H)) (H 0) (H 1) (p + 1) =
      ∑ w : Fin p → Fin 2, binaryHalfDefectWordWeight l w *
        ‖binaryCommutatorWord H w‖ := by
  rw [halfDefectCommutatorConstant, logDerivConjugationTerms_map]
  simp only [List.map_map, Function.comp_def]
  simp_rw [αCommConj_binaryStageList_eq_sum]
  have hseed (i : Fin 2) :
      αCommConj (fun j : Fin (l.map (binaryStageValue H)).length ↦
          -(l.map (binaryStageValue H)).get j) (H i) (p + 1) =
        ∑ w : Fin p → Fin 2, binaryListConjugationWordWeight l (i, 1) w *
          ‖binaryCommutatorWord H w‖ := by
    simpa only [binaryStageValue, one_smul] using
      αCommConj_binaryStageList_eq_sum H l (i, 1)
  rw [hseed, hseed, TrotterError.List.sum_map_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro w _
  rw [List.sum_map_mul_right]
  unfold binaryHalfDefectWordWeight
  ring

end NormedAlgebra

end FQFP

namespace FQFP.BCH

/-- The scalar coefficients and binary labels of the six Suzuki half-stages. -/
def suzukiHalfStages (p : ℝ) : List (Fin 2 × ℝ) :=
  [(0, p / 2), (1, p), (0, p), (1, p), (0, (1 - 3 * p) / 2), (1, (1 - 4 * p) / 2)]

/-- The seventh-order weight of a five-letter adjoint word, including time integration. -/
def suzukiSepticWordWeight (p : ℝ) (w : Fin 5 → Fin 2) : ℝ :=
  binaryHalfDefectWordWeight (suzukiHalfStages p) w

/-- Each seventh-order word weight is nonnegative, for every real composition parameter. -/
lemma suzukiSepticWordWeight_nonneg (p : ℝ) (w : Fin 5 → Fin 2) :
    0 ≤ suzukiSepticWordWeight p w := binaryHalfDefectWordWeight_nonneg ..

/-- The scalar-labeled stages evaluate to the existing six half-generators. -/
lemma suzukiHalfStages_map_eq {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) (p : ℝ) :
    (suzukiHalfStages p).map (binaryStageValue ![a, b]) =
      List.ofFn (fiveStageStrangHalfGenerator a b p) := by
  simp [suzukiHalfStages, binaryStageValue, fiveStageStrangHalfGenerator, List.ofFn_succ]

section NormedAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- **Exact 32-weight expansion.** The original seventh-order constant equals
the nonnegative weighted sum with the innermost bracket oriented as `[b,a]`. -/
theorem suzukiSepticConstant_eq_sum_wordWeight (a b : A) (p : ℝ) :
    suzukiSepticConstant a b p =
      ∑ w : Fin 5 → Fin 2, suzukiSepticWordWeight p w * ‖binaryCommutatorWord ![a, b] w‖ := by
  unfold suzukiSepticConstant
  rw [← suzukiHalfStages_map_eq]
  simpa only [suzukiSepticWordWeight, Matrix.cons_val_zero, Matrix.cons_val_one] using
    (halfDefectCommutatorConstant_eq_sum_binaryWordWeight (p := 5) ![a, b] (suzukiHalfStages p))

end NormedAlgebra

end FQFP.BCH
