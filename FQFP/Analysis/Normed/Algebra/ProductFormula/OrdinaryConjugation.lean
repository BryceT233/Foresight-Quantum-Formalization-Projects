/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.CommutatorExpansion

/-!
# Finite conjugation bounds from exponential contractions

The finite commutator expansion has no growth loss when each exponential is a
contraction for every real parameter. The coefficients, ordering and factorial
weights are those of `commutatorExpansion_conj`; no new expansion is introduced.

## Main results

* `norm_commutatorRemainder_le_of_le_one`: the original multinomial constant.
* `norm_multiConj_sub_sum_le_of_le_one`: the finite Taylor bound for every real step.
* `norm_multiConj_sub_sum_le_of_skewAdjoint`: the C*-algebra specialization.
-/

@[expose] public noncomputable section

open NormedSpace MeasureTheory Finset
open scoped RealScalar algebraMap

namespace TrotterError

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- A finite ordered composition of conjugations preserves the norm under
two-sided exponential contraction bounds, including for the empty list. -/
theorem norm_list_exp_conj_eq_of_le_one {ι : Type*} (A : ι → 𝔸)
    (hA : ∀ i (t : ℝ), ‖exp (t • A i)‖ ≤ 1) (l : List ι) (B : 𝔸) (t : ℝ) :
    ‖(l.map (fun i ↦ exp (t • A i))).reverse.prod * B *
      (l.map (fun i ↦ exp ((-t) • A i))).prod‖ = ‖B‖ := by
  induction l generalizing B with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      rw [show (l.map (fun i ↦ exp (t • A i))).reverse.prod * exp (t • A i) * B *
          (exp ((-t) • A i) * (l.map (fun i ↦ exp ((-t) • A i))).prod) =
        (l.map (fun i ↦ exp (t • A i))).reverse.prod * expSMulConj (A i) B t *
          (l.map (fun i ↦ exp ((-t) • A i))).prod by
            simp only [expSMulConj, mul_assoc]]
      rw [ih, norm_expSMulConj_eq_of_le_one (A i) B (hA i) t]

/-- A finite conjugation remainder term has its exact multinomial weight when
all the exponential factors are contractions in both time directions. -/
theorem norm_commutatorRemainderTerm_le_of_le_one {s : ℕ}
    (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (t : ℝ)
    (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B t j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |t| ^ p /
          (Nat.factorial p : ℝ) := by
  let X := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast_le : 1 ≤ q (Fin.last j) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have hint : ‖∫ u in 0..t, (((t - u) ^ (q (Fin.last j) - 1) *
        t ^ (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u‖ ≤
      ‖X‖ * |t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D) := by
    apply norm_conj_smul_integral_le_of_norm_conj_le (A j) X (q (Fin.last j))
      (∑ i : Fin j, q i.castSucc) D hlast_le hD t ‖X‖ (norm_nonneg X)
    intro u _
    exact (norm_expSMulConj_eq_of_le_one (A j) X (hA j) u).le
  have hcoeff : |t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
      ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |t| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      rw [add_comm, ← Fin.sum_univ_castSucc, hsum]
    rw [hqsum, ← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q t hsum hlast_le
  have hnorm : ‖commutatorRemainderTerm A B t j q‖ =
      ‖∫ u in 0..t, (((t - u) ^ (q (Fin.last j) - 1) *
        t ^ (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u‖ := by
    unfold commutatorRemainderTerm
    simpa only [List.map_drop, List.map_ofFn, Function.comp_def, X, D] using
      norm_list_exp_conj_eq_of_le_one A hA
        ((List.ofFn (fun i : Fin s ↦ i)).drop (j + 1)) _ t
  rw [hnorm]
  calc
    _ ≤ ‖X‖ * |t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D) := hint
    _ = ‖X‖ * (|t| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D)) := by ring
    _ = _ := by
      rw [hcoeff]
      dsimp only [X]
      ring

/-- **Finite conjugation remainder bound.** The full multinomial commutator
constant is retained, with no exponential growth factor or step restriction. -/
theorem norm_commutatorRemainder_le_of_le_one {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) (t : ℝ) (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) :
    ‖commutatorRemainder A B p t‖ ≤ αCommConj A B p * |t| ^ p /
      (Nat.factorial p : ℝ) := by
  simpa only [one_mul, mul_one] using
    norm_mul_commutatorRemainder_le_of_term_bound (1 : 𝔸) A B p t 1 (by norm_num)
      (fun j q hq ↦ by
        simpa only [one_mul, mul_one] using
          norm_commutatorRemainderTerm_le_of_le_one A B p t hA j q
            (mem_filter.mp hq).1 (mem_filter.mp hq).2)

/-- The finite Taylor polynomial of an ordered composition of conjugations has
the original multinomial remainder bound for every real parameter. -/
theorem norm_multiConj_sub_sum_le_of_le_one {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) (hp : 1 ≤ p) (t : ℝ)
    (hA : ∀ i (u : ℝ), ‖exp (u • A i)‖ ≤ 1) :
    ‖multiConj A B t - ∑ k ∈ range p, conjCoeff A B k * (t ^ k : 𝔸)‖ ≤
      αCommConj A B p * |t| ^ p / (Nat.factorial p : ℝ) := by
  rw [commutatorExpansion_conj A B p t hp, add_sub_cancel_left]
  exact norm_commutatorRemainder_le_of_le_one A B p t hA

/-- In a C*-algebra, skew-adjoint generators automatically satisfy the
exponential contraction assumptions of the finite Taylor bound. -/
theorem norm_multiConj_sub_sum_le_of_skewAdjoint [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (hp : 1 ≤ p)
    (t : ℝ) (hA : ∀ i, star (A i) = -A i) :
    ‖multiConj A B t - ∑ k ∈ range p, conjCoeff A B k * (t ^ k : 𝔸)‖ ≤
      αCommConj A B p * |t| ^ p / (Nat.factorial p : ℝ) := by
  rcases subsingleton_or_nontrivial 𝔸 with h | h
  · let := h
    rw [Subsingleton.elim (multiConj A B t -
      ∑ k ∈ range p, conjCoeff A B k * (t ^ k : 𝔸)) 0, norm_zero]
    unfold αCommConj
    positivity
  · let := h
    exact norm_multiConj_sub_sum_le_of_le_one A B p hp t
      (fun i u ↦ (norm_exp_smul_of_skewAdjoint (hA i) u).le)

end

/-- The multinomial commutator constant of an empty generator list vanishes
at every positive order. -/
theorem αCommConj_empty {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸]
    (A : Fin 0 → 𝔸) (B : 𝔸) (p : ℕ) (hp : 1 ≤ p) :
    αCommConj A B p = 0 := by
  have hempty : finAntidiagonal 0 p = ∅ := by
    ext q
    simp only [mem_finAntidiagonal, Finset.sum_empty, Finset.univ_eq_empty,
      Finset.notMem_empty, iff_false]
    lia
  simp [αCommConj, hempty]

end TrotterError
