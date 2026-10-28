/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.Word
public import Mathlib.Tactic.NoncommRing

/-!
# Binary word bounds and differences

Positive-length words are bounded without `NormOneClass`. Weighted coefficient tables
are handled directly by `FQFP.Analysis.Normed.Algebra.WordTable`; this file supplies binary word
bounds, unweighted finite sums, and telescoping differences of ordered products.
-/

@[expose] public section

open Finset

namespace FQFP.BCH

section Bounds

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- A positive-length binary word is bounded by the sum of the letter norms to its length. -/
lemma norm_binWord_le_of_pos {n : ℕ} (hn : 0 < n) (v : Fin n → Fin 2) (a b : 𝔸) :
    ‖wordEval ![a, b] v‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  simp only [wordEval, List.map_ofFn, Function.comp_def]
  refine norm_word_le_of_pos hn _ fun i ↦ ?_
  generalize v i = j
  fin_cases j <;> simp

/-- A nonempty binary word satisfies the uniform bound without an assumption on `‖1‖`. -/
lemma norm_prod_map_pair_le_of_ne_nil (l : List (Fin 2)) (hl : l ≠ []) (a b : 𝔸) :
    ‖(l.map ![a, b]).prod‖ ≤ (‖a‖ + ‖b‖) ^ l.length := by
  simpa only [wordEval, List.ofFn_getElem] using
    norm_binWord_le_of_pos (List.length_pos_iff.mpr hl) (fun i : Fin l.length ↦ l[i.val]) a b

end Bounds

/-! ### The unweighted group bound -/

section GroupBound

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- A sum of positive-length binary words is bounded by its number of words times their bound. -/
theorem norm_sum_wordEval_le_of_pos {ι : Type*} [Fintype ι] {n : ℕ} (hn : 0 < n)
    (v : ι → Fin n → Fin 2) (a b : 𝔸) :
    ‖∑ i, wordEval ![a, b] (v i)‖ ≤ (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by
  calc
    ‖∑ i, wordEval ![a, b] (v i)‖ ≤ ∑ i, ‖wordEval ![a, b] (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (‖a‖ + ‖b‖) ^ n :=
      Finset.sum_le_sum fun i _ ↦ norm_binWord_le_of_pos hn (v i) a b
    _ = (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by simp

end GroupBound

/-! ### Telescoping a difference of two word products

`∥u v - u' v'∥` is bounded by charging one `‖u i - v i‖` per position and `M` to all the others.
This is the primitive behind every "difference of a monomial" estimate: one application replaces a
hand-written expansion of the difference into `k` terms and `k - 1` triangle steps. -/

section Telescoping

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Split off the leading letter of a nonempty `List.ofFn` product. -/
private lemma ofFn_prod_succ {𝔸 : Type*} [Monoid 𝔸] {m : ℕ} (w : Fin (m + 1) → 𝔸) :
    (List.ofFn w).prod = w 0 * (List.ofFn fun i : Fin m => w i.succ).prod := by
  rw [List.ofFn_succ, List.prod_cons]

/-- The induction behind `norm_prod_sub_prod_le`, stated as a `∀` over the length so that the
induction hypothesis applies to the tails. -/
private theorem norm_prod_sub_prod_le_aux : ∀ n : ℕ, ∀ (u v : Fin (n + 1) → 𝔸) {M : ℝ}
    (d : Fin (n + 1) → ℝ), (∀ i, ‖u i‖ ≤ M) → (∀ i, ‖v i‖ ≤ M) →
    (∀ i, ‖u i - v i‖ ≤ d i) → (∀ i, 0 ≤ d i) → 0 ≤ M →
    ‖(List.ofFn u).prod - (List.ofFn v).prod‖ ≤ M ^ n * ∑ i, d i := by
  intro n
  induction n with
  | zero =>
      intro u v M d _ _ hd _ _
      rw [Fin.sum_univ_one, pow_zero, one_mul]
      simpa using hd 0
  | succ n ih =>
      intro u v M d hu hv hd hdn hM
      have hV : ‖(List.ofFn fun i : Fin (n + 1) => v i.succ).prod‖ ≤ M ^ (n + 1) :=
        norm_word_le_of_pos (Nat.zero_lt_succ n) _ fun i => hv i.succ
      have hUV : ‖(List.ofFn fun i : Fin (n + 1) => u i.succ).prod
            - (List.ofFn fun i : Fin (n + 1) => v i.succ).prod‖
          ≤ M ^ n * ∑ i : Fin (n + 1), d i.succ :=
        ih (fun i => u i.succ) (fun i => v i.succ) (fun i => d i.succ)
          (fun i => hu i.succ) (fun i => hv i.succ) (fun i => hd i.succ)
          (fun i => hdn i.succ) hM
      have htel : u 0 * (List.ofFn fun i : Fin (n + 1) => u i.succ).prod
            - v 0 * (List.ofFn fun i : Fin (n + 1) => v i.succ).prod =
          (u 0 - v 0) * (List.ofFn fun i : Fin (n + 1) => v i.succ).prod
            + u 0 * ((List.ofFn fun i : Fin (n + 1) => u i.succ).prod
              - (List.ofFn fun i : Fin (n + 1) => v i.succ).prod) := by
        noncomm_ring
      rw [ofFn_prod_succ u, ofFn_prod_succ v, htel, Fin.sum_univ_succ, pow_succ]
      calc ‖(u 0 - v 0) * (List.ofFn fun i : Fin (n + 1) => v i.succ).prod
            + u 0 * ((List.ofFn fun i : Fin (n + 1) => u i.succ).prod
              - (List.ofFn fun i : Fin (n + 1) => v i.succ).prod)‖
          ≤ ‖(u 0 - v 0) * (List.ofFn fun i : Fin (n + 1) => v i.succ).prod‖
            + ‖u 0 * ((List.ofFn fun i : Fin (n + 1) => u i.succ).prod
              - (List.ofFn fun i : Fin (n + 1) => v i.succ).prod)‖ := norm_add_le _ _
        _ ≤ ‖u 0 - v 0‖ * ‖(List.ofFn fun i : Fin (n + 1) => v i.succ).prod‖
            + ‖u 0‖ * ‖(List.ofFn fun i : Fin (n + 1) => u i.succ).prod
              - (List.ofFn fun i : Fin (n + 1) => v i.succ).prod‖ := by
            gcongr <;> exact norm_mul_le _ _
        _ ≤ d 0 * M ^ (n + 1) + M * (M ^ n * ∑ i : Fin (n + 1), d i.succ) :=
            add_le_add (mul_le_mul (hd 0) hV (norm_nonneg _) (hdn 0))
              (mul_le_mul (hu 0) hUV (norm_nonneg _) hM)
        _ = M ^ n * M * (d 0 + ∑ i : Fin (n + 1), d i.succ) := by ring

/-- **Telescoping bound for a difference of products.** If the letters of `u` and `v` are bounded by
`M` and differ by at most `d i` at position `i`, then the products differ by at most
`M ^ n * ∑ i, d i`, where `n + 1` is the number of letters.

The factor `M ^ n` is what one pays for the `n` letters that are merely bounded; the single
differing position costs `d i`. -/
theorem norm_prod_sub_prod_le {n : ℕ} (u v : Fin (n + 1) → 𝔸) {M : ℝ} (d : Fin (n + 1) → ℝ)
    (hu : ∀ i, ‖u i‖ ≤ M) (hv : ∀ i, ‖v i‖ ≤ M) (hd : ∀ i, ‖u i - v i‖ ≤ d i)
    (hdn : ∀ i, 0 ≤ d i) (hM : 0 ≤ M) :
    ‖(List.ofFn u).prod - (List.ofFn v).prod‖ ≤ M ^ n * ∑ i, d i :=
  norm_prod_sub_prod_le_aux n u v d hu hv hd hdn hM

/-- **Difference of two binary word products.** If the pattern `v` is read at `z` and at `x` in the
`a`-positions (`v i = 0`) and at `y` everywhere else, then the products differ by at most the number
of `a`-positions times `M ^ n * ‖z - x‖`.

Stated with `wordEval` spelled out: `wordEval letters v` *is*
`((List.ofFn v).map letters).prod`, and keeping the `List` form here means the two readings can be
rewritten independently. -/
theorem norm_binWord_sub_le {n : ℕ} (v : Fin (n + 1) → Fin 2) (z x y : 𝔸) {M : ℝ}
    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 0 ≤ M) :
    ‖(List.ofFn fun i => (![z, y] : Fin 2 → 𝔸) (v i)).prod
        - (List.ofFn fun i => (![x, y] : Fin 2 → 𝔸) (v i)).prod‖
      ≤ ((Finset.univ.filter fun i => v i = 0).card : ℝ) * M ^ n * ‖z - x‖ := by
  have hcard : (∑ i, (if v i = 0 then ‖z - x‖ else 0 : ℝ))
      = ((Finset.univ.filter fun i => v i = 0).card : ℝ) * ‖z - x‖ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have h01 : ∀ i : Fin (n + 1), v i = 0 ∨ v i = 1 := by
    intro i
    generalize hv : v i = w
    fin_cases w <;> simp
  have hmain : ‖(List.ofFn fun i => (![z, y] : Fin 2 → 𝔸) (v i)).prod
        - (List.ofFn fun i => (![x, y] : Fin 2 → 𝔸) (v i)).prod‖
      ≤ M ^ n * ∑ i, (if v i = 0 then ‖z - x‖ else 0 : ℝ) := by
    refine norm_prod_sub_prod_le _ _
      (fun i => if v i = 0 then ‖z - x‖ else 0) ?_ ?_ ?_ ?_ hM
    · intro i
      rcases h01 i with h | h <;> simp [h, hz, hy]
    · intro i
      rcases h01 i with h | h <;> simp [h, hx, hy]
    · intro i
      rcases h01 i with h | h <;> simp [h]
    · intro i
      rcases h01 i with h | h <;> simp [h]
  have hlast : M ^ n * ∑ i, (if v i = 0 then ‖z - x‖ else 0 : ℝ)
      = ((Finset.univ.filter fun i => v i = 0).card : ℝ) * M ^ n * ‖z - x‖ := by
    rw [hcard]
    ring
  exact hmain.trans (le_of_eq hlast)

/-- **Difference of two word expansions**, summed over an index type: the constant is the total
number of `a`-positions, which is what makes the sharp constants of the `Lean-BCH` quintic group
bounds (`10`, `25`, `35`, `5`) come out. -/
theorem norm_sum_binWord_diff_le {ι : Type*} [Fintype ι] {n : ℕ} (v : ι → Fin (n + 1) → Fin 2)
    (z x y : 𝔸) {M : ℝ} (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 0 ≤ M) :
    ‖(∑ i, (List.ofFn fun j => (![z, y] : Fin 2 → 𝔸) (v i j)).prod)
        - ∑ i, (List.ofFn fun j => (![x, y] : Fin 2 → 𝔸) (v i j)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => v i j = 0).card : ℝ)) * M ^ n * ‖z - x‖ := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ i, ((List.ofFn fun j => (![z, y] : Fin 2 → 𝔸) (v i j)).prod
          - (List.ofFn fun j => (![x, y] : Fin 2 → 𝔸) (v i j)).prod)‖
      ≤ ∑ i, ‖(List.ofFn fun j => (![z, y] : Fin 2 → 𝔸) (v i j)).prod
          - (List.ofFn fun j => (![x, y] : Fin 2 → 𝔸) (v i j)).prod‖ := norm_sum_le _ _
    _ ≤ ∑ i, (((Finset.univ.filter fun j => v i j = 0).card : ℝ) * M ^ n * ‖z - x‖) :=
        Finset.sum_le_sum fun i _ => norm_binWord_sub_le (v i) z x y hz hx hy hM
    _ = (∑ i, ((Finset.univ.filter fun j => v i j = 0).card : ℝ)) * M ^ n * ‖z - x‖ := by
        rw [Finset.sum_mul, Finset.sum_mul]

end Telescoping

end FQFP.BCH
