/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.WordNorm

/-!
# Weighted expansions in binary words

The BCH terms of `BCHTerms.lean` are sums of monomials — words on the two letters `a`, `b` — with
rational coefficients: the four quintic groups are 4, 10, 14 and 2 words over `720`, and the cubic
and quartic terms are of the same shape. This file supplies the arity-free norm API that such a
sum consumes, so that each generated monomial bound is one application rather than a `calc` block.

## Main results

* `wordEval v a b` — the word with letter `i` equal to `a` if `v i`, else `b`.
* `norm_wordEval_le` — `‖∏ i, wordEval v a b i‖ ≤ (‖a‖ + ‖b‖) ^ n`.
* `norm_sum_smul_wordEval_le` — **the group lemma**: a `ℚ`-weighted sum of `m` such words is bounded
  by `m * cb * (‖a‖ + ‖b‖) ^ n`.

## Implementation notes

The word pattern is data (`Fin n → Bool`), so a generated bound is
`norm_sum_smul_wordEval_le c v a b hc hcb` and needs no case analysis on the letters. Contrast the
hand-unrolled `norm_bchQuinticGroup*_le` in `BCHTerms.lean`, which write out one `norm_word5_le`
call per word plus a `norm_add_le` step per summand.
-/

@[expose] public section

open Finset

namespace FQFP.BCH

/-! ### Binary words -/

/-- The binary word `v` evaluated in a ring: its `i`-th letter is `a` if `v i` is true, and `b`
otherwise. -/
def wordEval {𝔸 : Type*} {n : ℕ} (v : Fin n → Bool) (a b : 𝔸) : Fin n → 𝔸 :=
  fun i => if v i then a else b

section Bounds

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- Every letter of a binary word has norm at most `‖a‖ + ‖b‖`. -/
lemma norm_wordEval_apply_le {n : ℕ} (v : Fin n → Bool) (a b : 𝔸) (i : Fin n) :
    ‖wordEval v a b i‖ ≤ ‖a‖ + ‖b‖ := by
  rw [wordEval]
  split
  · exact le_add_of_nonneg_right (norm_nonneg b)
  · exact le_add_of_nonneg_left (norm_nonneg a)

/-- The uniform word bound: the norm of a word on `{a, b}` is at most `(‖a‖ + ‖b‖) ^ n`. -/
lemma norm_wordEval_le [NormOneClass 𝔸] {n : ℕ} (v : Fin n → Bool) (a b : 𝔸) :
    ‖(List.ofFn (wordEval v a b)).prod‖ ≤ (‖a‖ + ‖b‖) ^ n :=
  norm_word_le _ fun i => norm_wordEval_apply_le v a b i

end Bounds

/-- **The group lemma**: an `ι`-indexed `ℚ`-weighted expansion in `n`-letter words on `{a, b}` is
bounded by `card ι * cb * (‖a‖ + ‖b‖) ^ n` as soon as every coefficient has norm at most `cb`.

A group of the quintic term is the case `ι = Fin m` with the words as data, so its bound becomes one
application of this lemma instead of `m` per-word estimates and `m - 1` triangle steps. -/
lemma norm_sum_smul_wordEval_le {ι : Type*} [Fintype ι] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] {n : ℕ} (c : ι → ℚ) (v : ι → Fin n → Bool)
    (a b : 𝔸) {cb : ℝ} (hc : ∀ i, ‖c i‖ ≤ cb) (hcb : 0 ≤ cb) :
    ‖∑ i, c i • (List.ofFn (wordEval (v i) a b)).prod‖
      ≤ (Fintype.card ι : ℝ) * cb * (‖a‖ + ‖b‖) ^ n := by
  calc ‖∑ i, c i • (List.ofFn (wordEval (v i) a b)).prod‖
      ≤ ∑ i, ‖c i • (List.ofFn (wordEval (v i) a b)).prod‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, cb * (‖a‖ + ‖b‖) ^ n := by
        refine sum_le_sum fun i _ => ?_
        calc ‖c i • (List.ofFn (wordEval (v i) a b)).prod‖
            ≤ ‖c i‖ * ‖(List.ofFn (wordEval (v i) a b)).prod‖ := norm_smul_le _ _
          _ ≤ cb * (‖a‖ + ‖b‖) ^ n :=
              mul_le_mul (hc i) (norm_wordEval_le (v i) a b) (norm_nonneg _) hcb
    _ = (Fintype.card ι : ℝ) * (cb * (‖a‖ + ‖b‖) ^ n) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * cb * (‖a‖ + ‖b‖) ^ n := by ring

end FQFP.BCH
