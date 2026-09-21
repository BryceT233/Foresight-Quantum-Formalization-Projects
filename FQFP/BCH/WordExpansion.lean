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

/-! ### The unweighted group bound -/

section GroupBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- **The group bound**: an `ι`-indexed expansion in `n`-letter words on `{a, b}` is bounded by
`card ι * (‖a‖ + ‖b‖) ^ n`. This is `norm_sum_smul_wordEval_le` at coefficient `1`, and it is what
a group of equally weighted words (such as the four `bchQuinticGroup*` of `BCHTerms.lean`) needs. -/
theorem norm_sum_wordEval_le {ι : Type*} [Fintype ι] {n : ℕ} (v : ι → Fin n → Bool) (a b : 𝔸) :
    ‖∑ i, (List.ofFn (wordEval (v i) a b)).prod‖ ≤
      (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by
  calc ‖∑ i, (List.ofFn (wordEval (v i) a b)).prod‖
      ≤ ∑ i, ‖(List.ofFn (wordEval (v i) a b)).prod‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (‖a‖ + ‖b‖) ^ n :=
        Finset.sum_le_sum fun i _ => norm_wordEval_le (v i) a b
    _ = (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by simp

end GroupBound

/-! ### Homogeneity of a word expansion -/

section Homogeneity

variable {𝕂 : Type*} [NormedField 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Scaling both letters scales every letter of the word. -/
theorem wordEval_smul {n : ℕ} (v : Fin n → Bool) (a b : 𝔸) (c : 𝕂) :
    wordEval v (c • a) (c • b) = fun i => c • wordEval v a b i := by
  funext i
  by_cases h : v i <;> simp [wordEval, h]

/-- Homogeneity of a word expansion: scaling `a` and `b` by `c` scales the `ι`-indexed sum of
`n`-letter word products by `c ^ n`. -/
theorem sum_wordEval_smul {ι : Type*} [Fintype ι] {n : ℕ} (v : ι → Fin n → Bool) (a b : 𝔸)
    (c : 𝕂) :
    (∑ i, (List.ofFn (wordEval (v i) (c • a) (c • b))).prod)
      = c ^ n • ∑ i, (List.ofFn (wordEval (v i) a b)).prod := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [wordEval_smul]; exact smul_prod c _

end Homogeneity

/-! ### Telescoping a difference of two word products

`∥u v - u' v'∥` is bounded by charging one `‖u i - v i‖` per position and `M` to all the others.
This is the primitive behind every "difference of a monomial" estimate: one application replaces a
hand-written expansion of the difference into `k` terms and `k - 1` triangle steps. -/

section Telescoping

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

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
        norm_word_le _ fun i => hv i.succ
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

/-- **Difference of two word products.** If the word pattern `v` is evaluated at `z` and at `x` in
the `a`-positions and at `y` everywhere else, then the products differ by at most the number of
`a`-positions times `M ^ n * ‖z - x‖`. -/
theorem norm_wordEval_sub_le {n : ℕ} (v : Fin (n + 1) → Bool) (z x y : 𝔸) {M : ℝ}
    (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 0 ≤ M) :
    ‖(List.ofFn (wordEval v z y)).prod - (List.ofFn (wordEval v x y)).prod‖
      ≤ ((Finset.univ.filter fun i => v i).card : ℝ) * M ^ n * ‖z - x‖ := by
  have hcard : (∑ i, (if v i then ‖z - x‖ else 0 : ℝ))
      = ((Finset.univ.filter fun i => v i).card : ℝ) * ‖z - x‖ := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc ‖(List.ofFn (wordEval v z y)).prod - (List.ofFn (wordEval v x y)).prod‖
      ≤ M ^ n * ∑ i, (if v i then ‖z - x‖ else 0 : ℝ) :=
        norm_prod_sub_prod_le (wordEval v z y) (wordEval v x y)
          (fun i => if v i then ‖z - x‖ else 0)
          (fun i => by by_cases h : v i <;> simp [wordEval, h, hz, hy])
          (fun i => by by_cases h : v i <;> simp [wordEval, h, hx, hy])
          (fun i => by by_cases h : v i <;> simp [wordEval, h, sub_self])
          (fun i => by by_cases h : v i <;> simp [h]) hM
    _ = ((Finset.univ.filter fun i => v i).card : ℝ) * M ^ n * ‖z - x‖ := by
        rw [hcard]; ring

/-- **Difference of two word expansions**, summed over an index type: the constant is the total
number of `a`-positions, which is what makes the sharp constants of the `Lean-BCH` quintic group
bounds (`10`, `25`, `35`, `5`) come out. -/
theorem norm_sum_wordEval_diff_le {ι : Type*} [Fintype ι] {n : ℕ} (v : ι → Fin (n + 1) → Bool)
    (z x y : 𝔸) {M : ℝ} (hz : ‖z‖ ≤ M) (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 0 ≤ M) :
    ‖(∑ i, (List.ofFn (wordEval (v i) z y)).prod)
        - ∑ i, (List.ofFn (wordEval (v i) x y)).prod‖
      ≤ (∑ i, ((Finset.univ.filter fun j => v i j).card : ℝ)) * M ^ n * ‖z - x‖ := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ i, ((List.ofFn (wordEval (v i) z y)).prod
          - (List.ofFn (wordEval (v i) x y)).prod)‖
      ≤ ∑ i, ‖(List.ofFn (wordEval (v i) z y)).prod
          - (List.ofFn (wordEval (v i) x y)).prod‖ := norm_sum_le _ _
    _ ≤ ∑ i, (((Finset.univ.filter fun j => v i j).card : ℝ) * M ^ n * ‖z - x‖) :=
        Finset.sum_le_sum fun i _ => norm_wordEval_sub_le (v i) z x y hz hx hy hM
    _ = (∑ i, ((Finset.univ.filter fun j => v i j).card : ℝ)) * M ^ n * ‖z - x‖ := by
        rw [Finset.sum_mul, Finset.sum_mul]

end Telescoping

/-! ### Words over an arbitrary alphabet

The Taylor remainders of `BCHTerms.lean` are sums of monomials on **three** letters (`x`, `V`, `y`),
so the binary `wordEval` above does not reach them. `wordProdList` generalizes to an arbitrary
alphabet `κ`, and represents the pattern as a `List κ` rather than a `Fin n → κ`.

The pattern representation is not cosmetic. A generated monomial sum is emitted with its words as
data and is *also* compared, downstream, against explicitly written polynomials; bridging the two
needs the concrete patterns to evaluate. `wordProdList`'s defining equations are `rfl`, so a literal
pattern evaluates definitionally. `wordEval`'s `if (v i) then a else b` does not: the `Bool`-coerced
condition reaches the goal as `if true = true then a else b`, which neither
`simp only [↓reduceIte]` nor `simp only [cond_true]` reduces in that context, and `abel` /
`noncomm_ring` then see it as an atom distinct from `a`. -/

section WordProdList

/-- The product of the letters selected by a word pattern over an alphabet `κ`: the empty pattern is
`1`, and a pattern is read left to right. -/
def wordProdList {κ 𝔸 : Type*} [Monoid 𝔸] (letters : κ → 𝔸) : List κ → 𝔸
  | [] => 1
  | k :: t => letters k * wordProdList letters t

@[simp]
lemma wordProdList_nil {κ 𝔸 : Type*} [Monoid 𝔸] (letters : κ → 𝔸) :
    wordProdList letters [] = 1 := rfl

@[simp]
lemma wordProdList_cons {κ 𝔸 : Type*} [Monoid 𝔸] (letters : κ → 𝔸) (k : κ) (t : List κ) :
    wordProdList letters (k :: t) = letters k * wordProdList letters t := rfl

variable {κ 𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- Letter-wise norm bound for `wordProdList`: if the letter `k` has norm at most `b k`, then the
product has norm at most the product of the bounds of the letters occurring in the pattern. -/
lemma norm_wordProdList_le (letters : κ → 𝔸) {b : κ → ℝ} (hb : ∀ k, ‖letters k‖ ≤ b k)
    (w : List κ) : ‖wordProdList letters w‖ ≤ (w.map b).prod := by
  induction w with
  | nil => simp
  | cons k t ih =>
      rw [wordProdList_cons, List.map_cons, List.prod_cons]
      calc ‖letters k * wordProdList letters t‖
          ≤ ‖letters k‖ * ‖wordProdList letters t‖ := norm_mul_le _ _
        _ ≤ b k * (List.map b t).prod :=
            mul_le_mul (hb k) ih (norm_nonneg _) (le_trans (norm_nonneg _) (hb k))

end WordProdList

/-- **The alphabet-free group bound**: an `ι`-indexed `ℚ`-weighted sum of words over an alphabet `κ`
is bounded by `card ι * cb * B` as soon as every coefficient has norm at most `cb`, every word has
norm at most `B`, and `cb` is nonnegative.

This is `norm_sum_smul_wordEval_le` with the alphabet freed, and it is what a generated Taylor
remainder bounds itself with, one application per group. -/
lemma norm_sum_smul_wordProdList_le {ι κ : Type*} [Fintype ι] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] (c : ι → ℚ) (letters : κ → 𝔸) (w : ι → List κ)
    {B cb : ℝ} (hc : ∀ i, ‖c i‖ ≤ cb) (hw : ∀ i, ‖wordProdList letters (w i)‖ ≤ B)
    (hcb : 0 ≤ cb) :
    ‖∑ i, c i • wordProdList letters (w i)‖ ≤ (Fintype.card ι : ℝ) * cb * B := by
  calc ‖∑ i, c i • wordProdList letters (w i)‖
      ≤ ∑ i, ‖c i • wordProdList letters (w i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, cb * B := Finset.sum_le_sum fun i _ => by
        calc ‖c i • wordProdList letters (w i)‖
            ≤ ‖c i‖ * ‖wordProdList letters (w i)‖ := norm_smul_le _ _
          _ ≤ cb * B := mul_le_mul (hc i) (hw i) (norm_nonneg _) hcb
    _ = (Fintype.card ι : ℝ) * (cb * B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * cb * B := by ring

/-! ### Distributing a sum over a binary word

`Finset.prod_add` — and every lemma of its family — is `CommSemiring`-only, because its right-hand
side collects all the `f`-factors at the front. For a noncommutative multiplication that identity
is simply false. BCH's `𝔸` is a general `NormedRing`, so the expansion of a word product has to
keep the letters in place.

`wordProdList_add` does that. It is proved by induction on the word from the *left*
(`List.reverseRecOn`): appending one letter leaves the position indices of the prefix unchanged, so
the subsets of positions carry over verbatim. Every product step is `List.prod_append`, which needs
no commutativity; the `Finset` steps only ever concern sums, which are commutative anyway. -/

section Distributing

variable {𝔸 : Type*} [Semiring 𝔸]

/-- Reading a word is mapping its letters and taking the product. -/
lemma wordProdList_eq_prod_map {κ : Type*} (letters : κ → 𝔸) (w : List κ) :
    wordProdList letters w = (w.map letters).prod := by
  induction w with
  | nil => rfl
  | cons k t ih => rw [wordProdList_cons, List.map_cons, List.prod_cons, ih]

/-- `wordProdList` over a concatenation is the product of the `wordProdList`s. -/
lemma wordProdList_append {κ : Type*} (letters : κ → 𝔸) (l₁ l₂ : List κ) :
    wordProdList letters (l₁ ++ l₂) = wordProdList letters l₁ * wordProdList letters l₂ := by
  rw [wordProdList_eq_prod_map, wordProdList_eq_prod_map, wordProdList_eq_prod_map,
    List.map_append, List.prod_append]

/-- The `List (Fin 2)` reading of a `Bool`-valued word pattern: `true` is the letter `a` (index
`0`) and `false` the letter `b` (index `1`). -/
def wordEvalPattern {n : ℕ} (v : Fin n → Bool) : List (Fin 2) :=
  List.ofFn fun j => if v j then 0 else 1

/-- `wordEval` read through `wordProdList`: the two readings of a word pattern — `Bool` with
`true` for `a`, and `Fin 2` with `0` for `a` — give the same product. -/
lemma wordProdList_wordEvalPattern {n : ℕ} (v : Fin n → Bool) (a b : 𝔸) :
    wordProdList ![a, b] (wordEvalPattern v) = (List.ofFn (wordEval v a b)).prod := by
  rw [wordProdList_eq_prod_map, wordEvalPattern, List.map_ofFn]
  refine congrArg List.prod ?_
  rw [List.ofFn_inj]
  funext j
  by_cases h : v j <;> simp [wordEval, h]

/-- The positions of the letter `a` (index `0`) in a binary word pattern, as absolute indices. -/
def wordAPositions (w : List (Fin 2)) : Finset ℕ :=
  (Finset.range w.length).filter fun j => w[j]? = some 0

/-- The word `w` with the letter `a` at each position in `s` replaced by `c`, read over the ternary
alphabet `0 = a`, `1 = c`, `2 = b`. Positions outside `s` keep their original letter. -/
def wordSubstA (w : List (Fin 2)) (s : Finset ℕ) : List (Fin 3) :=
  (List.range w.length).map fun j => if j ∈ s then 1 else if w[j]? = some 0 then 0 else 2

private lemma wordAPositions_concat (l : List (Fin 2)) (k : Fin 2) :
    wordAPositions (l ++ [k])
      = if k = 0 then insert l.length (wordAPositions l) else wordAPositions l := by
  unfold wordAPositions
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
    List.getElem?_concat_length]
  have hf : (Finset.range l.length).filter (fun j => (l ++ [k])[j]? = some 0)
      = (Finset.range l.length).filter (fun j => l[j]? = some 0) :=
    Finset.filter_congr fun j hj => by
      rw [List.getElem?_append_left (List.mem_range.mp hj)]
  rw [hf]
  by_cases hk : k = 0 <;> simp [hk]

private lemma length_notMem_wordAPositions (l : List (Fin 2)) :
    l.length ∉ wordAPositions l := by
  simp [wordAPositions]

private lemma wordSubstA_concat (l : List (Fin 2)) (k : Fin 2) (s : Finset ℕ) :
    wordSubstA (l ++ [k]) s = wordSubstA l (s.erase l.length)
      ++ [if l.length ∈ s then 1 else if k = 0 then 0 else 2] := by
  unfold wordSubstA
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    have hjlt : j < l.length := List.mem_range.mp hj
    have hjn : j ≠ l.length := by lia
    rw [List.getElem?_append_left hjlt]
    by_cases h : j ∈ s <;> simp [h, hjn, Finset.mem_erase]
  · simp

private lemma wordAPositions_concat_zero (l : List (Fin 2)) :
    wordAPositions (l ++ [0]) = insert l.length (wordAPositions l) := by
  rw [wordAPositions_concat]; simp

private lemma wordAPositions_concat_one (l : List (Fin 2)) :
    wordAPositions (l ++ [1]) = wordAPositions l := by
  rw [wordAPositions_concat]; simp

private lemma wordSubstA_concat_zero (l : List (Fin 2)) (s : Finset ℕ) :
    wordSubstA (l ++ [0]) s
      = wordSubstA l (s.erase l.length) ++ [if l.length ∈ s then 1 else 0] := by
  rw [wordSubstA_concat]; simp

private lemma wordSubstA_concat_one (l : List (Fin 2)) (s : Finset ℕ) :
    wordSubstA (l ++ [1]) s
      = wordSubstA l (s.erase l.length) ++ [if l.length ∈ s then 1 else 2] := by
  rw [wordSubstA_concat]; simp

private lemma prod_map_concat (l : List (Fin 2)) (k : Fin 2) (a c b : 𝔸) :
    ((l ++ [k]).map ![a + c, b]).prod = ((l.map ![a + c, b]).prod) * ![a + c, b] k := by
  rw [List.map_append, List.prod_append]
  simp

private lemma prod_map_concat_zero (l : List (Fin 2)) (a c b : 𝔸) :
    ((l ++ [0]).map ![a + c, b]).prod = ((l.map ![a + c, b]).prod) * (a + c) := by
  rw [prod_map_concat]; simp

private lemma prod_map_concat_one (l : List (Fin 2)) (a c b : 𝔸) :
    ((l ++ [1]).map ![a + c, b]).prod = ((l.map ![a + c, b]).prod) * b := by
  rw [prod_map_concat]; simp

/-- **Order-preserving expansion of a binary word product.**

Replacing the letter `a` by the sum `a + c` distributes into the sum, over the subsets `s` of the
`a`-positions, of the products in which exactly the positions in `s` carry `c` instead of `a`. The
factors stay in their original positions, so — unlike `Finset.prod_add` — no commutativity is used
and the identity holds in any semiring. -/
theorem wordProdList_add (w : List (Fin 2)) (a c b : 𝔸) :
    wordProdList ![a + c, b] w
      = ∑ s ∈ (wordAPositions w).powerset, wordProdList ![a, c, b] (wordSubstA w s) := by
  rw [wordProdList_eq_prod_map]
  induction w using List.reverseRecOn with
  | nil => simp [wordAPositions, wordSubstA, wordProdList_eq_prod_map]
  | append_singleton l k ih =>
      have hsub : ∀ s ∈ (wordAPositions l).powerset, s ⊆ wordAPositions l := fun s hs =>
        Finset.mem_powerset.mp hs
      have hlast : ∀ s ∈ (wordAPositions l).powerset, l.length ∉ s := fun s hs h =>
        length_notMem_wordAPositions l (hsub s hs h)
      have hk2 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      obtain rfl | rfl := hk2
      · rw [prod_map_concat_zero, ih, wordAPositions_concat_zero,
          Finset.sum_powerset_insert (length_notMem_wordAPositions l), mul_add, Finset.sum_mul,
          Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun s hs => ?_
          have hxer : s.erase l.length = s := Finset.erase_eq_of_notMem (hlast s hs)
          rw [wordSubstA_concat_zero, hxer, wordProdList_eq_prod_map, wordProdList_eq_prod_map]
          simp [hlast s hs]
        · refine Finset.sum_congr rfl fun s hs => ?_
          have hiner : (insert l.length s).erase l.length = s :=
            Finset.erase_insert (hlast s hs)
          rw [wordSubstA_concat_zero, hiner, wordProdList_eq_prod_map, wordProdList_eq_prod_map]
          simp
      · rw [prod_map_concat_one, ih, wordAPositions_concat_one, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hxer : s.erase l.length = s := Finset.erase_eq_of_notMem (hlast s hs)
        rw [wordSubstA_concat_one, hxer, wordProdList_eq_prod_map, wordProdList_eq_prod_map]
        simp [hlast s hs]

/-- A `List`-map is a range-indexed map of `getElem?`: the two ways of reading a word letter by
letter agree. -/
private lemma map_eq_range_map_getElem? {α β : Type*} [Inhabited α] (w : List α) (f : α → β) :
    w.map f = (List.range w.length).map fun j => f ((w[j]?).getD default) := by
  induction w with
  | nil => simp
  | cons k t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_map,
        List.getElem?_cons_zero, Option.getD_some, ih]
      refine congrArg (List.cons (f k)) ?_
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, List.getElem?_cons_succ]

/-- The empty substitution is the original word over the two-letter alphabet: substituting `V` for
no `a`-position leaves the letters where they were. This is what lets the `s = ∅` term of
`wordProdList_add` be cancelled against the unsubstituted word. -/
lemma wordProdList_substA_empty (w : List (Fin 2)) (x V y : 𝔸) :
    wordProdList ![x, y] w = wordProdList ![x, V, y] (wordSubstA w ∅) := by
  rw [wordProdList_eq_prod_map, wordProdList_eq_prod_map, map_eq_range_map_getElem? w ![x, y],
    wordSubstA, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j hj => ?_)
  have hjn : j < w.length := List.mem_range.mp hj
  simp only [Function.comp_apply]
  cases hw : w[j]? with
  | none => exact absurd hjn (by have := List.getElem?_eq_none_iff.mp hw; lia)
  | some k =>
      have hk2 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      obtain rfl | rfl := hk2 <;> simp

end Distributing

end FQFP.BCH
