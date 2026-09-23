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

* `wordEval letters v` — the product of the letters of the word `v`, read through `letters`.
* `norm_prod_map_le` — a word whose letters are bounded by `b` has norm at most `∏ b`.
* `norm_sum_smul_prod_map_le` — **the group lemma**: a `ℚ`-weighted sum of `m` such words is
  bounded by `m * cb * B`.

## Implementation notes

A word pattern is data, and the alphabet is a *type*: words are `Fin n → κ` (or `List κ`), and a
`Fin 2`-valued pattern means a word on the two letters `a`, `b`. There is no `Bool`-valued pattern
and no `if`-ladder: the letter at a position is the pattern entry itself, read through
`letters : κ → 𝔸`. This is what lets one API serve both the binary expansion (`κ := Fin 2`) and the
ternary one produced by `wordSubstA` (`κ := Fin 3`).

The word product has no bespoke definition either — `wordEval` is an `abbrev` for
`((List.ofFn v).map letters).prod`, so `List.prod_cons`, `List.prod_nil`, `List.prod_append` and
`List.norm_prod_le` are the library behind it. Contrast the hand-unrolled
`norm_bchQuinticGroup*_le` in `BCHTerms.lean`, which write out one `norm_word5_le` call per word
plus a `norm_add_le` step per summand.
-/

@[expose] public section

open Finset

namespace FQFP.BCH

/-! ### Words over an arbitrary alphabet

`wordEval` is the single evaluation: read every letter of the word through `letters` and multiply.
It is an `abbrev`, so it stays transparent — a goal never *contains* `wordEval`, only the
`List.map`/`List.prod` it stands for, and a literal pattern therefore reduces with the ordinary
`List` simp lemmas. -/

/-- Evaluate a word: read every letter through `letters` and take the product.

The `[Monoid 𝔸]` binder belongs here rather than at the use site: unlike a `def`, an `abbrev`'s
body is elaborated eagerly and has no signature to draw the instance from. -/
abbrev wordEval {n : ℕ} {κ 𝔸 : Type*} [Monoid 𝔸] (letters : κ → 𝔸) (v : Fin n → κ) : 𝔸 :=
  ((List.ofFn v).map letters).prod

section Bounds

variable {κ 𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- Letter-wise norm bound: if the letter `k` has norm at most `b k`, then the product of the
letters occurring in the pattern `w` has norm at most the product of their bounds.

This is not `List.norm_prod_le`, which bounds `‖(List.ofFn w).prod‖` by `∏ i, ‖w i‖` and so says
nothing when only a *family* of letter bounds is available; here the bounds are pushed through
`List.map` first. -/
lemma norm_prod_map_le (letters : κ → 𝔸) {b : κ → ℝ} (hb : ∀ k, ‖letters k‖ ≤ b k)
    (w : List κ) : ‖(w.map letters).prod‖ ≤ (w.map b).prod := by
  induction w with
  | nil => simp
  | cons k t ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      calc ‖letters k * (List.map letters t).prod‖
          ≤ ‖letters k‖ * ‖(List.map letters t).prod‖ := norm_mul_le _ _
        _ ≤ b k * (List.map b t).prod :=
            mul_le_mul (hb k) ih (norm_nonneg _) (le_trans (norm_nonneg _) (hb k))

/-- A product of a constant is that constant raised to the length. -/
private lemma prod_map_const {κ : Type*} {𝔸 : Type*} [Monoid 𝔸] (w : List κ) (x : 𝔸) :
    (w.map fun _ => x).prod = x ^ w.length := by
  induction w with
  | nil => simp
  | cons k t ih => rw [List.length_cons, List.map_cons, List.prod_cons, ih, pow_succ']

/-- **The uniform word bound** for a binary word: the norm of a word on `{a, b}` is at most
`(‖a‖ + ‖b‖) ^ n`. This is `norm_prod_map_le` at the constant family `b := fun _ => ‖a‖ + ‖b‖`. -/
lemma norm_binWord_le {n : ℕ} (v : Fin n → Fin 2) (a b : 𝔸) :
    ‖wordEval ![a, b] v‖ ≤ (‖a‖ + ‖b‖) ^ n := by
  have h := norm_prod_map_le (![a, b] : Fin 2 → 𝔸)
    (b := fun _ : Fin 2 => ‖a‖ + ‖b‖) (fun k => by
      fin_cases k
      · simp [le_add_of_nonneg_right (norm_nonneg b)]
      · simp [le_add_of_nonneg_left (norm_nonneg a)]) (List.ofFn v)
  rw [prod_map_const (List.ofFn v) (‖a‖ + ‖b‖), List.length_ofFn] at h
  simpa [wordEval, List.map_ofFn] using h

end Bounds

/-- **The group lemma**: an `ι`-indexed `ℚ`-weighted expansion in words over an alphabet `κ` is
bounded by `card ι * cb * B` as soon as every coefficient has norm at most `cb`, every word has
norm at most `B`, and `cb` is nonnegative.

A group of the quintic term is the case `ι = Fin m` with the words as data, so its bound becomes one
application of this lemma instead of `m` per-word estimates and `m - 1` triangle steps. -/
lemma norm_sum_smul_prod_map_le {ι κ : Type*} [Fintype ι] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] (c : ι → ℚ) (letters : κ → 𝔸) (w : ι → List κ)
    {B cb : ℝ} (hc : ∀ i, ‖c i‖ ≤ cb) (hw : ∀ i, ‖((w i).map letters).prod‖ ≤ B)
    (hcb : 0 ≤ cb) :
    ‖∑ i, c i • ((w i).map letters).prod‖ ≤ (Fintype.card ι : ℝ) * cb * B := by
  calc ‖∑ i, c i • ((w i).map letters).prod‖
      ≤ ∑ i, ‖c i • ((w i).map letters).prod‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, cb * B := Finset.sum_le_sum fun i _ => by
        calc ‖c i • ((w i).map letters).prod‖
            ≤ ‖c i‖ * ‖((w i).map letters).prod‖ := norm_smul_le _ _
          _ ≤ cb * B := mul_le_mul (hc i) (hw i) (norm_nonneg _) hcb
    _ = (Fintype.card ι : ℝ) * (cb * B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * cb * B := by ring

/-- **The alphabet-free group bound**: an `ι`-indexed `ℚ`-weighted sum of words over an alphabet `κ`
is bounded by `card ι * cb * B` as soon as every coefficient has norm at most `cb`, every word has
norm at most `B`, and `cb` is nonnegative.

This is `norm_sum_smul_prod_map_le` spelled with the `wordEval` abbreviation. -/
lemma norm_sum_smul_wordEval_le {ι κ : Type*} [Fintype ι] {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] {n : ℕ} (c : ι → ℚ) (letters : κ → 𝔸) (v : ι → Fin n → κ)
    {B cb : ℝ} (hc : ∀ i, ‖c i‖ ≤ cb) (hw : ∀ i, ‖wordEval letters (v i)‖ ≤ B)
    (hcb : 0 ≤ cb) :
    ‖∑ i, c i • wordEval letters (v i)‖ ≤ (Fintype.card ι : ℝ) * cb * B :=
  norm_sum_smul_prod_map_le c letters (fun i => List.ofFn (v i)) hc
    (fun i => by simpa [wordEval] using hw i) hcb

/-! ### The unweighted group bound -/

section GroupBound

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-- **The group bound**: an `ι`-indexed expansion in `n`-letter words on `{a, b}` is bounded by
`card ι * (‖a‖ + ‖b‖) ^ n`. This is `norm_sum_smul_prod_map_le` at coefficient `1` and bound
`(‖a‖ + ‖b‖) ^ n`, and it is what a group of equally weighted words (such as the four
`bchQuinticGroup*` of `BCHTerms.lean`) needs. -/
theorem norm_sum_wordEval_le {ι : Type*} [Fintype ι] {n : ℕ} (v : ι → Fin n → Fin 2)
    (a b : 𝔸) :
    ‖∑ i, wordEval ![a, b] (v i)‖ ≤ (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by
  calc ‖∑ i, wordEval ![a, b] (v i)‖
      ≤ ∑ i, ‖wordEval ![a, b] (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (‖a‖ + ‖b‖) ^ n :=
        Finset.sum_le_sum fun i _ => norm_binWord_le (v i) a b
    _ = (Fintype.card ι : ℝ) * (‖a‖ + ‖b‖) ^ n := by simp

end GroupBound

/-! ### Homogeneity of a word expansion -/

section Homogeneity

variable {𝕂 : Type*} [NormedField 𝕂]
variable {κ 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Scaling every letter scales every letter of the word. -/
theorem prod_map_smul (letters : κ → 𝔸) (w : List κ) (c : 𝕂) :
    (w.map fun k => c • letters k).prod = c ^ w.length • (w.map letters).prod := by
  cases w with
  | nil => simp
  | cons k t =>
      simp only [List.length_cons, List.map_cons, List.prod_cons]
      rw [prod_map_smul letters t c, pow_succ', smul_mul_assoc, mul_smul_comm, smul_smul]

/-- Homogeneity of a word expansion: scaling every letter by `c` scales the `ι`-indexed sum of
`n`-letter word products by `c ^ n`. -/
theorem sum_prod_map_smul {ι : Type*} [Fintype ι] {n : ℕ} (letters : κ → 𝔸)
    (v : ι → Fin n → κ) (c : 𝕂) :
    (∑ i, wordEval (fun k => c • letters k) (v i)) = c ^ n • ∑ i, wordEval letters (v i) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show wordEval (fun k => c • letters k) (v i)
        = ((List.ofFn (v i)).map fun k => c • letters k).prod from rfl,
    prod_map_smul letters (List.ofFn (v i)) c, List.length_ofFn]

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

/-! ### Distributing a sum over a binary word

`Finset.prod_add` — and every lemma of its family — is `CommSemiring`-only, because its right-hand
side collects all the `f`-factors at the front. For a noncommutative multiplication that identity
is simply false. BCH's `𝔸` is a general `NormedRing`, so the expansion of a word product has to
keep the letters in place.

`prod_map_add` does that. It is proved by induction on the word from the *left*
(`List.reverseRecOn`): appending one letter leaves the position indices of the prefix unchanged, so
the subsets of positions carry over verbatim. Every product step is `List.prod_append`, which needs
no commutativity; the `Finset` steps only ever concern sums, which are commutative anyway. -/

section Distributing

variable {𝔸 : Type*} [Semiring 𝔸]

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
theorem prod_map_add (w : List (Fin 2)) (a c b : 𝔸) :
    (w.map ![a + c, b]).prod
      = ∑ s ∈ (wordAPositions w).powerset, ((wordSubstA w s).map ![a, c, b]).prod := by
  induction w using List.reverseRecOn with
  | nil => simp [wordAPositions, wordSubstA]
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
          rw [wordSubstA_concat_zero, hxer]
          simp [hlast s hs]
        · refine Finset.sum_congr rfl fun s hs => ?_
          have hiner : (insert l.length s).erase l.length = s :=
            Finset.erase_insert (hlast s hs)
          rw [wordSubstA_concat_zero, hiner]
          simp
      · rw [prod_map_concat_one, ih, wordAPositions_concat_one, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hxer : s.erase l.length = s := Finset.erase_eq_of_notMem (hlast s hs)
        rw [wordSubstA_concat_one, hxer]
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
`prod_map_add` be cancelled against the unsubstituted word. -/
lemma prod_map_substA_empty (w : List (Fin 2)) (x V y : 𝔸) :
    (w.map ![x, y]).prod = ((wordSubstA w ∅).map ![x, V, y]).prod := by
  rw [map_eq_range_map_getElem? w ![x, y], wordSubstA, List.map_map]
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
