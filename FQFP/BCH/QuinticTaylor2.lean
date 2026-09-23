/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms
public import FQFP.BCH.WordExpansion

/-!
# The Taylor expansion of the degree-5 term

`bchQuinticTerm (x + V) y - bchQuinticTerm x y` splits into its directional derivative
(`bchQuinticTermLinDiff`, linear in `V`) and a second-order remainder
(`bchQuinticTermTaylor2Remainder`), and the remainder splits further by the number of `V` letters
(`bchQuinticTermTaylor2Remainder{2V,3V,4V}`).

## How the split is organised

`bchQuinticTerm a b` is `(1/720)` times a combination of **four groups** of binary words, and every
one of those words has at most four letters `a`. Replacing `a` by `a + V` therefore expands, by
`WordExpansion.prod_map_add`, into the sum over the *subsets* of the word's `a`-positions; each
subset records which of the `x`-letters became `V`. Grouping those subsets by their cardinality `k`
gives one piece per `k`:

* `k = 0` is the word unchanged, i.e. `bchQuinticTerm x y` itself;
* `k = 1` is the linear part (`bchQuinticTermLinDiff`);
* `k ≥ 2` is the second-order remainder, and the number of letters `V` in a substituted word is
  exactly `k`, which is what makes the pieces `{2V,3V,4V}`.

So the pieces are **defined by the same `∑ i, ∑ s` shape that the expansion produces**, and
`bchQuinticTermTaylor2Decomp` becomes a rearrangement of `Finset.sum`s rather than a noncommutative
polynomial identity: no `noncomm_ring`, and no heartbeat bump. The uniform cardinality `k` is also
what lets each piece be bounded by `(number of subsets) * (largest coefficient) * M^(5-k) * ‖V‖^k`,
which relaxes to the source's constant via `‖V‖ ≤ M`.

## Provenance

Ported from `Lean-BCH/BCH/Basic.lean:3028-4830`. The source presents both sides as explicit
`+`-chains of monomials and closes the identity with `match_scalars <;> ring` under
`maxHeartbeats 1024000000`; see `artifacts/quintic-taylor2-route.md` for why that presentation is
not available here. The source constant of the remainder is `(1680 + 720 + 30)/720 = 2430/720`, the
sum of the three pieces' constants.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open Finset

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*}

/-! ### The subset pieces -/

/-- The signed combination of the four groups of `bchQuinticTerm`, at their coefficients
`-1`, `4`, `-6`, `24`. -/
def bchQuinticBracket [Ring 𝔸] [Algebra ℚ 𝔸] (v1 v4 v6 v24 : 𝔸) : 𝔸 :=
  -v1 + (4 : ℚ) • v4 - (6 : ℚ) • v6 + (24 : ℚ) • v24

/-- **The `k`-subset piece of one group**: for each word of the group, the sum, over the subsets
`s` of size `k` of its `a`-positions, of the word obtained by substituting `V` at the positions in
`s`. Reading the result over `![x, V, y]` gives the words of the Taylor expansion that carry
exactly `k` letters `V`. -/
def bchQuinticGroupSubsets [Semiring 𝔸] {m : ℕ} (words : Fin m → Fin 5 → Fin 2) (k : ℕ)
    (x V y : 𝔸) : 𝔸 :=
  ∑ i : Fin m, ∑ s ∈ (wordAPositions (List.ofFn (words i))).powersetCard k,
    ((wordSubstA (List.ofFn (words i)) s).map ![x, V, y]).prod

/-- **The `k`-th piece of the degree-5 Taylor expansion**: the four groups of `bchQuinticTerm` at
their coefficients, with every word replaced by its `k`-subset piece. -/
def bchQuinticSubsetPiece [Ring 𝔸] [Algebra ℚ 𝔸] (k : ℕ) (x V y : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • bchQuinticBracket
    (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)

/-- **First-order directional difference** of `bchQuinticTerm` in its first argument: the pieces in
which exactly one `x`-letter became `V`. -/
def bchQuinticTermLinDiff [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchQuinticSubsetPiece 1 x V y

/-- The `2V` piece of the second-order Taylor remainder: exactly two letters `V`. -/
def bchQuinticTermTaylor2Remainder2V [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchQuinticSubsetPiece 2 x V y

/-- The `3V` piece of the second-order Taylor remainder: exactly three letters `V`. -/
def bchQuinticTermTaylor2Remainder3V [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchQuinticSubsetPiece 3 x V y

/-- The `4V` piece of the second-order Taylor remainder: exactly four letters `V`. -/
def bchQuinticTermTaylor2Remainder4V [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchQuinticSubsetPiece 4 x V y

/-- **Second-order Taylor remainder** of `bchQuinticTerm` in its first argument: the pieces in
which at least two `x`-letters became `V`. The split by the number of `V` letters is part of the
definition, so the split identity is `rfl`. -/
def bchQuinticTermTaylor2Remainder [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) : 𝔸 :=
  bchQuinticTermTaylor2Remainder2V x V y + bchQuinticTermTaylor2Remainder3V x V y +
    bchQuinticTermTaylor2Remainder4V x V y

/-! ### The combinatorial bookkeeping -/

/-- **Splitting a powerset by cardinality**: when every subset has at most four elements, the sum
over the powerset is the sum of the sums over the subsets of size `0`, `1`, `2`, `3`, `4`. -/
private lemma sum_powerset_eq_sum_powersetCard {α β : Type*} [AddCommMonoid β]
    {s : Finset α} (h : s.card ≤ 4) (f : Finset α → β) :
    ∑ t ∈ s.powerset, f t = ∑ k ∈ Finset.range 5, ∑ t ∈ s.powersetCard k, f t := by
  classical
  refine (Finset.sum_fiberwise_of_maps_to (s := s.powerset) (t := Finset.range 5)
    (g := Finset.card) ?_ f).symm.trans ?_
  · intro t ht
    simp only [Finset.mem_range]
    have := Finset.card_le_card (Finset.mem_powerset.mp ht)
    lia
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.powersetCard_eq_filter]

/-- Every word of `bchQuinticTerm`'s coefficient-1 group has at most four letters `a`. -/
private lemma card_group1 (i : Fin 4) :
    (wordAPositions (List.ofFn (bchQuinticGroup1Words i))).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-4 group has at most four letters `a`. -/
private lemma card_group4 (i : Fin 10) :
    (wordAPositions (List.ofFn (bchQuinticGroup4Words i))).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-6 group has at most four letters `a`. -/
private lemma card_group6 (i : Fin 14) :
    (wordAPositions (List.ofFn (bchQuinticGroup6Words i))).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-24 group has at most four letters `a`. -/
private lemma card_group24 (i : Fin 2) :
    (wordAPositions (List.ofFn (bchQuinticGroup24Words i))).card ≤ 4 := by
  fin_cases i <;> decide

/-! ### The algebraic bookkeeping -/

/-- `bchQuinticTerm` is its bracket at `(1/720)`. -/
private lemma bchQuinticTerm_eq_bracket [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    bchQuinticTerm a b = (720 : ℚ)⁻¹ • bchQuinticBracket
      (bchQuinticGroup1 a b) (bchQuinticGroup4 a b) (bchQuinticGroup6 a b)
      (bchQuinticGroup24 a b) := rfl

/-- The bracket of four sums is the sum of the brackets. -/
private lemma bracket_sum [Ring 𝔸] [Algebra ℚ 𝔸] {ι : Type*} {s : Finset ι} (A B C D : ι → 𝔸) :
    bchQuinticBracket (∑ k ∈ s, A k) (∑ k ∈ s, B k) (∑ k ∈ s, C k) (∑ k ∈ s, D k)
      = ∑ k ∈ s, bchQuinticBracket (A k) (B k) (C k) (D k) := by
  simp only [bchQuinticBracket, Finset.smul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]

/-- The sum of the pieces is `(1/720)` times the sum of the brackets. -/
private lemma sum_pieces_eq [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    ∑ k ∈ Finset.range 5, bchQuinticSubsetPiece k x V y
      = (720 : ℚ)⁻¹ • ∑ k ∈ Finset.range 5, bchQuinticBracket
          (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y) := by
  unfold bchQuinticSubsetPiece
  rw [Finset.smul_sum]

/-! ### The group expansion -/

/-- **One group, fully expanded**: replacing `a` by `a + V` in a group of words distributes into
the sum, over the size `k` of the substituted position set, of the group's `k`-subset pieces. -/
private lemma group_add_eq_sum_subsets [Semiring 𝔸] {m : ℕ} (words : Fin m → Fin 5 → Fin 2)
    (hcard : ∀ i : Fin m, (wordAPositions (List.ofFn (words i))).card ≤ 4) (x V y : 𝔸) :
    (∑ i : Fin m, ((List.ofFn (words i)).map ![x + V, y]).prod)
      = ∑ k ∈ Finset.range 5, bchQuinticGroupSubsets words k x V y := by
  calc ∑ i : Fin m, ((List.ofFn (words i)).map ![x + V, y]).prod
      = ∑ i : Fin m, ∑ s ∈ (wordAPositions (List.ofFn (words i))).powerset,
          ((wordSubstA (List.ofFn (words i)) s).map ![x, V, y]).prod :=
        Finset.sum_congr rfl fun i _ => prod_map_add (List.ofFn (words i)) x V y
    _ = ∑ i : Fin m, ∑ k ∈ Finset.range 5,
          ∑ s ∈ (wordAPositions (List.ofFn (words i))).powersetCard k,
            ((wordSubstA (List.ofFn (words i)) s).map ![x, V, y]).prod :=
        Finset.sum_congr rfl fun i _ => sum_powerset_eq_sum_powersetCard (hcard i) _
    _ = ∑ k ∈ Finset.range 5, bchQuinticGroupSubsets words k x V y := by
        rw [Finset.sum_comm]
        rfl

/-- **`bchQuinticTerm` at `x + V` is the sum of its subset pieces.** -/
theorem bchQuinticTerm_add_eq_sum_pieces [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticTerm (x + V) y = ∑ k ∈ Finset.range 5, bchQuinticSubsetPiece k x V y := by
  have h1 : bchQuinticGroup1 (x + V) y
      = ∑ i : Fin 4, ((List.ofFn (bchQuinticGroup1Words i)).map ![x + V, y]).prod := by
    unfold bchQuinticGroup1
    simp only [wordEval, List.map_ofFn]
  have h4 : bchQuinticGroup4 (x + V) y
      = ∑ i : Fin 10,
          ((List.ofFn (bchQuinticGroup4Words i)).map ![x + V, y]).prod := by
    unfold bchQuinticGroup4
    simp only [wordEval, List.map_ofFn]
  have h6 : bchQuinticGroup6 (x + V) y
      = ∑ i : Fin 14,
          ((List.ofFn (bchQuinticGroup6Words i)).map ![x + V, y]).prod := by
    unfold bchQuinticGroup6
    simp only [wordEval, List.map_ofFn]
  have h24 : bchQuinticGroup24 (x + V) y
      = ∑ i : Fin 2,
          ((List.ofFn (bchQuinticGroup24Words i)).map ![x + V, y]).prod := by
    unfold bchQuinticGroup24
    simp only [wordEval, List.map_ofFn]
  rw [bchQuinticTerm_eq_bracket, sum_pieces_eq, h1, h4, h6, h24,
    group_add_eq_sum_subsets _ card_group1, group_add_eq_sum_subsets _ card_group4,
    group_add_eq_sum_subsets _ card_group6, group_add_eq_sum_subsets _ card_group24,
    bracket_sum]

/-- **The `k = 0` piece is `bchQuinticTerm` itself**: substituting `V` at no position leaves the
word alone. -/
theorem bchQuinticSubsetPiece_zero [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticSubsetPiece 0 x V y = bchQuinticTerm x y := by
  have h1 : bchQuinticGroupSubsets bchQuinticGroup1Words 0 x V y = bchQuinticGroup1 x y := by
    unfold bchQuinticGroupSubsets bchQuinticGroup1
    simp only [wordEval, List.map_ofFn, Finset.powersetCard_zero, Finset.sum_singleton]
    rfl
  have h4 : bchQuinticGroupSubsets bchQuinticGroup4Words 0 x V y = bchQuinticGroup4 x y := by
    unfold bchQuinticGroupSubsets bchQuinticGroup4
    simp only [wordEval, List.map_ofFn, Finset.powersetCard_zero, Finset.sum_singleton]
    rfl
  have h6 : bchQuinticGroupSubsets bchQuinticGroup6Words 0 x V y = bchQuinticGroup6 x y := by
    unfold bchQuinticGroupSubsets bchQuinticGroup6
    simp only [wordEval, List.map_ofFn, Finset.powersetCard_zero, Finset.sum_singleton]
    rfl
  have h24 : bchQuinticGroupSubsets bchQuinticGroup24Words 0 x V y = bchQuinticGroup24 x y := by
    unfold bchQuinticGroupSubsets bchQuinticGroup24
    simp only [wordEval, List.map_ofFn, Finset.powersetCard_zero, Finset.sum_singleton]
    rfl
  rw [bchQuinticSubsetPiece, bchQuinticTerm_eq_bracket, h1, h4, h6, h24]

/-! ### The matching identity -/

/-- **Second-order Taylor matching identity for `bchQuinticTerm`**:

    bchQuinticTerm (x + V) y - bchQuinticTerm x y
      = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y.

The pieces are indexed by how many of the word's `x`-letters became `V`, so the split isolates the
linear-in-`V` part from the remainder, every term of which carries at least two factors of `V`.
This is what makes the `‖·‖ ≤ K · M³ · ‖V‖²` bound possible. -/
theorem bchQuinticTermTaylor2Decomp [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticTerm (x + V) y - bchQuinticTerm x y
      = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y := by
  rw [bchQuinticTerm_add_eq_sum_pieces, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    bchQuinticSubsetPiece_zero]
  unfold bchQuinticTermLinDiff bchQuinticTermTaylor2Remainder bchQuinticTermTaylor2Remainder2V
    bchQuinticTermTaylor2Remainder3V bchQuinticTermTaylor2Remainder4V
  abel

/-! ### The norm bounds

Each piece is bounded in three steps, none of which needs a case analysis on the words:

1. every substituted word of the `k`-th piece carries exactly `k` letters `V` and `5 - k` letters
   from `{x, y}`, so `WordExpansion.norm_prod_map_le` bounds it by `M ^ (5 - k) * Vn ^ k`;
2. the number of such words in a group is `∑ i, (#a-positions).choose k`, evaluated by `decide`;
3. `M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2` because `Vn ≤ M`.

The resulting constants (`384/720`, `136/720`, `16/720` for the three pieces) are sharper than the
source's `1680/720`, `720/720`, `30/720`, which are kept in the statements. -/

/-- **The profile product**: a product that reads `B` at the positions in `s` and `A` elsewhere is
`A ^ (n - s.card) * B ^ s.card`. This is where the letter count of a substituted word comes from. -/
private lemma prod_ite_range (s : Finset ℕ) (n : ℕ) (h : s ⊆ Finset.range n) (A B : ℝ) :
    ((List.range n).map fun j => if j ∈ s then B else A).prod = A ^ (n - s.card) * B ^ s.card := by
  induction n generalizing s with
  | zero =>
      have hs : s = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun j hj => ?_
        have := h hj
        simp at this
      simp [hs]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one]
      set s' := s.erase n with hs'
      have hsub : s' ⊆ Finset.range n := by
        intro j hj
        rw [Finset.mem_range]
        have hj' : j ∈ s := (Finset.mem_erase.mp hj).2
        have := h hj'
        rw [Finset.mem_range] at this
        exact lt_of_le_of_ne (Nat.le_of_lt_succ this) (Finset.mem_erase.mp hj).1
      have hle : s'.card ≤ n := by
        simpa [Finset.card_range] using Finset.card_le_card hsub
      have hmap : (List.range n).map (fun j => if j ∈ s then B else A)
          = (List.range n).map (fun j => if j ∈ s' then B else A) := by
        refine List.map_congr_left fun j hj => ?_
        have hjn : j ≠ n := by
          have := List.mem_range.mp hj
          lia
        have hiff : (j ∈ s') ↔ (j ∈ s) := by
          rw [hs', Finset.mem_erase]
          exact ⟨fun h => h.2, fun h => ⟨hjn, h⟩⟩
        by_cases hjs : j ∈ s
        · simp [hjs, hiff.mpr hjs]
        · have hjs' : j ∉ s' := fun hc => hjs (hiff.mp hc)
          simp [hjs, hjs']
      rw [hmap, ih s' hsub]
      by_cases hn : n ∈ s
      · have hcard : s'.card + 1 = s.card := by rw [hs', Finset.card_erase_add_one hn]
        have hexp : n + 1 - s.card = n - s'.card := by lia
        have hif : (if n ∈ s then B else A) = B := by simp [hn]
        rw [hif, hexp, ← hcard, pow_succ]
        ring
      · have hss : s' = s := Finset.erase_eq_of_notMem hn
        have hle' : s.card ≤ n := by
          have hs : s ⊆ Finset.range n := by
            intro j hj
            rw [Finset.mem_range]
            have := h hj
            rw [Finset.mem_range] at this
            exact lt_of_le_of_ne (Nat.le_of_lt_succ this) fun hc => hn (hc ▸ hj)
          simpa [Finset.card_range] using Finset.card_le_card hs
        have hexp : n + 1 - s.card = (n - s'.card) + 1 := by
          rw [hss]
          lia
        have hif : (if n ∈ s then B else A) = A := by simp [hn]
        rw [hif, hexp, hss, pow_succ]
        ring

/-- A position of `wordAPositions w` really carries the letter `a`. -/
private lemma getElem?_eq_some_zero_of_mem_wordAPositions {w : List (Fin 2)} {j : ℕ}
    (h : j ∈ wordAPositions w) : w[j]? = some 0 :=
  (Finset.mem_filter.mp h).2

/-- `wordAPositions` is a set of positions of `w`. -/
private lemma wordAPositions_subset_range (w : List (Fin 2)) :
    wordAPositions w ⊆ Finset.range w.length := by
  intro j hj
  rw [Finset.mem_range]
  by_contra hlt
  have hmem : w[j]? = some 0 := getElem?_eq_some_zero_of_mem_wordAPositions hj
  rw [List.getElem?_eq_none_iff.mpr (by lia)] at hmem
  exact absurd hmem (by simp)

/-- A substituted word has exactly `s.card` letters `V`, so its norm is at most
`M ^ (w.length - s.card) * Vn ^ s.card`. -/
private lemma norm_wordSubstA_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] (w : List (Fin 2))
    (s : Finset ℕ) (hsub : s ⊆ wordAPositions w) (x V y : 𝔸) {M Vn : ℝ} (hx : ‖x‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) :
    ‖((wordSubstA w s).map ![x, V, y]).prod‖ ≤ M ^ (w.length - s.card) * Vn ^ s.card := by
  have hletter : ∀ k : Fin 3, ‖![x, V, y] k‖ ≤ ![M, Vn, M] k := by
    intro k
    fin_cases k
    · simpa using hx
    · simpa using hV
    · simpa using hy
  refine le_trans (norm_prod_map_le ![x, V, y] hletter (wordSubstA w s)) ?_
  rw [wordSubstA, List.map_map]
  have hmap : (List.range w.length).map ((![M, Vn, M] : Fin 3 → ℝ) ∘
        fun j => if j ∈ s then 1 else if w[j]? = some 0 then 0 else 2)
      = (List.range w.length).map fun j => if j ∈ s then Vn else M := by
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    by_cases h : j ∈ s
    · simp [h]
    · by_cases hw : w[j]? = some 0 <;> simp [h, hw]
  rw [hmap, prod_ite_range s w.length (fun j hj => wordAPositions_subset_range w (hsub hj))]

/-- **The group bound**: a group's `k`-subset piece is bounded by its number of terms times
`M ^ (5 - k) * Vn ^ k`. -/
private lemma norm_bchQuinticGroupSubsets_le {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] {m : ℕ}
    (words : Fin m → Fin 5 → Fin 2) (k : ℕ) (x V y : 𝔸) {M Vn : ℝ} (hx : ‖x‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hy : ‖y‖ ≤ M) :
    ‖bchQuinticGroupSubsets words k x V y‖
      ≤ (∑ i : Fin m, (((wordAPositions (List.ofFn (words i))).card).choose k : ℝ))
          * (M ^ (5 - k) * Vn ^ k) := by
  have hlen : ∀ i : Fin m, (List.ofFn (words i)).length = 5 := fun i => by
    simp
  calc ‖bchQuinticGroupSubsets words k x V y‖
      ≤ ∑ i : Fin m, ∑ _s ∈ (wordAPositions (List.ofFn (words i))).powersetCard k,
          M ^ (5 - k) * Vn ^ k := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s hs => ?_)
        have hs' : s ⊆ wordAPositions (List.ofFn (words i)) :=
          (Finset.mem_powersetCard.mp hs).1
        have hsk : s.card = k := (Finset.mem_powersetCard.mp hs).2
        have := norm_wordSubstA_le (List.ofFn (words i)) s hs' x V y hx hV hy
        rw [hlen i, hsk] at this
        exact this
    _ = (∑ i : Fin m, (((wordAPositions (List.ofFn (words i))).card).choose k : ℝ))
          * (M ^ (5 - k) * Vn ^ k) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- **The bracket bound**: the four groups at their coefficients `-1`, `4`, `-6`, `24`. -/
private lemma norm_bchQuinticBracket_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    (v1 v4 v6 v24 : 𝔸) :
    ‖bchQuinticBracket v1 v4 v6 v24‖ ≤ ‖v1‖ + 4 * ‖v4‖ + 6 * ‖v6‖ + 24 * ‖v24‖ := by
  have h4 : ‖(4 : ℚ) • v4‖ ≤ 4 * ‖v4‖ := by
    calc ‖(4 : ℚ) • v4‖ ≤ ‖(4 : ℚ)‖ * ‖v4‖ := norm_smul_le _ _
      _ = 4 * ‖v4‖ := by simp [← Rat.norm_cast_real]
  have h6 : ‖(6 : ℚ) • v6‖ ≤ 6 * ‖v6‖ := by
    calc ‖(6 : ℚ) • v6‖ ≤ ‖(6 : ℚ)‖ * ‖v6‖ := norm_smul_le _ _
      _ = 6 * ‖v6‖ := by simp [← Rat.norm_cast_real]
  have h24 : ‖(24 : ℚ) • v24‖ ≤ 24 * ‖v24‖ := by
    calc ‖(24 : ℚ) • v24‖ ≤ ‖(24 : ℚ)‖ * ‖v24‖ := norm_smul_le _ _
      _ = 24 * ‖v24‖ := by simp [← Rat.norm_cast_real]
  have hA : ‖-v1 + (4 : ℚ) • v4‖ ≤ ‖v1‖ + 4 * ‖v4‖ := by
    calc ‖-v1 + (4 : ℚ) • v4‖ ≤ ‖-v1‖ + ‖(4 : ℚ) • v4‖ := norm_add_le _ _
      _ ≤ ‖v1‖ + 4 * ‖v4‖ := by rw [norm_neg]; linarith
  simp only [bchQuinticBracket]
  calc ‖-v1 + (4 : ℚ) • v4 - (6 : ℚ) • v6 + (24 : ℚ) • v24‖
      ≤ ‖-v1 + (4 : ℚ) • v4 - (6 : ℚ) • v6‖ + ‖(24 : ℚ) • v24‖ := norm_add_le _ _
    _ ≤ (‖-v1 + (4 : ℚ) • v4‖ + ‖(6 : ℚ) • v6‖) + ‖(24 : ℚ) • v24‖ := by
        have := norm_sub_le (-v1 + (4 : ℚ) • v4) ((6 : ℚ) • v6)
        linarith
    _ ≤ (‖v1‖ + 4 * ‖v4‖ + 6 * ‖v6‖) + 24 * ‖v24‖ := by linarith
    _ = ‖v1‖ + 4 * ‖v4‖ + 6 * ‖v6‖ + 24 * ‖v24‖ := by ring

/-- The relaxation `M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2` for `2 ≤ k ≤ 5`. -/
private lemma profile_le (M Vn : ℝ) (hM0 : 0 ≤ M) (hVn0 : 0 ≤ Vn) (hVnM : Vn ≤ M) {k : ℕ}
    (hk : 2 ≤ k) (hk5 : k ≤ 5) : M ^ (5 - k) * Vn ^ k ≤ M ^ 3 * Vn ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by lia⟩
  have hj3 : j ≤ 3 := by lia
  have hM : 5 - (j + 2) = 3 - j := by lia
  rw [hM, pow_add]
  calc M ^ (3 - j) * (Vn ^ j * Vn ^ 2)
      ≤ M ^ (3 - j) * (M ^ j * Vn ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hVn0 hVnM j) (pow_nonneg hVn0 2))
          (pow_nonneg hM0 (3 - j))
    _ = M ^ 3 * Vn ^ 2 := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj3]

/-- **The piece bound**: if the four groups of the `k`-th piece have `n1`, `n4`, `n6`, `n24` words
respectively and `(n1 + 4n4 + 6n6 + 24n24)/720 ≤ C`, then the piece is bounded by
`C * M ^ 3 * ‖V‖ ^ 2`. -/
private lemma norm_bchQuinticSubsetPiece_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] {k : ℕ} (hk : 2 ≤ k) (hk5 : k ≤ 5)
    {n1 n4 n6 n24 : ℕ}
    (hc1 : (∑ i : Fin 4,
      ((wordAPositions (List.ofFn (bchQuinticGroup1Words i))).card).choose k) = n1)
    (hc4 : (∑ i : Fin 10,
      ((wordAPositions (List.ofFn (bchQuinticGroup4Words i))).card).choose k) = n4)
    (hc6 : (∑ i : Fin 14,
      ((wordAPositions (List.ofFn (bchQuinticGroup6Words i))).card).choose k) = n6)
    (hc24 : (∑ i : Fin 2,
      ((wordAPositions (List.ofFn (bchQuinticGroup24Words i))).card).choose k) = n24)
    {C : ℝ} (hC : ((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) / 720 ≤ C) (x V y : 𝔸) :
    ‖bchQuinticSubsetPiece k x V y‖ ≤ C * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by
  set M := ‖x‖ + ‖V‖ + ‖y‖ with hM
  set Vn := ‖V‖ with hVn
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hVn0 : 0 ≤ Vn := norm_nonneg _
  have hVnM : Vn ≤ M := by rw [hM]; linarith [norm_nonneg x, norm_nonneg y]
  have hx : ‖x‖ ≤ M := by rw [hM]; linarith [norm_nonneg V, norm_nonneg y]
  have hV : ‖V‖ ≤ Vn := le_refl _
  have hy : ‖y‖ ≤ M := by rw [hM]; linarith [norm_nonneg x, norm_nonneg V]
  have h1 := norm_bchQuinticGroupSubsets_le bchQuinticGroup1Words k x V y hx hV hy
  have h4 := norm_bchQuinticGroupSubsets_le bchQuinticGroup4Words k x V y hx hV hy
  have h6 := norm_bchQuinticGroupSubsets_le bchQuinticGroup6Words k x V y hx hV hy
  have h24 := norm_bchQuinticGroupSubsets_le bchQuinticGroup24Words k x V y hx hV hy
  rw [show (∑ i : Fin 4, (((wordAPositions (List.ofFn (bchQuinticGroup1Words i))).card
      ).choose k : ℝ)) = n1 by rw [← Nat.cast_sum, hc1]] at h1
  rw [show (∑ i : Fin 10, (((wordAPositions (List.ofFn (bchQuinticGroup4Words i))).card
      ).choose k : ℝ)) = n4 by rw [← Nat.cast_sum, hc4]] at h4
  rw [show (∑ i : Fin 14, (((wordAPositions (List.ofFn (bchQuinticGroup6Words i))).card
      ).choose k : ℝ)) = n6 by rw [← Nat.cast_sum, hc6]] at h6
  rw [show (∑ i : Fin 2, (((wordAPositions (List.ofFn (bchQuinticGroup24Words i))).card
      ).choose k : ℝ)) = n24 by rw [← Nat.cast_sum, hc24]] at h24
  have hbr := norm_bchQuinticBracket_le (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
    (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)
  have hprof := profile_le M Vn hM0 hVn0 hVnM hk hk5
  have hX : (0 : ℝ) ≤ M ^ 3 * Vn ^ 2 := by positivity
  have h720 : ‖(720 : ℚ)⁻¹‖ = (720 : ℝ)⁻¹ := by
    rw [← Rat.norm_cast_real, Real.norm_eq_abs]
    norm_num
  have hsm : ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * ‖bchQuinticBracket
          (bchQuinticGroupSubsets bchQuinticGroup1Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup4Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup6Words k x V y)
          (bchQuinticGroupSubsets bchQuinticGroup24Words k x V y)‖ := by
    rw [bchQuinticSubsetPiece]
    refine le_trans (norm_smul_le _ _) ?_
    rw [h720]
  have key : ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2)) := by
    refine le_trans hsm (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have b1 : ‖bchQuinticGroupSubsets bchQuinticGroup1Words k x V y‖
        ≤ (n1 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n1))
    have b4 : ‖bchQuinticGroupSubsets bchQuinticGroup4Words k x V y‖
        ≤ (n4 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h4 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n4))
    have b6 : ‖bchQuinticGroupSubsets bchQuinticGroup6Words k x V y‖
        ≤ (n6 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h6 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n6))
    have b24 : ‖bchQuinticGroupSubsets bchQuinticGroup24Words k x V y‖
        ≤ (n24 : ℝ) * (M ^ 3 * Vn ^ 2) :=
      le_trans h24 (mul_le_mul_of_nonneg_left hprof (Nat.cast_nonneg n24))
    calc ‖bchQuinticBracket _ _ _ _‖
        ≤ ‖bchQuinticGroupSubsets bchQuinticGroup1Words k x V y‖
          + 4 * ‖bchQuinticGroupSubsets bchQuinticGroup4Words k x V y‖
          + 6 * ‖bchQuinticGroupSubsets bchQuinticGroup6Words k x V y‖
          + 24 * ‖bchQuinticGroupSubsets bchQuinticGroup24Words k x V y‖ := hbr
      _ ≤ (n1 : ℝ) * (M ^ 3 * Vn ^ 2) + 4 * ((n4 : ℝ) * (M ^ 3 * Vn ^ 2))
          + 6 * ((n6 : ℝ) * (M ^ 3 * Vn ^ 2)) + 24 * ((n24 : ℝ) * (M ^ 3 * Vn ^ 2)) := by
          linarith
      _ = ((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2) := by ring
  calc ‖bchQuinticSubsetPiece k x V y‖
      ≤ (720 : ℝ)⁻¹ * (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) * (M ^ 3 * Vn ^ 2)) := key
    _ = (((n1 : ℝ) + 4 * n4 + 6 * n6 + 24 * n24) / 720) * (M ^ 3 * Vn ^ 2) := by ring
    _ ≤ C * (M ^ 3 * Vn ^ 2) := mul_le_mul_of_nonneg_right hC hX
    _ = C * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) := by rw [hM, hVn]

/-- Norm bound for the `2V` piece: `≤ (1680/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder2V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder2V x V y‖
      ≤ (1680 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_bchQuinticSubsetPiece_le (𝔸 := 𝔸) (k := 2) (by norm_num) (by norm_num)
    (n1 := 12) (n4 := 24) (n6 := 30) (n24 := 4)
    (by decide) (by decide) (by decide) (by decide) (C := 1680 / 720) (by norm_num) x V y

/-- Norm bound for the `3V` piece: `≤ (720/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder3V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder3V x V y‖
      ≤ (720 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_bchQuinticSubsetPiece_le (𝔸 := 𝔸) (k := 3) (by norm_num) (by norm_num)
    (n1 := 8) (n4 := 11) (n6 := 10) (n24 := 1)
    (by decide) (by decide) (by decide) (by decide) (C := 720 / 720) (by norm_num) x V y

/-- Norm bound for the `4V` piece: `≤ (30/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`. -/
theorem norm_bchQuinticTermTaylor2Remainder4V_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder4V x V y‖
      ≤ (30 / 720 : ℝ) * ((‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2) :=
  norm_bchQuinticSubsetPiece_le (𝔸 := 𝔸) (k := 4) (by norm_num) (by norm_num)
    (n1 := 2) (n4 := 2) (n6 := 1) (n24 := 0)
    (by decide) (by decide) (by decide) (by decide) (C := 30 / 720) (by norm_num) x V y

/-- **Norm bound for the second-order Taylor remainder**:
`‖C₅(x+V,y) - C₅(x,y) - linDiff‖ ≤ (2430/720) M³‖V‖²` with `M = ‖x‖ + ‖V‖ + ‖y‖`.

`(1680 + 720 + 30)/720 = 2430/720` is the sum of the three pieces' constants. -/
theorem norm_bchQuinticTermTaylor2Remainder_le {𝔸 : Type*}
    [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] (x V y : 𝔸) :
    ‖bchQuinticTermTaylor2Remainder x V y‖ ≤
      (2430 / 720 : ℝ) * (‖x‖ + ‖V‖ + ‖y‖) ^ 3 * ‖V‖ ^ 2 := by
  have h2 := norm_bchQuinticTermTaylor2Remainder2V_le x V y
  have h3 := norm_bchQuinticTermTaylor2Remainder3V_le x V y
  have h4 := norm_bchQuinticTermTaylor2Remainder4V_le x V y
  have s1 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y +
    bchQuinticTermTaylor2Remainder3V x V y) (bchQuinticTermTaylor2Remainder4V x V y)
  have s2 := norm_add_le (bchQuinticTermTaylor2Remainder2V x V y)
    (bchQuinticTermTaylor2Remainder3V x V y)
  have hsum : (2430 / 720 : ℝ) = 1680 / 720 + 720 / 720 + 30 / 720 := by norm_num
  unfold bchQuinticTermTaylor2Remainder
  rw [hsum]
  linarith only [s1, s2, h2, h3, h4]

end

end FQFP.BCH
