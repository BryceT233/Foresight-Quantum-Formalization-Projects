/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Terms
public import FQFP.BCH.Algebra.WordTaylor

/-!
# The Taylor expansion of the degree-5 term

`bchQuinticTerm (x + V) y - bchQuinticTerm x y` splits into its directional derivative
(`bchQuinticTermLinDiff`, linear in `V`) and a second-order remainder
(`bchQuinticTermTaylor2Remainder`), and the remainder splits further by the number of `V` letters
(`bchQuinticTermTaylor2Remainder{2V,3V,4V}`).

## How the split is organised

`bchQuinticTerm a b` is `(1/720)` times a combination of **four groups** of binary words, and every
one of those words has at most four letters `a`. Replacing `a` by `a + V` therefore expands, by
`prod_word_update_add`, into the sum over the *subsets* of the word's `a`-positions; each
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
  ∑ i : Fin m, ∑ s ∈ (wordPositions (words i) 0).powersetCard k,
    (List.ofFn (s.piecewise (fun _ => V) (fun j => ![x, y] (words i j)))).prod

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

/-- Every word of `bchQuinticTerm`'s coefficient-1 group has at most four letters `a`. -/
private lemma card_group1 (i : Fin 4) :
    (wordPositions (bchQuinticGroup1Words i) 0).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-4 group has at most four letters `a`. -/
private lemma card_group4 (i : Fin 10) :
    (wordPositions (bchQuinticGroup4Words i) 0).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-6 group has at most four letters `a`. -/
private lemma card_group6 (i : Fin 14) :
    (wordPositions (bchQuinticGroup6Words i) 0).card ≤ 4 := by
  fin_cases i <;> decide

/-- Every word of `bchQuinticTerm`'s coefficient-24 group has at most four letters `a`. -/
private lemma card_group24 (i : Fin 2) :
    (wordPositions (bchQuinticGroup24Words i) 0).card ≤ 4 := by
  fin_cases i <;> decide

/-! ### The algebraic bookkeeping -/

/-- `bchQuinticTerm` is its bracket at `(1/720)`. -/
private lemma bchQuinticTerm_eq_bracket [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
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
    (hcard : ∀ i : Fin m, (wordPositions (words i) 0).card ≤ 4) (x V y : 𝔸) :
    (∑ i : Fin m, ((List.ofFn (words i)).map ![x + V, y]).prod)
      = ∑ k ∈ Finset.range 5, bchQuinticGroupSubsets words k x V y := by
  have hu : Function.update (![x, y] : Fin 2 → 𝔸) 0 (x + V) = ![x + V, y] := by
    ext j
    fin_cases j <;> simp
  calc
    _ = ∑ i : Fin m, ∑ k ∈ Finset.range 5,
        wordTaylorPiece (words i) 0 ![x, y] V k :=
      Finset.sum_congr rfl fun i _ ↦ by
        simpa only [Matrix.cons_val_zero, hu, wordEval] using
          word_update_add_eq_sum_taylorPiece (words i) 0 ![x, y] V (hcard i)
    _ = _ := by
      rw [Finset.sum_comm]
      rfl

/-- **`bchQuinticTerm` at `x + V` is the sum of its subset pieces.** -/
theorem bchQuinticTerm_add_eq_sum_pieces [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticTerm (x + V) y = ∑ k ∈ Finset.range 5, bchQuinticSubsetPiece k x V y := by
  rw [bchQuinticTerm_eq_bracket, sum_pieces_eq, bchQuinticGroup1, bchQuinticGroup4,
    bchQuinticGroup6, bchQuinticGroup24,
    group_add_eq_sum_subsets _ card_group1, group_add_eq_sum_subsets _ card_group4,
    group_add_eq_sum_subsets _ card_group6, group_add_eq_sum_subsets _ card_group24,
    bracket_sum]

/-- **The `k = 0` piece is `bchQuinticTerm` itself**: substituting `V` at no position leaves the
word alone. -/
theorem bchQuinticSubsetPiece_zero [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticSubsetPiece 0 x V y = bchQuinticTerm x y := by
  simp only [bchQuinticSubsetPiece, bchQuinticGroupSubsets, Finset.powersetCard_zero,
    Finset.sum_singleton, Finset.piecewise_empty, bchQuinticTerm, bchQuinticBracket,
    bchQuinticGroup1, bchQuinticGroup4, bchQuinticGroup6, bchQuinticGroup24,
    wordEval, List.map_ofFn, Function.comp_def]

/-! ### The matching identity -/

/-- **Second-order Taylor matching identity for `bchQuinticTerm`**:

    bchQuinticTerm (x + V) y - bchQuinticTerm x y
      = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y.

The pieces are indexed by how many of the word's `x`-letters became `V`, so the split isolates the
linear-in-`V` part from the remainder, every term of which carries at least two factors of `V`.
This is what makes the `‖·‖ ≤ K · M³ · ‖V‖²` bound possible. -/
theorem bchQuinticTermTaylor2Decomp [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticTerm (x + V) y - bchQuinticTerm x y
      = bchQuinticTermLinDiff x V y + bchQuinticTermTaylor2Remainder x V y := by
  rw [bchQuinticTerm_add_eq_sum_pieces, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    bchQuinticSubsetPiece_zero]
  unfold bchQuinticTermLinDiff bchQuinticTermTaylor2Remainder bchQuinticTermTaylor2Remainder2V
    bchQuinticTermTaylor2Remainder3V bchQuinticTermTaylor2Remainder4V
  abel

end

end FQFP.BCH
