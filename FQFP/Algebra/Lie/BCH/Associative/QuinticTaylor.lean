/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.Terms
public import FQFP.Algebra.Word.Taylor

/-!
# The Taylor expansion of the degree-5 term

`bchQuinticTerm (x + V) y - bchQuinticTerm x y` splits into its directional derivative
(`bchQuinticTermLinDiff`, linear in `V`) and a second-order remainder
(`bchQuinticTermTaylor2Remainder`), and the remainder splits further by the number of `V` letters
(`bchQuinticTermTaylor2Remainder{2V,3V,4V}`).

## Main definitions and results

* `FQFP.BCH.bchQuinticSubsetPiece` collects the terms with a prescribed number of substituted
  letters.
* `FQFP.BCH.bchQuinticTermLinDiff` collects the terms linear in the increment.
* `FQFP.BCH.bchQuinticTermTaylor2Decomp` splits the change into a linear part and the higher-order
  remainder.

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

`bchQuinticSubsetPiece_eq_taylorPiece` identifies each grouped sum with the corresponding
Taylor component of `bchQuinticTermTable`. The table expansion then gives the decomposition,
and its weighted counts of size-`k` subsets give the norm bounds.

## Provenance

Ported from `Lean-BCH/BCH/Basic.lean:3028-4830`. The source presents both sides as explicit
`+`-chains of monomials and closes the identity with `match_scalars <;> ring` under
`maxHeartbeats 1024000000`; see `artifacts/quintic-taylor2-route.md` for why that presentation is
not available here. The source constant of the remainder is `(1680 + 720 + 30)/720 = 2430/720`, the
sum of the three pieces' constants.
-/

@[expose] public section

open Finset FQFP.WordTable

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

/-- Each quintic subset piece is the Taylor component of the quintic coefficient table. -/
theorem bchQuinticSubsetPiece_eq_taylorPiece [Ring 𝔸] [Algebra ℚ 𝔸] (k : ℕ) (x V y : 𝔸) :
    bchQuinticSubsetPiece k x V y =
      taylorPiece coefficientScale bchQuinticTermTable 0 ![x, y] V k := by
  simp only [bchQuinticTermTable, taylorPiece_append, taylorPiece_ofFn, bchQuinticSubsetPiece,
    bchQuinticBracket, bchQuinticGroupSubsets, wordTaylorPiece]
  norm_num [coefficientScale]
  module

/-- **`bchQuinticTerm` at `x + V` is the sum of its subset pieces.** -/
theorem bchQuinticTerm_add_eq_sum_pieces [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticTerm (x + V) y = ∑ k ∈ Finset.range 5, bchQuinticSubsetPiece k x V y := by
  rw [← eval_bchQuinticTermTable]
  simpa only [bchQuinticSubsetPiece_eq_taylorPiece, Matrix.vecCons, Fin.cons_zero,
    Fin.update_cons_zero] using
    eval_update_add_eq_sum_taylorPiece coefficientScale bchQuinticTermTable 0 ![x, y] V 4
      (by decide +kernel)

/-- **The `k = 0` piece is `bchQuinticTerm` itself**: substituting `V` at no position leaves the
word alone. -/
theorem bchQuinticSubsetPiece_zero [Ring 𝔸] [Algebra ℚ 𝔸] (x V y : 𝔸) :
    bchQuinticSubsetPiece 0 x V y = bchQuinticTerm x y := by
  rw [bchQuinticSubsetPiece_eq_taylorPiece, taylorPiece_zero, eval_bchQuinticTermTable]

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
