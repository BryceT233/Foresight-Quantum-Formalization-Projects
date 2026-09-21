/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms

/-!
# The subset-expansion route for `bchQuinticTermTaylor2Decomp`: verified core

These lemmas are the reusable core of the route described in
`artifacts/bch-quintic-representations.md`. They compile, so this file doubles as a regression
check for the pieces that are already known to work.

The route: `bchQuinticTerm (x + V) y - bchQuinticTerm x y` is a sum over the 30 core words. For each
word `w`, let `s := {i | w i = 0}` be its `x`-positions. Then

* `wordProdList ![x+V, V, y] w = ∏ i, if i ∈ s then x + V else y` (other positions hold `y`),
* `wordProdList ![x, V, y] w = ∏ i, if i ∈ s then x else y`,

and the difference of the two is `Finset.prod_add` with `f = if · ∈ s then x else y` and
`g = if · ∈ s then V else 0`, whose `t = s` summand is the subtrahend.

Remaining work: the `Finset` index bookkeeping that turns the surviving summands into
`∑ t ∈ s.powerset.filter Nonempty, (∏ i ∈ t, (x+V)) * ∏ i ∈ s \ t, x`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open Finset

namespace FQFP.BCH

noncomputable section

variable {𝔸 : Type*} [CommRing 𝔸] {n : ℕ}

/-- **The substitution product splits over `s`**, the `x`-positions. `Finset.prod_ite` does the
split, so no `prod_sdiff` reasoning is needed. -/
lemma taylorProdSplit (x V y : 𝔸) (s : Finset (Fin n)) :
    (∏ i : Fin n, (if i ∈ s then x + V else y))
      = (∏ _i ∈ s, (x + V)) * ∏ _i ∈ (Finset.univ \ s : Finset (Fin n)), y := by
  rw [Finset.prod_ite (fun _i : Fin n => x + V) (fun _i : Fin n => y)]
  congr 1
  · exact Finset.prod_congr (by ext i; simp) fun i _ => rfl
  · exact Finset.prod_congr (by ext i; simp) fun i _ => rfl

/-- **The binomial expansion of the `s`-product**, i.e. `Finset.prod_add` with constant functions.
The `t = s` summand is `∏ i ∈ s, x` — that is the subtrahend, *not* the `t = ∅` summand. -/
lemma prodAdd_const (x V : 𝔸) (s : Finset (Fin n)) :
    (∏ _i ∈ s, (x + V)) = ∑ t ∈ s.powerset, (∏ _i ∈ t, x) * ∏ _i ∈ s \ t, V :=
  Finset.prod_add (fun _i : Fin n => x) (fun _i : Fin n => V) s

/-- The `t = s` summand of that expansion is exactly the subtrahend. -/
lemma prodAdd_const_at_s (x V : 𝔸) (s : Finset (Fin n)) :
    (∏ _i ∈ (s : Finset (Fin n)), x) * ∏ _i ∈ s \ s, (V : 𝔸) = ∏ _i ∈ s, x := by
  simp

end

end FQFP.BCH
