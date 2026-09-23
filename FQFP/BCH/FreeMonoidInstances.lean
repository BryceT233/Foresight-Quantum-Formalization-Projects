/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.FreeMonoid.Basic

/-!
# The two missing `FreeMonoid` instances

`ℚ[FreeMonoid α]` — the free associative algebra on `α`, presented as a monoid algebra — is the
vehicle for comparing BCH terms coefficient-wise. Two instances that this needs are absent from
Mathlib, and they are *both about the `FreeMonoid`/`List` presentation* rather than about BCH, so
they live here, at their natural level of generality in `α`.

## Main results

* `instDecidableEqFreeMonoid` — `DecidableEq (FreeMonoid α)` from `DecidableEq α`.
* `instHasMulAntidiagonalFreeMonoid` — `HasMulAntidiagonal (FreeMonoid α)` from `DecidableEq α`.

## Implementation notes

`FreeMonoid α` is a `def` alias for `List α`, so instance search does **not** see through the
alias: `List`'s `DecidableEq` is not found for `FreeMonoid α`. Both instances here are therefore
transfers across the identity equivalence `FreeMonoid.toList`.

The antidiagonal is the family of `take`/`drop` splits: a word of length `n` has exactly `n + 1`
factorizations `w = u * v`, indexed by the length of `u`. `DecidableEq α` is needed only because
`List.toFinset` deduplicates the splits; the splits are distinct already, so the hypothesis is
engineered rather than mathematical. Removing it would mean building the `Finset` from
`Finset.range` by an embedding, which does not appear worth the plumbing.
-/

@[expose] public section

/-- `FreeMonoid α` is a `def` alias for `List α`, so `List`'s `DecidableEq` is not found by
instance search; transfer it across the identity equivalence `FreeMonoid.toList`. -/
instance instDecidableEqFreeMonoid {α : Type*} [DecidableEq α] : DecidableEq (FreeMonoid α) :=
  FreeMonoid.toList.injective.decidableEq

namespace FreeMonoid

variable {α : Type*}

/-- The factorizations of a word are its `take`/`drop` splits: a word of length `n` has exactly
`n + 1` factorizations `w = u * v`, indexed by the length of `u`. -/
instance instHasMulAntidiagonal [DecidableEq α] : Finset.HasMulAntidiagonal (FreeMonoid α) where
  mulAntidiagonal w :=
    ((List.range (w.toList.length + 1)).map
      fun i => (ofList (w.toList.take i), ofList (w.toList.drop i))).toFinset
  mem_mulAntidiagonal := by
    intro n p
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, -, rfl⟩
      rw [← ofList_append, List.take_append_drop, ofList_toList]
    · rintro (h : p.1 * p.2 = n)
      have hcat : p.1.toList ++ p.2.toList = n.toList := by
        simpa using congrArg toList h
      have hlen : p.1.toList.length ≤ n.toList.length := by
        rw [← hcat]; simp
      refine ⟨p.1.toList.length, by lia, ?_⟩
      have htake : n.toList.take p.1.toList.length = p.1.toList := by
        rw [← hcat, List.take_left]
      have hdrop : n.toList.drop p.1.toList.length = p.2.toList := by
        rw [← hcat, List.drop_left]
      rw [htake, hdrop, ofList_toList, ofList_toList]

end FreeMonoid
