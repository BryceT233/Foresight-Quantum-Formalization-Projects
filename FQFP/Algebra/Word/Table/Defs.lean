/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Module.Rat

/-!
# Integer word tables and their scaled evaluation

Definitions of the integer representation. Operation and evaluation compatibility
with general coefficient tables is provided by `FQFP.Algebra.Word.Compatibility`.
-/

@[expose] public section

namespace FQFP.WordTable

/-- A finite integer coefficient table on the alphabet `α`. -/
abbrev Table (α : Type*) := List (List α × ℤ)

variable {α 𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸]

/-- Evaluate each word in order, weighted by its coefficient divided by the scale
raised to its length. -/
noncomputable def eval (scale : ℚ) (letters : α → 𝔸) (t : Table α) : 𝔸 :=
  (t.map fun p => ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod).sum

/-- The identity table of the empty word. -/
def unit : Table α := [([], 1)]

/-- **Row-wise product of two tables**: cartesian product of the rows, word concatenation,
integer coefficient product. -/
def mul (s t : Table α) : Table α :=
  s.flatMap fun p => t.map fun r => (p.1 ++ r.1, p.2 * r.2)

/-- Multiply every coefficient by an integer. -/
def smul (c : ℤ) (t : Table α) : Table α := t.map fun p => (p.1, c * p.2)

/-- The `n`-fold product of a table with itself. -/
def pow (t : Table α) : ℕ → Table α
  | 0 => unit
  | n + 1 => mul (pow t n) t

/-- Add one row to an accumulator, merging it with an equal word. The merged row carries `p.1` as
its word, which is the same word by the branch condition, so no projection is needed. -/
def addRow [DecidableEq α] (p : List α × ℤ) : Table α → Table α
  | [] => [p]
  | r :: t => if r.1 = p.1 then (p.1, r.2 + p.2) :: t else r :: addRow p t

/-- Merge every row of a table into an accumulator, one row at a time. -/
def collapseAux [DecidableEq α] : Table α → Table α → Table α
  | [], acc => acc
  | p :: t, acc => collapseAux t (addRow p acc)

/-- Collect the coefficients of equal words, retaining the order of first occurrence.

Zero coefficients are retained. Computation uses the supplied decidable equality on the
alphabet and integer addition; no comparison of rational coefficients is needed. -/
def collapse [DecidableEq α] (t : Table α) : Table α := collapseAux t []

end FQFP.WordTable
