/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

/-!
# Integer coefficient tables for the free word algebra on two letters

BCH's degree-`k` terms are finite sums of length-`k` words on two letters with rational
coefficients, and the cancellation identities are polynomial identities between such sums,
compared coefficient by coefficient.

The coefficients are what makes that comparison expensive. `ℚ` has no kernel reduction
(`(2 : ℚ) * 3 = 6` is not `rfl`, and `DecidableEq ℚ` does not reduce), so a coefficient comparison
can only be driven by `norm_num`, one small expression at a time — and the degree-6 identity
written that way needs 64 separate declarations, each unfolding a ~1000-row table. See
`artifacts/abstractions/wordalgebra-int.md` and `artifacts/bch-wordalgebra-next-step.md`.

This file replaces the coefficients by **integers**: a degree-`d` table stores `K ^ d` times its
rational coefficients, where `K = 210` clears every denominator occurring in degrees `≤ 8`.
Integer arithmetic *is* kernel-reducible, so the same identity becomes one computation that `rfl`
and `decide` both do.

## Main definitions

* `KTab` — a *table*: rows of `(word, integer coefficient)`; the data of a term.
* `evalKTab a b t` — the element of `𝔸` a table denotes: each row's word is multiplied out
  through `a`, `b`, and weighted by its coefficient over `K ^ (length of the word)`.
* `mulKTab`, `smulKTab`, `powKTab`, `unitKTab` — the data-level ring operations.
* `ratTab` — the rational table a cleared table denotes (`c ↦ c / K ^ |w|`), for consumers stated
  over `ℚ`-weighted word lists (the norm API of `WordExpansion.lean`).
* `addRowK`, `collapseAuxK`, `collapseK` — the support-pinned normal form: one row per word.

## Main results

* `evalKTab_append`, `evalKTab_mulKTab`, `evalKTab_smulKTab`, `evalKTab_powKTab` — the table
  operations compute the ring operations.
* `evalKTab_collapseK` — collapsing does not change the evaluation.
* `evalKTab_eq_zero_of_all_beq` — **the criterion** a degree-`k` identity is settled by: if the
  collapsed table has no nonzero coefficient, the evaluation is zero.

## Implementation notes

The scaling is carried by the **word length**, not by a separate degree field: a row `(w, c)`
denotes `(c / K ^ w.length)` times the monomial of `w`. Multiplication is then automatically
compatible, because `K ^ (l₁ ++ l₂).length = K ^ l₁.length * K ^ l₂.length`; there is no
homogeneity invariant to maintain, no degree index, and no `Finsupp` convolution involved.
`rat_div_mul_div` is the only place `K` is used.

Only *integer* scalars are available in a table. The rational coefficients `1/2, …, 1/d` of the
Dynkin/Ree form are therefore cleared **before** the scaling, by multiplying the identity through
by `lcm(1, …, d)`; the tables of `SmallSDischarge.lean` carry the resulting integer multipliers.

`K = 210 = 2 * 3 * 5 * 7`, so `K ^ d` is divisible by every denominator occurring at degree `d`
for `d ≤ 8`: the factorials `d!`, and the common denominators `1440`, `30240` and `120960` of the
degree-6, -7 and -8 terms. A higher degree needs a larger `K` — it must contain every prime up to
that degree, so `210` covers `d ≤ 8` and degree `9` or `10` should not be attempted without
revisiting it. The tables are generated data, so that is one constant to change.
-/

@[expose] public section

namespace FQFP.BCH.WordAlgebra

variable {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸]

/-- The factor that clears the coefficients: `210 = 2 * 3 * 5 * 7`. A degree-`d` table stores
`K ^ d` times its rational coefficients, and every denominator occurring up to degree `8` divides
`K ^ d`. -/
def K : ℕ := 210

/-- **A table**: rows of `(word, integer coefficient)`. The row `(w, c)` denotes `c / K ^ |w|`
times the monomial of the word `w`. -/
abbrev KTab : Type := List (List (Fin 2) × ℤ)

/-- **The evaluation of a table** in an algebra `𝔸`: multiply out each row's word through `a` and
`b`, weight it by its coefficient over `K ^ (length of the word)`, and sum.

This is the only bridge from a table to a ring element; everything below says that the table
operations compute the ring operations. -/
noncomputable def evalKTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) (t : KTab) : 𝔸 :=
  (t.map fun p => ((p.2 : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod).sum

/-- The rational table a cleared table denotes: `(w, c) ↦ (w, c / K ^ |w|)`. A cleared table and
this rational table have the same evaluation, which is what lets the `ℚ`-weighted norm API be
reused unchanged. -/
def ratTab (t : KTab) : List (List (Fin 2) × ℚ) :=
  t.map fun p => (p.1, (p.2 : ℚ) / (K : ℚ) ^ p.1.length)

/-- The identity table of the empty word. -/
def unitKTab : KTab := [([], 1)]

/-- **Row-wise product of two tables**: cartesian product of the rows, word concatenation,
integer coefficient product. -/
def mulKTab (s t : KTab) : KTab :=
  s.flatMap fun p => t.map fun r => (p.1 ++ r.1, p.2 * r.2)

/-- Scale every coefficient by an integer. Only integer scalars are available: the rational
coefficients of a Dynkin/Ree expression are cleared before the scaling, not after. -/
def smulKTab (c : ℤ) (t : KTab) : KTab := t.map fun p => (p.1, c * p.2)

/-- The `n`-fold product of a table with itself. -/
def powKTab (t : KTab) : ℕ → KTab
  | 0 => unitKTab
  | n + 1 => mulKTab (powKTab t n) t

/-- Add one row to an accumulator, merging it with an equal word. The merged row carries `p.1` as
its word, which is the same word by the branch condition, so no projection is needed. -/
def addRowK (p : List (Fin 2) × ℤ) : KTab → KTab
  | [] => [p]
  | r :: t => if r.1 = p.1 then (p.1, r.2 + p.2) :: t else r :: addRowK p t

/-- Merge every row of a table into an accumulator, one row at a time. -/
def collapseAuxK : KTab → KTab → KTab
  | [], acc => acc
  | p :: t, acc => collapseAuxK t (addRowK p acc)

/-- **The support-pinned normal form of a table**: one row per word.

This is what makes a degree-`k` coefficient comparison affordable: the merge tests only *word*
equality, which `List (Fin 2)` decides by kernel reduction, and the integer additions are kernel
reducible too, so a collapsed table is a `rfl`-level computation. -/
def collapseK (t : KTab) : KTab := collapseAuxK t []

/-! ### Coefficient arithmetic

The only algebraic fact the scaling needs. -/

/-- The two denominators clear against the concatenated word: `K ^ (a + b) = K ^ a * K ^ b`. -/
lemma rat_div_mul_div (c₁ c₂ : ℤ) (a b : ℕ) :
    (c₁ : ℚ) / (K : ℚ) ^ a * ((c₂ : ℚ) / (K : ℚ) ^ b)
      = ((c₁ * c₂ : ℤ) : ℚ) / (K : ℚ) ^ (a + b) := by
  rw [div_mul_div_comm, ← pow_add, Int.cast_mul]

/-! ### Evaluating a table -/

lemma evalKTab_nil (a b : 𝔸) : evalKTab a b ([] : KTab) = 0 := rfl

lemma evalKTab_cons (a b : 𝔸) (p : List (Fin 2) × ℤ) (t : KTab) :
    evalKTab a b (p :: t)
      = ((p.2 : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod + evalKTab a b t := by
  rw [evalKTab, List.map_cons, List.sum_cons]
  rfl

lemma evalKTab_append (a b : 𝔸) (s t : KTab) :
    evalKTab a b (s ++ t) = evalKTab a b s + evalKTab a b t := by
  induction s with
  | nil => rw [List.nil_append, evalKTab_nil, zero_add]
  | cons p s ih => rw [List.cons_append, evalKTab_cons, ih, evalKTab_cons, add_assoc]

/-- **The rational table evaluates the same way.** Stated so that the `ℚ`-weighted norm API of
`WordExpansion.lean` applies to a cleared table without any change to that file. -/
lemma evalKTab_ratTab (a b : 𝔸) (t : KTab) :
    evalKTab a b t = ((ratTab t).map fun p => p.2 • (p.1.map ![a, b]).prod).sum := by
  rw [evalKTab, ratTab, List.map_map]
  rfl

/-- **A product of two weighted monomials is one weighted monomial**: the words concatenate and
the integer coefficients multiply, at the table's scaling. -/
lemma smul_prod_mul_smul_prod (a b : 𝔸) (l₁ l₂ : List (Fin 2)) (c₁ c₂ : ℤ) :
    ((c₁ : ℚ) / (K : ℚ) ^ l₁.length) • (l₁.map ![a, b]).prod
        * (((c₂ : ℚ) / (K : ℚ) ^ l₂.length) • (l₂.map ![a, b]).prod)
      = (((c₁ * c₂ : ℤ) : ℚ) / (K : ℚ) ^ (l₁ ++ l₂).length)
          • ((l₁ ++ l₂).map ![a, b]).prod := by
  rw [smul_mul_smul_comm, ← List.prod_append, ← List.map_append, List.length_append,
    rat_div_mul_div]

lemma evalKTab_mul_single (a b : 𝔸) (p : List (Fin 2) × ℤ) (t : KTab) :
    evalKTab a b (t.map fun r => (p.1 ++ r.1, p.2 * r.2))
      = ((p.2 : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod * evalKTab a b t := by
  induction t with
  | nil => rw [List.map_nil, evalKTab_nil, mul_zero]
  | cons r t ih =>
      rw [List.map_cons, evalKTab_cons, ih, evalKTab_cons, mul_add, smul_prod_mul_smul_prod]

/-- **The evaluation of a table product is the product of the evaluations.** -/
lemma evalKTab_mulKTab (a b : 𝔸) (s t : KTab) :
    evalKTab a b (mulKTab s t) = evalKTab a b s * evalKTab a b t := by
  induction s with
  | nil =>
      change evalKTab a b ([] : KTab) = evalKTab a b ([] : KTab) * _
      rw [evalKTab_nil, zero_mul]
  | cons p s ih =>
      change evalKTab a b (List.flatMap
        (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) (p :: s)) = _
      rw [List.flatMap_cons, evalKTab_append, evalKTab_mul_single, evalKTab_cons, add_mul]
      rw [show evalKTab a b (List.flatMap
            (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) s)
          = evalKTab a b s * evalKTab a b t from ih]

/-- **The evaluation of a scaled table is the scaled evaluation.** -/
lemma evalKTab_smulKTab (a b : 𝔸) (c : ℤ) (t : KTab) :
    evalKTab a b (smulKTab c t) = (c : ℚ) • evalKTab a b t := by
  induction t with
  | nil => rw [smulKTab, List.map_nil, evalKTab_nil, smul_zero]
  | cons p t ih =>
      change (((c * p.2 : ℤ) : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod
          + evalKTab a b (smulKTab c t) = (c : ℚ) • evalKTab a b (p :: t)
      rw [ih, evalKTab_cons, smul_add]
      congr 1
      rw [smul_smul, Int.cast_mul, mul_div_assoc]

lemma evalKTab_singleton (a b : 𝔸) (p : List (Fin 2) × ℤ) :
    evalKTab a b [p] = ((p.2 : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod := by
  rw [evalKTab_cons, evalKTab_nil, add_zero]

/-- **The unit table evaluates to `1`.** -/
lemma evalKTab_unitKTab (a b : 𝔸) : evalKTab a b unitKTab = 1 := by
  rw [unitKTab, evalKTab_singleton]
  simp [List.length_nil]

/-- **The evaluation of a table power is the power of the evaluation.** -/
lemma evalKTab_powKTab (a b : 𝔸) (t : KTab) (n : ℕ) :
    evalKTab a b (powKTab t n) = evalKTab a b t ^ n := by
  induction n with
  | zero => rw [powKTab, evalKTab_unitKTab, pow_zero]
  | succ n ih => rw [powKTab, evalKTab_mulKTab, ih, pow_succ]

/-! ### Collapsing -/

/-- **Adding a row does not change the evaluation.** -/
lemma evalKTab_addRowK (a b : 𝔸) (p : List (Fin 2) × ℤ) (acc : KTab) :
    evalKTab a b (addRowK p acc)
      = ((p.2 : ℚ) / (K : ℚ) ^ p.1.length) • (p.1.map ![a, b]).prod + evalKTab a b acc := by
  induction acc with
  | nil => rw [addRowK, evalKTab_cons, evalKTab_nil, add_zero]
  | cons r t ih =>
      rw [addRowK]
      split_ifs with h
      · rw [evalKTab_cons, evalKTab_cons]
        dsimp only
        rw [h, Int.cast_add, add_div, add_smul]
        ac_rfl
      · rw [evalKTab_cons, ih, evalKTab_cons]
        ac_rfl

/-- **Collapsing does not change the evaluation.** -/
lemma evalKTab_collapseAuxK (a b : 𝔸) (t acc : KTab) :
    evalKTab a b (collapseAuxK t acc) = evalKTab a b t + evalKTab a b acc := by
  induction t generalizing acc with
  | nil => rw [collapseAuxK, evalKTab_nil, zero_add]
  | cons p t ih =>
      rw [collapseAuxK, ih, evalKTab_addRowK, evalKTab_cons]
      ac_rfl

/-- **A table and its collapsed form evaluate equally.** -/
lemma evalKTab_collapseK (a b : 𝔸) (t : KTab) :
    evalKTab a b (collapseK t) = evalKTab a b t := by
  rw [collapseK, evalKTab_collapseAuxK, evalKTab_nil, add_zero]

/-! ### The zero criterion

A degree-`k` identity is proved by collapsing one side and checking that no coefficient survives.
The two lemmas below are the two halves of that: the `==` form is what the kernel computes in the
data-level goal, and the `∀` form is what it is used as. -/

/-- **A table whose rows all carry coefficient `0` evaluates to `0`.** -/
lemma evalKTab_eq_zero_of_rows (a b : 𝔸) (t : KTab) (h : ∀ p ∈ t, p.2 = 0) :
    evalKTab a b t = 0 := by
  induction t with
  | nil => exact evalKTab_nil a b
  | cons p t ih =>
      rw [evalKTab_cons, ih fun q hq => h q (List.mem_cons_of_mem _ hq), add_zero]
      rw [h p List.mem_cons_self, Int.cast_zero, zero_div, zero_smul]

/-- **The zero criterion**, in the form the kernel check produces. -/
lemma evalKTab_eq_zero_of_all_beq (a b : 𝔸) (t : KTab) (h : t.all (fun p => p.2 == 0) = true) :
    evalKTab a b t = 0 :=
  evalKTab_eq_zero_of_rows a b t fun p hp => by
    have := (List.all_eq_true.mp h) p hp
    simpa [beq_iff_eq] using this

end FQFP.BCH.WordAlgebra
