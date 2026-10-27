/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic
public import FQFP.BCH.Algebra.Word

/-!
# Integer certificates for noncommutative polynomial identities

A table is a finite list of words with integer coefficients. At a rational scale `s`,
the row `(w, c)` denotes `(c / s ^ w.length)` times the ordered product of its letters.
Both the alphabet and the scale are parameters. No degree restriction, topology, or
nonzero-scale hypothesis is needed for the evaluation identities.

The list representation supports kernel computation of coefficient certificates. It
does not impose a new ring structure: multiplication and collection are operations
on representatives, and their evaluation laws supply their mathematical semantics.

## Main definitions

* `Table`: integer coefficient tables on an arbitrary alphabet.
* `eval`: evaluation in a rational algebra, with an explicit scale and letter assignment.
* `mul`, `smul`, `pow`: operations on representatives.
* `collapse`: collection of coefficients of equal words.

## Main results

* `eval_mul`, `eval_smul`, `eval_pow`: evaluation respects the table operations.
* `eval_of_length`: a homogeneous table has one common scaling denominator.
* `eval_smul_of_length`: homogeneous tables scale by their common word length.
* `eval_collapse`: collecting coefficients preserves evaluation.
* `eval_eq_zero_of_all_beq`: a checked zero coefficient table evaluates to zero.
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

/-! ### Coefficient arithmetic

The only algebraic fact the scaling needs. -/

/-- Scaled coefficients multiply according to addition of word lengths. -/
lemma rat_div_mul_div (scale : ℚ) (c₁ c₂ : ℤ) (a b : ℕ) :
    (c₁ : ℚ) / scale ^ a * ((c₂ : ℚ) / scale ^ b)
      = ((c₁ * c₂ : ℤ) : ℚ) / scale ^ (a + b) := by
  rw [div_mul_div_comm, ← pow_add, Int.cast_mul]

/-! ### Evaluating a table -/

lemma eval_nil (scale : ℚ) (letters : α → 𝔸) : eval scale letters ([] : Table α) = 0 := rfl

lemma eval_cons (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) (t : Table α) :
    eval scale letters (p :: t)
      = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod + eval scale letters t := by
  rw [eval, List.map_cons, List.sum_cons]
  rfl

lemma eval_append (scale : ℚ) (letters : α → 𝔸) (s t : Table α) :
    eval scale letters (s ++ t) = eval scale letters s + eval scale letters t := by
  simp only [eval, List.map_append, List.sum_append]

/-- Evaluate a finite family of words of one length and one coefficient. -/
lemma eval_ofFn (scale : ℚ) (letters : α → 𝔸) {m n : ℕ}
    (words : Fin m → Fin n → α) (c : ℤ) :
    eval scale letters (List.ofFn fun i => (List.ofFn (words i), c)) =
      ((c : ℚ) / scale ^ n) • ∑ i, ((List.ofFn (words i)).map letters).prod := by
  simp only [eval, List.map_ofFn, List.sum_ofFn, List.length_ofFn,
    Finset.smul_sum, Function.comp_def]

/-- At a common word length, the table scale is one common scalar factor. -/
lemma eval_of_length {κ A : Type*} [Semiring A] [Algebra ℚ A]
    (scale : ℚ) (letters : κ → A) (t : Table κ) (n : ℕ)
    (hlen : ∀ p ∈ t, p.1.length = n) :
    eval scale letters t = (scale ^ n)⁻¹ • eval 1 letters t := by
  induction t with
  | nil => simp [eval_nil]
  | cons p t ih =>
    rw [eval_cons, eval_cons, hlen p List.mem_cons_self,
      ih (fun q hq ↦ hlen q (List.mem_cons_of_mem p hq)), smul_add, smul_smul]
    simp [div_eq_mul_inv, mul_comm]

/-- Evaluating a homogeneous table on scaled letters scales by the common word length. -/
lemma eval_smul_of_length {R κ A : Type*} [CommSemiring R] [Semiring A]
    [Algebra ℚ A] [Algebra R A] (scale : ℚ) (letters : κ → A) (t : Table κ)
    (n : ℕ) (hlen : ∀ p ∈ t, p.1.length = n) (c : R) :
    eval scale (fun k ↦ c • letters k) t = c ^ n • eval scale letters t := by
  induction t with
  | nil => simp [eval]
  | cons p t ih =>
    rw [eval_cons, eval_cons, ih (fun q hq ↦ hlen q (List.mem_cons_of_mem p hq)), smul_add,
      prod_map_smul, hlen p List.mem_cons_self, smul_comm]

/-- **A product of two weighted monomials is one weighted monomial**: the words concatenate and
the integer coefficients multiply, at the table's scaling. -/
lemma smul_prod_mul_smul_prod (scale : ℚ) (letters : α → 𝔸) (l₁ l₂ : List α) (c₁ c₂ : ℤ) :
    ((c₁ : ℚ) / scale ^ l₁.length) • (l₁.map letters).prod
        * (((c₂ : ℚ) / scale ^ l₂.length) • (l₂.map letters).prod)
      = (((c₁ * c₂ : ℤ) : ℚ) / scale ^ (l₁ ++ l₂).length)
          • ((l₁ ++ l₂).map letters).prod := by
  rw [smul_mul_smul_comm, ← List.prod_append, ← List.map_append, List.length_append,
    rat_div_mul_div]

lemma eval_mul_single (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) (t : Table α) :
    eval scale letters (t.map fun r => (p.1 ++ r.1, p.2 * r.2))
      = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod * eval scale letters t := by
  induction t with
  | nil => rw [List.map_nil, eval_nil, mul_zero]
  | cons r t ih =>
      rw [List.map_cons, eval_cons, ih, eval_cons, mul_add, smul_prod_mul_smul_prod]

/-- **The evaluation of a table product is the product of the evaluations.** -/
lemma eval_mul (scale : ℚ) (letters : α → 𝔸) (s t : Table α) :
    eval scale letters (mul s t) = eval scale letters s * eval scale letters t := by
  induction s with
  | nil =>
      change eval scale letters ([] : Table α) = eval scale letters ([] : Table α) * _
      rw [eval_nil, zero_mul]
  | cons p s ih =>
      change eval scale letters (List.flatMap
        (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) (p :: s)) = _
      rw [List.flatMap_cons, eval_append, eval_mul_single, eval_cons, add_mul]
      rw [show eval scale letters (List.flatMap
            (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) s)
          = eval scale letters s * eval scale letters t from ih]

/-- **The evaluation of a scaled table is the scaled evaluation.** -/
lemma eval_smul (scale : ℚ) (letters : α → 𝔸) (c : ℤ) (t : Table α) :
    eval scale letters (smul c t) = (c : ℚ) • eval scale letters t := by
  induction t with
  | nil => rw [smul, List.map_nil, eval_nil, smul_zero]
  | cons p t ih =>
      change (((c * p.2 : ℤ) : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod
          + eval scale letters (smul c t) = (c : ℚ) • eval scale letters (p :: t)
      rw [ih, eval_cons, smul_add]
      congr 1
      rw [smul_smul, Int.cast_mul, mul_div_assoc]

lemma eval_singleton (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) :
    eval scale letters [p] = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod := by
  rw [eval_cons, eval_nil, add_zero]

/-- **The unit table evaluates to `1`.** -/
lemma eval_unit (scale : ℚ) (letters : α → 𝔸) : eval scale letters unit = 1 := by
  rw [unit, eval_singleton]
  simp [List.length_nil]

/-- **The evaluation of a table power is the power of the evaluation.** -/
lemma eval_pow (scale : ℚ) (letters : α → 𝔸) (t : Table α) (n : ℕ) :
    eval scale letters (pow t n) = eval scale letters t ^ n := by
  induction n with
  | zero => rw [pow, eval_unit, pow_zero]
  | succ n ih => rw [pow, eval_mul, ih, pow_succ]

/-! ### Collapsing -/

/-- **Adding a row does not change the evaluation.** -/
lemma eval_addRow [DecidableEq α] (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) (acc : Table α) :
    eval scale letters (addRow p acc)
      = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod + eval scale letters acc := by
  induction acc with
  | nil => rw [addRow, eval_cons, eval_nil, add_zero]
  | cons r t ih =>
      rw [addRow]
      split_ifs with h
      · rw [eval_cons, eval_cons]
        dsimp only
        rw [h, Int.cast_add, add_div, add_smul]
        ac_rfl
      · rw [eval_cons, ih, eval_cons]
        ac_rfl

/-- **Collapsing does not change the evaluation.** -/
lemma eval_collapseAux [DecidableEq α] (scale : ℚ) (letters : α → 𝔸) (t acc : Table α) :
    eval scale letters (collapseAux t acc) = eval scale letters t + eval scale letters acc := by
  induction t generalizing acc with
  | nil => rw [collapseAux, eval_nil, zero_add]
  | cons p t ih =>
      rw [collapseAux, ih, eval_addRow, eval_cons]
      ac_rfl

/-- **A table and its collapsed form evaluate equally.** -/
lemma eval_collapse [DecidableEq α] (scale : ℚ) (letters : α → 𝔸) (t : Table α) :
    eval scale letters (collapse t) = eval scale letters t := by
  rw [collapse, eval_collapseAux, eval_nil, add_zero]

/-! ### The zero criterion -/

/-- **A table whose rows all carry coefficient `0` evaluates to `0`.** -/
lemma eval_eq_zero_of_rows (scale : ℚ) (letters : α → 𝔸) (t : Table α) (h : ∀ p ∈ t, p.2 = 0) :
    eval scale letters t = 0 := by
  induction t with
  | nil => exact eval_nil scale letters
  | cons p t ih =>
      rw [eval_cons, ih fun q hq => h q (List.mem_cons_of_mem _ hq), add_zero]
      rw [h p List.mem_cons_self, Int.cast_zero, zero_div, zero_smul]

/-- **The zero criterion**, in the form the kernel check produces. -/
lemma eval_eq_zero_of_all_beq (scale : ℚ) (letters : α → 𝔸) (t : Table α)
    (h : t.all (fun p => p.2 == 0) = true) :
    eval scale letters t = 0 :=
  eval_eq_zero_of_rows scale letters t fun p hp => by
    simpa only [beq_iff_eq] using (List.all_eq_true.mp h) p hp

end FQFP.WordTable
