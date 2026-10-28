/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.Table
public import FQFP.Algebra.Word.Basic

/-!
# Prefix trees for binary coefficient certificates

Insertion follows a word's letters rather than searching a list of previously seen words.
The evaluation theorem connects this computational representation to `WordTable.eval`.
Converting a tree back to its nonzero rows gives a coefficient collection operation.

## Main results

* `eval_collapse`: prefix collection preserves scaled ordered-word evaluation.
* `eval_table_eq_zero`: a zero tree certifies a polynomial identity.
-/

@[expose] public section

namespace FQFP.BinaryWordTable

/-- A binary prefix tree with an integer coefficient at every word, including the empty word. -/
inductive Tree where
  | zero
  | node (coeff : ℤ) (left right : Tree)

/-- Add a coefficient at a word's path. -/
def insert : List (Fin 2) → ℤ → Tree → Tree
  | [], c, .zero => .node c .zero .zero
  | [], c, .node d l r => .node (c + d) l r
  | a :: w, c, .zero =>
    if a = 0 then .node 0 (insert w c .zero) .zero
    else .node 0 .zero (insert w c .zero)
  | a :: w, c, .node d l r =>
    if a = 0 then .node d (insert w c l) r
    else .node d l (insert w c r)

/-- Collect a table by following its word prefixes. -/
def collect : WordTable.Table (Fin 2) → Tree
  | [] => .zero
  | p :: t => insert p.1 p.2 (collect t)

/-- Check all stored integer coefficients. -/
def isZero : Tree → Bool
  | .zero => true
  | .node c l r => c == 0 && isZero l && isZero r

/-- Return the nonzero rows of a binary coefficient tree. -/
def toTable : Tree → WordTable.Table (Fin 2)
  | .zero => []
  | .node c l r =>
    (if c = 0 then [] else [([], c)]) ++
      (toTable l).map (fun p ↦ (0 :: p.1, p.2)) ++
      (toTable r).map (fun p ↦ (1 :: p.1, p.2))

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Horner evaluation of the prefix tree, with ordered multiplication. -/
noncomputable def eval (f : Fin 2 → A) : Tree → A
  | .zero => 0
  | .node c l r => (c : ℚ) • (1 : A) + f 0 * eval f l + f 1 * eval f r

/-- Inserting a word adds exactly its weighted ordered product. -/
theorem eval_insert (f : Fin 2 → A) (w : List (Fin 2)) (c : ℤ) (t : Tree) :
    eval f (insert w c t) = (c : ℚ) • (w.map f).prod + eval f t := by
  induction w generalizing t with
  | nil => cases t <;> simp [insert, eval, Int.cast_add, add_smul, add_assoc]
  | cons a w ih =>
    fin_cases a <;> cases t <;>
      simp [insert, eval, ih, mul_add, add_assoc, add_left_comm, add_comm]

/-- Collecting the table preserves its unscaled evaluation. -/
theorem eval_collect (f : Fin 2 → A) (t : WordTable.Table (Fin 2)) :
    eval f (collect t) = WordTable.eval 1 f t := by
  induction t with
  | nil => rfl
  | cons p t ih => simp [collect, eval_insert, WordTable.eval_cons, ih]

/-- A tree with zero coefficients evaluates to zero. -/
theorem eval_eq_zero (f : Fin 2 → A) (t : Tree) (h : isZero t = true) : eval f t = 0 := by
  induction t with
  | zero => rfl
  | node c l r hl hr =>
    simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [eval, h.1.1, hl h.1.2, hr h.2]

/-- Absorb a table's scale into its letter assignment. This includes zero scale. -/
theorem eval_scale (s : ℚ) (f : Fin 2 → A) (t : WordTable.Table (Fin 2)) :
    WordTable.eval s f t = WordTable.eval 1 (fun a => s⁻¹ • f a) t := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    rw [WordTable.eval_cons, WordTable.eval_cons, ih, FQFP.prod_map_smul]
    simp [smul_smul, div_eq_mul_inv, inv_pow]

/-- A checked prefix tree certifies the original scaled word table. -/
theorem eval_table_eq_zero (s : ℚ) (f : Fin 2 → A) (t : WordTable.Table (Fin 2))
    (h : isZero (collect t) = true) : WordTable.eval s f t = 0 := by
  rw [eval_scale, ← eval_collect]
  exact eval_eq_zero _ _ h

private theorem eval_map_cons (f : Fin 2 → A) (a : Fin 2) (t : WordTable.Table (Fin 2)) :
    WordTable.eval 1 f (t.map fun p ↦ (a :: p.1, p.2)) = f a * WordTable.eval 1 f t := by
  induction t with
  | nil => simp [WordTable.eval_nil]
  | cons p t ih =>
    rw [List.map_cons, WordTable.eval_cons, WordTable.eval_cons, ih, mul_add]
    simp [List.map_cons, List.prod_cons]

/-- Converting a coefficient tree to rows preserves its ordered polynomial. -/
theorem eval_toTable (f : Fin 2 → A) (t : Tree) :
    WordTable.eval 1 f (toTable t) = eval f t := by
  induction t with
  | zero => rfl
  | node c l r hl hr =>
    rw [toTable, WordTable.eval_append, WordTable.eval_append,
      eval_map_cons, eval_map_cons, hl, hr, eval]
    by_cases hc : c = 0 <;> simp [hc, WordTable.eval_nil, WordTable.eval_singleton]

/-- Collect a binary table by its word prefixes, discarding zero rows. -/
def collapse (t : WordTable.Table (Fin 2)) : WordTable.Table (Fin 2) := toTable (collect t)

/-- Prefix collection preserves the original table's scaled evaluation. -/
theorem eval_collapse (s : ℚ) (f : Fin 2 → A) (t : WordTable.Table (Fin 2)) :
    WordTable.eval s f (collapse t) = WordTable.eval s f t := by
  rw [eval_scale, collapse, eval_toTable, eval_collect, ← eval_scale]

end FQFP.BinaryWordTable
