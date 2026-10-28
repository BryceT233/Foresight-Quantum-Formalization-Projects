/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic
public import FQFP.Algebra.Word.Compatibility

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

variable {α 𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸]

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
  simpa only [eval_eq_coeffWordTable] using
    CoeffWordTable.eval_append (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) s t

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

lemma eval_singleton (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) :
    eval scale letters [p] = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod := by
  rw [eval_cons, eval_nil, add_zero]

lemma eval_mul_single (scale : ℚ) (letters : α → 𝔸) (p : List α × ℤ) (t : Table α) :
    eval scale letters (t.map fun r => (p.1 ++ r.1, p.2 * r.2))
      = ((p.2 : ℚ) / scale ^ p.1.length) • (p.1.map letters).prod * eval scale letters t := by
  simpa only [CoeffWordTable.mul, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ← eval_eq_coeffWordTable scale letters, eval_singleton] using
      CoeffWordTable.eval_mul (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) [p] t

/-- **The evaluation of a table product is the product of the evaluations.** -/
lemma eval_mul (scale : ℚ) (letters : α → 𝔸) (s t : Table α) :
    eval scale letters (mul s t) = eval scale letters s * eval scale letters t := by
  simp only [eval_eq_coeffWordTable, mul_eq_coeffWordTable, CoeffWordTable.eval_mul]

/-- **The evaluation of a scaled table is the scaled evaluation.** -/
lemma eval_smul (scale : ℚ) (letters : α → 𝔸) (c : ℤ) (t : Table α) :
    eval scale letters (smul c t) = (c : ℚ) • eval scale letters t := by
  simpa only [eval_eq_coeffWordTable, smul_eq_coeffWordTable, Int.coe_castRingHom] using
    CoeffWordTable.eval_smul (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) c t

/-- **The unit table evaluates to `1`.** -/
lemma eval_unit (scale : ℚ) (letters : α → 𝔸) : eval scale letters unit = 1 := by
  simpa only [eval_eq_coeffWordTable, unit_eq_coeffWordTable] using
    CoeffWordTable.eval_unit (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k)

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
  simpa only [eval_eq_coeffWordTable, addRow_eq_coeffWordTable,
    Int.coe_castRingHom, smul_prod_scaled_letters] using
      CoeffWordTable.eval_addRow (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) p acc

/-- **Collapsing does not change the evaluation.** -/
lemma eval_collapseAux [DecidableEq α] (scale : ℚ) (letters : α → 𝔸) (t acc : Table α) :
    eval scale letters (collapseAux t acc) = eval scale letters t + eval scale letters acc := by
  simpa only [eval_eq_coeffWordTable, collapseAux_eq_coeffWordTable] using
    CoeffWordTable.eval_collapseAux (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) t acc

/-- **A table and its collapsed form evaluate equally.** -/
lemma eval_collapse [DecidableEq α] (scale : ℚ) (letters : α → 𝔸) (t : Table α) :
    eval scale letters (collapse t) = eval scale letters t := by
  simpa only [eval_eq_coeffWordTable, collapse_eq_coeffWordTable] using
    CoeffWordTable.eval_collapse (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) t

/-! ### The zero criterion -/

/-- **A table whose rows all carry coefficient `0` evaluates to `0`.** -/
lemma eval_eq_zero_of_rows (scale : ℚ) (letters : α → 𝔸) (t : Table α) (h : ∀ p ∈ t, p.2 = 0) :
    eval scale letters t = 0 := by
  rw [eval_eq_coeffWordTable]
  exact CoeffWordTable.eval_eq_zero_of_rows (Int.castRingHom ℚ)
    (fun k ↦ scale⁻¹ • letters k) t h

/-- **The zero criterion**, in the form the kernel check produces. -/
lemma eval_eq_zero_of_all_beq (scale : ℚ) (letters : α → 𝔸) (t : Table α)
    (h : t.all (fun p => p.2 == 0) = true) :
    eval scale letters t = 0 :=
  eval_eq_zero_of_rows scale letters t fun p hp => by
    simpa only [beq_iff_eq] using (List.all_eq_true.mp h) p hp

end FQFP.WordTable
