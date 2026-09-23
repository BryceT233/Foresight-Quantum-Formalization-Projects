/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Fin.VecNotation
public import FQFP.BCH.WordAlgebraLift
public import FQFP.BCH.WordExpansion

/-!
# Reading coefficients of a word expansion

`BCHTerms.lean` writes the degree-`k` BCH terms as `ℚ`-weighted sums of word monomials. The
degree-`k` cancellation identities of `SmallSDischarge.lean` are polynomial identities in such
sums, and proving them in an abstract noncommutative ring forces `noncomm_ring` to normalise
hundreds of monomials at once — which does not fit the default heartbeat budget (see
`artifacts/bch-port.md` §3.3quater).

This file supplies the alternative: evaluate the identity in the *free* word algebra
`MonoidAlgebra ℚ (FreeMonoid (Fin 2))`, where a word is a basis vector, and compare coefficients.
The bridge from a word pattern to a monomial is `wordEval_gen`, and `MonoidAlgebra.coeff` reads a
coefficient of the resulting free element.

## Main results

* `wordEval_gen` — `wordEval` through the two generators is the monomial of the letter list.
* `coeff_mono` — the coefficient of a monomial at a concrete word.
* `coeff_smul_mono` — the coefficient of a scaled monomial.
* `mono_pow` — powers of a single-letter monomial.
* `coeff_mono_mul` — the coefficient of a product of two monomials.

## Implementation notes

`MonoidAlgebra` is a one-field structure wrapping `Finsupp` (Mathlib v4.34.0), not a type synonym
for it. Consequences that the proofs below have to respect:

* `Finsupp.single_eq_same` does **not** rewrite a `MonoidAlgebra.single`: the goal must first be
  pushed to the `Finsupp` layer with `change`.
* `decide` and `native_decide` cannot settle an equation in `MonoidAlgebra` or in `Finsupp`:
  their `DecidableEq` goes through `Quot` and does not reduce.
* A monomial is written `q • MonoidAlgebra.of … (FreeMonoid.ofList l)`, so that the coefficient of
  a *product* of monomials reduces by `smul_single'` rather than by a `Finsupp` convolution.

The `FreeMonoid.of` product is right-associated, while the canonical form used here is
`FreeMonoid.ofList l`; `ofList_mul` and `FreeMonoid.ofList_cons` are the two lemmas that move
between them.
-/

@[expose] public section

namespace FQFP.BCH

noncomputable section

/-- The two generators of the free word algebra on two letters, as a function on letters. -/
abbrev freeGen : Fin 2 → MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  (MonoidAlgebra.of ℚ (FreeMonoid (Fin 2))) ∘ FreeMonoid.of

/-- A monomial: the word `l` as a basis vector, scaled by `q`. -/
abbrev mono (l : List (Fin 2)) (q : ℚ) : MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  q • MonoidAlgebra.of ℚ (FreeMonoid (Fin 2)) (FreeMonoid.ofList l)

/-- A product of `ofList`s is the `ofList` of the concatenation. This is the direction that
pushes a product of words into canonical form. -/
lemma ofList_mul (a b : List (Fin 2)) :
    FreeMonoid.ofList a * FreeMonoid.ofList b = FreeMonoid.ofList (a ++ b) :=
  (FreeMonoid.ofList_append a b).symm

/-- A power of one letter is the word of replicated letters. -/
lemma of_pow_eq_ofList_replicate (k : Fin 2) (n : ℕ) :
    (FreeMonoid.of k : FreeMonoid (Fin 2)) ^ n = FreeMonoid.ofList (List.replicate n k) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ih, List.replicate_succ, FreeMonoid.ofList_cons]

/-- A monomial in the `MonoidAlgebra.single` presentation. -/
lemma mono_eq_single (l : List (Fin 2)) (q : ℚ) :
    mono l q = MonoidAlgebra.single (FreeMonoid.ofList l) q := by
  rw [mono, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]

/-- A one-letter monomial is the corresponding generator. -/
lemma mono_singleton (k : Fin 2) : mono [k] 1 = freeGen k := by
  rw [freeGen, Function.comp_apply, mono, one_smul, FreeMonoid.ofList_singleton]

/-- The product of two monomials is the monomial of the concatenated word. -/
lemma mono_mul (l₁ l₂ : List (Fin 2)) (r₁ r₂ : ℚ) :
    mono l₁ r₁ * mono l₂ r₂ = mono (l₁ ++ l₂) (r₁ * r₂) := by
  rw [mono, mono, mono, smul_mul_smul_comm, ← map_mul, ← FreeMonoid.ofList_append]

/-- **The bridge**: a word read through the two generators is one monomial. -/
lemma prod_eq_mono (l : List (Fin 2)) : (l.map freeGen).prod = mono l 1 := by
  induction l with
  | nil =>
      rw [List.map_nil, List.prod_nil, mono, MonoidAlgebra.of_apply, FreeMonoid.ofList_nil,
        MonoidAlgebra.one_def, one_smul]
  | cons k t ih =>
      rw [List.map_cons, List.prod_cons, ih, ← mono_singleton k, mono_mul, List.singleton_append,
        mul_one]

/-- **`wordEval` through the two generators is a monomial.** -/
lemma wordEval_gen {n : ℕ} (v : Fin n → Fin 2) : wordEval freeGen v = mono (List.ofFn v) 1 := by
  rw [wordEval]
  exact prod_eq_mono (List.ofFn v)

/-- **The coefficient of a monomial at a concrete word**: `q` on that word, `0` elsewhere. -/
lemma coeff_mono (l w : List (Fin 2)) (q : ℚ) :
    (mono l q).coeff (FreeMonoid.ofList w) = if w = l then q else 0 := by
  rw [mono_eq_single]
  change (Finsupp.single (FreeMonoid.ofList l) q) (FreeMonoid.ofList w) = _
  rw [Finsupp.single_apply]
  by_cases h : w = l
  · subst h; simp
  · rw [ite_eq_right (fun hc => h (FreeMonoid.ofList.injective hc).symm), ite_eq_right h]

/-- **The coefficient of a scaled monomial**: the scalar multiplies the coefficient. -/
lemma coeff_smul_mono (c : ℚ) (l w : List (Fin 2)) (q : ℚ) :
    (c • mono l q).coeff (FreeMonoid.ofList w) = if w = l then c * q else 0 := by
  rw [show c • mono l q = mono l (c * q) from by rw [mono, mono, smul_smul]]
  exact coeff_mono l w (c * q)

/-- **The coefficient of a product of two monomials.** -/
lemma coeff_mono_mul (l₁ l₂ w : List (Fin 2)) (r₁ r₂ : ℚ) :
    (mono l₁ r₁ * mono l₂ r₂).coeff (FreeMonoid.ofList w)
      = if w = l₁ ++ l₂ then r₁ * r₂ else 0 := by
  rw [mono_mul]
  exact coeff_mono (l₁ ++ l₂) w (r₁ * r₂)

/-- **Powers of a single-letter monomial.** -/
lemma mono_pow (k : Fin 2) (n : ℕ) : (mono [k] 1) ^ n = mono (List.replicate n k) 1 := by
  induction n with
  | zero =>
      rw [pow_zero, List.replicate_zero, mono, MonoidAlgebra.of_apply, FreeMonoid.ofList_nil,
        MonoidAlgebra.one_def, one_smul]
  | succ n ih => rw [pow_succ, ih, List.replicate_succ', mono_mul, mul_one]

end

end FQFP.BCH
