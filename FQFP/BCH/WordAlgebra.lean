/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Fin.VecNotation
public import FQFP.BCH.FreeMonoidInstances
public import FQFP.BCH.WordExpansion

/-!
# The free word algebra on two letters

BCH's degree-`k` terms are `ℚ`-linear combinations of length-`k` words on two letters, and the
cancellation identities of `SmallSDischarge.lean` are polynomial identities between such
combinations. Proving them in an abstract noncommutative ring forces `noncomm_ring` to normalise
hundreds of monomials at once, which does not fit the default heartbeat budget (see
`artifacts/bch-port.md` §3.3quater).

This file sets up the alternative: evaluate the identity in the *free* word algebra
`ℚ[FreeMonoid (Fin 2)]` — which *is* the free associative `ℚ`-algebra on two generators — and
compare coefficients there.

## Main results

* `wordAlgebraLift a b` — the evaluation `ℚ[FreeMonoid (Fin 2)] →ₐ[ℚ] 𝔸` sending the two generators
  to `a`, `b`. This is the map that turns a coefficient list into an element of `𝔸`.
* `wordAlgebraLift_injective` — the evaluation at the two *free* generators is injective, so an
  identity in `𝔸` follows from the corresponding coefficient identity.
* `wordEval_gen` — `wordEval` (from `WordExpansion.lean`) through the two generators is the
  monomial of the letter list: the bridge from a word pattern to a free-algebra basis vector.
* `coeff_mono`, `coeff_smul_mono`, `coeff_mono_mul`, `coeff_mono_sum` — reading coefficients.
* `prod_mono_aux` — a product of monomials is one monomial (concatenate the words, multiply the
  coefficients).
* `evalTab`, `mulTab`, `smulTab`, `evalTab_mulTab`, `evalTab_smulTab` — a *table* (a list of
  `(word, coefficient)` rows) is the data of a term, and evaluation turns the table operations into
  the ring operations (`evalTab_append` handles sums).
* `reprTab`, `evalTab_eq_reprTab`, `evalTab_eq_of_reprTab_eq` — **the criterion**: a table is its
  coefficient function, so two tables with the same coefficients evaluate equally, and a degree-`k`
  identity can be settled on `List` and `ℚ` data alone.

## Implementation notes

`MonoidAlgebra R M` is a one-field structure wrapping `M →₀ R`, so `MonoidAlgebra.coeff` and
`MonoidAlgebra.ofCoeff` are the two directions of that conversion and a `MonoidAlgebra.single` is
definitionally a `Finsupp.single`. Two consequences shape the proofs below:

* `Finsupp.single_eq_same` and friends act on the `Finsupp` presentation, so coefficient goals are
  stated so that `coeff` is already applied — never by inserting a `change`.
* `decide` and `native_decide` cannot settle an equation in `MonoidAlgebra` or in `Finsupp`: their
  `DecidableEq` passes through `Quot` and does not reduce. Coefficients are compared with `rw` and
  `norm_num`, and word equalities are decided by `decide` only as an *input* to a rewrite.

A monomial is written `q • MonoidAlgebra.of … (FreeMonoid.ofList l)` rather than
`MonoidAlgebra.single (FreeMonoid.ofList l) q`, so that the coefficient of a *product* of monomials
reduces by `smul_single'` instead of by a `Finsupp` convolution.

The `FreeMonoid.of` product is right-associated, while the canonical form used here is
`FreeMonoid.ofList l`; `ofList_mul` and `FreeMonoid.ofList_cons` are the two lemmas that move
between them.
-/

@[expose] public section

namespace FQFP.BCH.WordAlgebra

noncomputable section

/-! ### Evaluation of the free word algebra -/

/-- **The evaluation of the free word algebra in an arbitrary `ℚ`-algebra**: the two generators go
to `a` and `b`, and the word product becomes the ring product.

This is the `MonoidAlgebra` universal property `MonoidAlgebra.lift` along `FreeMonoid.lift ![a, b]`,
so it is a ring homomorphism: a coefficient list is evaluated by multiplying out its words. -/
noncomputable abbrev wordAlgebraLift {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    MonoidAlgebra ℚ (FreeMonoid (Fin 2)) →ₐ[ℚ] 𝔸 :=
  MonoidAlgebra.lift ℚ 𝔸 (FreeMonoid (Fin 2)) (FreeMonoid.lift ![a, b])

/-- The monoid hom `FreeMonoid (Fin 2) →* FreeAlgebra ℚ (Fin 2)` reading the two letters as the two
free generators. -/
private def freeGenerators : FreeMonoid (Fin 2) →* FreeAlgebra ℚ (Fin 2) :=
  FreeMonoid.lift (FreeAlgebra.ι ℚ)

/-- **`wordAlgebraLift` at the two free generators is the inverse of
`FreeAlgebra.equivMonoidAlgebraFreeMonoid`.** Both are `MonoidAlgebra.lift` along the same monoid
homomorphism; the only content is the identification of the two monoid homomorphisms. -/
private theorem wordAlgebraLift_free_eq_symm :
    (wordAlgebraLift (FreeAlgebra.ι ℚ (0 : Fin 2)) (FreeAlgebra.ι ℚ 1) :
        MonoidAlgebra ℚ (FreeMonoid (Fin 2)) →ₐ[ℚ] FreeAlgebra ℚ (Fin 2)) =
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Fin 2)).symm :
        MonoidAlgebra ℚ (FreeMonoid (Fin 2)) →ₐ[ℚ] FreeAlgebra ℚ (Fin 2)) := by
  have h : FreeMonoid.lift ![(FreeAlgebra.ι ℚ (0 : Fin 2)), FreeAlgebra.ι ℚ 1] =
      freeGenerators := by
    ext i
    fin_cases i <;> rfl
  rw [wordAlgebraLift, h, freeGenerators]
  rfl

/-- **The evaluation at the two free generators is injective.** An identity between two `𝔸`-valued
word expansions is therefore equivalent to the identity of their coefficient functions in the free
word algebra; the free algebra is only an auxiliary object in the proof. -/
theorem wordAlgebraLift_injective :
    Function.Injective
      (wordAlgebraLift (FreeAlgebra.ι ℚ (0 : Fin 2)) (FreeAlgebra.ι ℚ 1) :
        MonoidAlgebra ℚ (FreeMonoid (Fin 2)) → FreeAlgebra ℚ (Fin 2)) := by
  rw [wordAlgebraLift_free_eq_symm]
  exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ) (X := Fin 2)).symm.injective

/-! ### The monomial presentation

A word is a basis vector of the free word algebra, so a term is a finitely supported coefficient
function. `mono l q` is the basis vector of the word `l`, scaled by `q`. -/

/-- The two generators of the free word algebra on two letters, as a function on letters. -/
abbrev freeGen : Fin 2 → MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  (MonoidAlgebra.of ℚ (FreeMonoid (Fin 2))) ∘ FreeMonoid.of

/-- A monomial: the word `l` as a basis vector, scaled by `q`. -/
abbrev mono (l : List (Fin 2)) (q : ℚ) : MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  q • MonoidAlgebra.of ℚ (FreeMonoid (Fin 2)) (FreeMonoid.ofList l)

/-- A product of `ofList`s is the `ofList` of the concatenation. This is the direction that pushes
a product of words into canonical form. -/
lemma ofList_mul (a b : List (Fin 2)) :
    FreeMonoid.ofList a * FreeMonoid.ofList b = FreeMonoid.ofList (a ++ b) :=
  (FreeMonoid.ofList_append a b).symm

/-- A power of one letter is the word of replicated letters. -/
lemma of_pow_eq_ofList_replicate (k : Fin 2) (n : ℕ) :
    (FreeMonoid.of k : FreeMonoid (Fin 2)) ^ n = FreeMonoid.ofList (List.replicate n k) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ih, List.replicate_succ, FreeMonoid.ofList_cons]

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

/-- **`wordEval` through the two generators is a monomial**: the bridge from a word pattern to a
basis vector of the free word algebra. -/
lemma wordEval_gen {n : ℕ} (v : Fin n → Fin 2) : wordEval freeGen v = mono (List.ofFn v) 1 := by
  rw [wordEval]
  exact prod_eq_mono (List.ofFn v)

/-! ### Reading coefficients

A coefficient goal is stated with `MonoidAlgebra.coeff` applied, so that it is in the `Finsupp`
presentation that `Finsupp.single_apply` acts on. `MonoidAlgebra.coeff` and `MonoidAlgebra.ofCoeff`
are the two directions of the structure conversion, and `MonoidAlgebra.coeff_single` routes a
monomial into that presentation. -/

/-- **The coefficient of a monomial at a concrete word**: `q` on that word, `0` elsewhere. -/
lemma coeff_mono (l w : List (Fin 2)) (q : ℚ) :
    (mono l q).coeff (FreeMonoid.ofList w) = if w = l then q else 0 := by
  rw [mono, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
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

/-- The empty word's monomial is the identity. -/
lemma mono_nil : mono ([] : List (Fin 2)) (1 : ℚ) = 1 := by
  rw [mono, MonoidAlgebra.of_apply, FreeMonoid.ofList_nil, MonoidAlgebra.one_def, one_smul]

/-! ### Tables

A *table* is a list of `(word, coefficient)` rows — the data of a degree-`k` term. `prod_mono_aux`
says that the product of the monomials of a table is the monomial of the concatenated words with
the product of the coefficients, which is what makes coefficient comparison purely a computation on
data. -/

/-- **A product of monomials is one monomial**: the words concatenate, the coefficients multiply.
The accumulator-free form of `mono_mul` iterated. -/
lemma prod_mono_aux (t : List (List (Fin 2) × ℚ)) :
    ((t.map fun p => mono p.1 p.2).prod)
      = mono (t.map Prod.fst).flatten (t.map Prod.snd).prod := by
  induction t with
  | nil => simp [mono, MonoidAlgebra.one_def]
  | cons p t ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.flatten_cons, List.map_cons,
        List.prod_cons, mono_mul]

/-- **The coefficient of a sum of monomials, as data**: the coefficients of the rows whose word
is `w`. This is what turns a coefficient comparison into `List`/`ℚ` arithmetic. -/
lemma coeff_mono_sum {ι : Type*} (s : Finset ι) (L : ι → List (Fin 2)) (C : ι → ℚ)
    (w : List (Fin 2)) :
    ((∑ i ∈ s, mono (L i) (C i) : MonoidAlgebra ℚ (FreeMonoid (Fin 2)))).coeff
        (FreeMonoid.ofList w)
      = ∑ i ∈ s, if w = L i then C i else 0 := by
  rw [MonoidAlgebra.coeff_sum (R := ℚ) (M := FreeMonoid (Fin 2)), Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => coeff_mono (L i) w (C i)

/-- A table's evaluation: the sum of its rows' monomials. -/
def evalTab (t : List (List (Fin 2) × ℚ)) : MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  (t.map fun p => mono p.1 p.2).sum

/-- **Row-wise product of two tables**: cartesian product, word concatenation, coefficient product.
This is the data-level multiplication that mirrors the ring multiplication. -/
def mulTab (s t : List (List (Fin 2) × ℚ)) : List (List (Fin 2) × ℚ) :=
  s.flatMap fun p => t.map fun r => (p.1 ++ r.1, p.2 * r.2)

lemma evalTab_nil : evalTab ([] : List (List (Fin 2) × ℚ)) = 0 := rfl

lemma evalTab_cons (p : List (Fin 2) × ℚ) (t : List (List (Fin 2) × ℚ)) :
    evalTab (p :: t) = mono p.1 p.2 + evalTab t := by
  rw [evalTab, List.map_cons, List.sum_cons]
  rfl

lemma evalTab_append (s t : List (List (Fin 2) × ℚ)) :
    evalTab (s ++ t) = evalTab s + evalTab t := by
  induction s with
  | nil => rw [List.nil_append, evalTab_nil, zero_add]
  | cons p s ih => rw [List.cons_append, evalTab_cons, ih, evalTab_cons, add_assoc]

lemma evalTab_mul_single (p : List (Fin 2) × ℚ) (t : List (List (Fin 2) × ℚ)) :
    evalTab (t.map fun r => (p.1 ++ r.1, p.2 * r.2)) = mono p.1 p.2 * evalTab t := by
  induction t with
  | nil => rw [List.map_nil, evalTab_nil, mul_zero]
  | cons r t ih =>
      rw [List.map_cons, evalTab_cons, ih, evalTab_cons, mul_add, mono_mul]

/-- **The evaluation of a table product is the product of the evaluations.** This is what lets a
ring expression built from degree-`k` pieces be computed entirely on tables. -/
lemma evalTab_mulTab (s t : List (List (Fin 2) × ℚ)) :
    evalTab (mulTab s t) = evalTab s * evalTab t := by
  induction s with
  | nil =>
      change evalTab ([] : List (List (Fin 2) × ℚ)) = evalTab ([] : List (List (Fin 2) × ℚ)) * _
      rw [evalTab_nil, zero_mul]
  | cons p s ih =>
      change evalTab (List.flatMap (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t)
          (p :: s)) = _
      rw [List.flatMap_cons, evalTab_append, evalTab_mul_single, evalTab_cons, add_mul]
      rw [show evalTab (List.flatMap (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) s)
          = evalTab s * evalTab t from ih]

/-- Scale every coefficient of a table. -/
def smulTab (c : ℚ) (t : List (List (Fin 2) × ℚ)) : List (List (Fin 2) × ℚ) :=
  t.map fun p => (p.1, c * p.2)

/-- **The evaluation of a scaled table is the scalar multiple of the evaluation.** -/
lemma evalTab_smulTab (c : ℚ) (t : List (List (Fin 2) × ℚ)) :
    evalTab (smulTab c t) = c • evalTab t := by
  induction t with
  | nil => rw [smulTab, List.map_nil, evalTab_nil, smul_zero]
  | cons p t ih =>
      change mono p.1 (c * p.2) + evalTab (smulTab c t) = c • evalTab (p :: t)
      rw [ih, evalTab_cons, smul_add]
      congr 1
      exact (show c • mono p.1 p.2 = mono p.1 (c * p.2) from by rw [mono, mono, smul_smul]).symm

/-- **The coefficient of a list of monomials, as data**: the rows whose word is `w`, with their
coefficients. This is the list-level companion of `coeff_mono_sum`, and it is what turns a
coefficient comparison of two tables into `List` and `ℚ` arithmetic.

Stated with `w` a `List` so that `iteration` can decide the row conditions by `decide`; the
`FreeMonoid` form follows by `FreeMonoid.toList`. -/
lemma coeff_mono_list (t : List (List (Fin 2) × ℚ)) (w : List (Fin 2)) :
    (evalTab t).coeff (FreeMonoid.ofList w)
      = (t.map fun p => if p.1 = w then p.2 else 0).sum := by
  induction t with
  | nil => rw [evalTab_nil, List.map_nil, List.sum_nil]; rfl
  | cons p t ih =>
      rw [evalTab_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih,
        List.map_cons, List.sum_cons, coeff_mono]
      by_cases h : p.1 = w
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right]
        intro hc
        exact h hc.symm

/-! ### From a table to its coefficient function

`evalTab_eq_reprTab` turns a table into one `Finsupp.single` per row, so two tables can be compared
through their coefficient functions instead of through the ring.
`evalTab_eq_of_reprTab_eq` is then the criterion: **equal coefficient functions give equal
evaluations**, which is what lets a degree-`k` identity be settled on data. -/

/-- The `Finsupp` a table represents: one `single` per row. -/
def reprTab : List (List (Fin 2) × ℚ) → FreeMonoid (Fin 2) →₀ ℚ
  | [] => 0
  | p :: t => Finsupp.single (FreeMonoid.ofList p.1) p.2 + reprTab t

/-- **The bridge**: evaluating a table gives the `Finsupp` the table represents. -/
theorem evalTab_eq_reprTab (t : List (List (Fin 2) × ℚ)) :
    evalTab t = MonoidAlgebra.ofCoeff (reprTab t) := by
  induction t with
  | nil => rw [evalTab_nil, reprTab, MonoidAlgebra.ofCoeff_zero]
  | cons p t ih =>
      rw [evalTab_cons, ih, reprTab, MonoidAlgebra.ofCoeff_add]
      congr 1
      rw [mono, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
      exact (show MonoidAlgebra.single (FreeMonoid.ofList p.1) p.2
          = MonoidAlgebra.ofCoeff (Finsupp.single (FreeMonoid.ofList p.1) p.2) from rfl)

/-- **The criterion**: tables with the same coefficient function evaluate equally. -/
theorem evalTab_eq_of_reprTab_eq {s t : List (List (Fin 2) × ℚ)} (h : reprTab s = reprTab t) :
    evalTab s = evalTab t := by
  rw [evalTab_eq_reprTab, evalTab_eq_reprTab, h]

/-- **The coefficient of a table's representation, pointwise**: the rows whose word is `l`, with
their coefficients. With this, `reprTab` comparisons are sums over `List` and `ℚ` only, so a table
identity can be checked word by word without any `Decidable`-instance rewriting. -/
lemma reprTab_apply_eq (t : List (List (Fin 2) × ℚ)) (l : List (Fin 2)) :
    reprTab t (FreeMonoid.ofList l) = (t.map fun p => if p.1 = l then p.2 else (0 : ℚ)).sum := by
  induction t with
  | nil => rw [reprTab, List.map_nil, List.sum_nil]; rfl
  | cons p t ih =>
      rw [reprTab, Finsupp.add_apply, ih, List.map_cons, List.sum_cons]
      by_cases h : p.1 = l
      · rw [show (if p.1 = l then p.2 else (0 : ℚ)) = p.2 from ite_eq_left h]
        rw [show (Finsupp.single (FreeMonoid.ofList p.1) p.2 : FreeMonoid (Fin 2) →₀ ℚ)
              (FreeMonoid.ofList l) = p.2 from by
            rw [show FreeMonoid.ofList l = FreeMonoid.ofList p.1 from h.symm]
            exact Finsupp.single_eq_same]
      · rw [show (if p.1 = l then p.2 else (0 : ℚ)) = (0 : ℚ) from ite_eq_right h]
        rw [show (Finsupp.single (FreeMonoid.ofList p.1) p.2 : FreeMonoid (Fin 2) →₀ ℚ)
              (FreeMonoid.ofList l) = (0 : ℚ) from by
            exact Finsupp.single_eq_of_ne (M := ℚ) (a := FreeMonoid.ofList p.1)
              (a' := FreeMonoid.ofList l) (by
                intro hc
                exact h (FreeMonoid.ofList.injective hc.symm))]

end

end FQFP.BCH.WordAlgebra
