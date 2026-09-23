/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

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
* `wordAlgebraLift_mono`, `wordAlgebraLift_evalTab` — the evaluation read off a monomial and off a
  table. These are what carry a statement *about tables* into `𝔸`.
* `wordEval_gen` — `wordEval` (from `WordExpansion.lean`) through the two generators is the
  monomial of the letter list: the bridge from a word pattern to a free-algebra basis vector.
* `coeff_mono`, `coeff_smul_mono`, `coeff_mono_mul`, `coeff_mono_sum` — reading coefficients.
* `prod_mono_aux` — a product of monomials is one monomial (concatenate the words, multiply the
  coefficients).
* `Tab` — a *table*: a list of `(word, coefficient)` rows, i.e. the data of a term.
* `evalTab`, `mulTab`, `smulTab`, `evalTab_mulTab`, `evalTab_smulTab` — evaluation turns the table
  operations into the ring operations (`evalTab_append` handles sums).
* `reprTab`, `evalTab_eq_reprTab`, `evalTab_eq_of_reprTab_eq`, `reprTab_apply_eq`, `reprTab_append`,
  `reprTab_smulTab` — **the criterion**: a table is its coefficient function, so two tables with the
  same coefficients evaluate equally, and a degree-`k` identity can be settled on `List` and `ℚ`
  data alone.

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

Two facts shape what can be *decided* here, as opposed to merely stated:

* **`ℚ` has no kernel reduction.** `(2 : ℚ) * 3 = 6` is not `rfl`, `(q : ℚ).num` does not reduce,
  and `DecidableEq ℚ` does not reduce either, so `rfl` and `decide` can settle *words*
  (`List (Fin 2)` equality does reduce) but never *coefficients*. Coefficient arithmetic is
  `norm_num`'s job, and one `norm_num` over a few hundred `ℚ` terms already runs past the default
  heartbeat budget. That is why a term is compared table by table and word by word instead of in a
  single goal.
* **Injectivity into the free algebra is not needed here.** The transfer used downstream goes from
  the free word algebra *to* `𝔸`, and a ring homomorphism carries identities forward on its own; an
  injective evaluation is only needed for the reverse direction, which nothing in this development
  uses. `wordAlgebraLift_mono` at `l = [k]`, `q = 1` identifies the two generators.
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

/-- A *table*: rows of `(word, coefficient)`. This is the data of a term of the free word algebra,
and the type on which coefficient comparison is a computation on `List` and `ℚ` alone. -/
abbrev Tab : Type := List (List (Fin 2) × ℚ)

/-- **A product of monomials is one monomial**: the words concatenate, the coefficients multiply.
The accumulator-free form of `mono_mul` iterated. -/
lemma prod_mono_aux (t : Tab) :
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
def evalTab (t : Tab) : MonoidAlgebra ℚ (FreeMonoid (Fin 2)) :=
  (t.map fun p => mono p.1 p.2).sum

/-- **Row-wise product of two tables**: cartesian product, word concatenation, coefficient product.
This is the data-level multiplication that mirrors the ring multiplication. -/
def mulTab (s t : Tab) : Tab :=
  s.flatMap fun p => t.map fun r => (p.1 ++ r.1, p.2 * r.2)

lemma evalTab_nil : evalTab ([] : Tab) = 0 := rfl

lemma evalTab_cons (p : List (Fin 2) × ℚ) (t : Tab) :
    evalTab (p :: t) = mono p.1 p.2 + evalTab t := by
  rw [evalTab, List.map_cons, List.sum_cons]
  rfl

lemma evalTab_append (s t : Tab) :
    evalTab (s ++ t) = evalTab s + evalTab t := by
  induction s with
  | nil => rw [List.nil_append, evalTab_nil, zero_add]
  | cons p s ih => rw [List.cons_append, evalTab_cons, ih, evalTab_cons, add_assoc]

lemma evalTab_mul_single (p : List (Fin 2) × ℚ) (t : Tab) :
    evalTab (t.map fun r => (p.1 ++ r.1, p.2 * r.2)) = mono p.1 p.2 * evalTab t := by
  induction t with
  | nil => rw [List.map_nil, evalTab_nil, mul_zero]
  | cons r t ih =>
      rw [List.map_cons, evalTab_cons, ih, evalTab_cons, mul_add, mono_mul]

/-- **The evaluation of a table product is the product of the evaluations.** This is what lets a
ring expression built from degree-`k` pieces be computed entirely on tables. -/
lemma evalTab_mulTab (s t : Tab) :
    evalTab (mulTab s t) = evalTab s * evalTab t := by
  induction s with
  | nil =>
      change evalTab ([] : Tab) = evalTab ([] : Tab) * _
      rw [evalTab_nil, zero_mul]
  | cons p s ih =>
      change evalTab (List.flatMap (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t)
          (p :: s)) = _
      rw [List.flatMap_cons, evalTab_append, evalTab_mul_single, evalTab_cons, add_mul]
      rw [show evalTab (List.flatMap (fun p => List.map (fun r => (p.1 ++ r.1, p.2 * r.2)) t) s)
          = evalTab s * evalTab t from ih]

/-- Scale every coefficient of a table. -/
def smulTab (c : ℚ) (t : Tab) : Tab :=
  t.map fun p => (p.1, c * p.2)

/-- **The evaluation of a scaled table is the scalar multiple of the evaluation.** -/
lemma evalTab_smulTab (c : ℚ) (t : Tab) :
    evalTab (smulTab c t) = c • evalTab t := by
  induction t with
  | nil => rw [smulTab, List.map_nil, evalTab_nil, smul_zero]
  | cons p t ih =>
      change mono p.1 (c * p.2) + evalTab (smulTab c t) = c • evalTab (p :: t)
      rw [ih, evalTab_cons, smul_add]
      congr 1
      exact (show c • mono p.1 p.2 = mono p.1 (c * p.2) from by rw [mono, mono, smul_smul]).symm

/-- A one-row table evaluates to its monomial. -/
lemma evalTab_singleton (p : List (Fin 2) × ℚ) : evalTab [p] = mono p.1 p.2 := by
  rw [evalTab_cons, evalTab_nil, add_zero]

/-- The one-row table of the empty word with coefficient `1`: the identity of `mulTab`, and hence
the base case of `powTab`. -/
def unitTab : Tab := [([], 1)]

/-- **The unit table evaluates to `1`.** -/
lemma evalTab_unitTab : evalTab unitTab = 1 := by
  rw [unitTab, evalTab_singleton, mono_nil]

/-- **The `n`-fold product of a table with itself**: the data-level counterpart of `^`. A graded
piece such as `z ^ 6` has to be computed as a table before it can be compared. -/
def powTab (t : Tab) : ℕ → Tab
  | 0 => unitTab
  | n + 1 => mulTab (powTab t n) t

lemma powTab_zero (t : Tab) : powTab t 0 = unitTab := rfl

lemma powTab_succ (t : Tab) (n : ℕ) : powTab t (n + 1) = mulTab (powTab t n) t := rfl

/-- **The evaluation of a table power is the power of the evaluation.** -/
lemma evalTab_powTab (t : Tab) (n : ℕ) : evalTab (powTab t n) = evalTab t ^ n := by
  induction n with
  | zero => rw [powTab_zero, evalTab_unitTab, pow_zero]
  | succ n ih => rw [powTab_succ, evalTab_mulTab, ih, pow_succ]

/-- **The coefficient of a list of monomials, as data**: the rows whose word is `w`, with their
coefficients. This is the list-level companion of `coeff_mono_sum`, and it is what turns a
coefficient comparison of two tables into `List` and `ℚ` arithmetic.

Stated with `w` a `List` so that `iteration` can decide the row conditions by `decide`; the
`FreeMonoid` form follows by `FreeMonoid.toList`. -/
lemma coeff_mono_list (t : Tab) (w : List (Fin 2)) :
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
def reprTab : Tab → FreeMonoid (Fin 2) →₀ ℚ
  | [] => 0
  | p :: t => Finsupp.single (FreeMonoid.ofList p.1) p.2 + reprTab t

/-- **The bridge**: evaluating a table gives the `Finsupp` the table represents. -/
theorem evalTab_eq_reprTab (t : Tab) :
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
theorem evalTab_eq_of_reprTab_eq {s t : Tab} (h : reprTab s = reprTab t) :
    evalTab s = evalTab t := by
  rw [evalTab_eq_reprTab, evalTab_eq_reprTab, h]

/-- **A table's representation is additive in the rows**: the coefficient function of a
concatenation is the sum of the coefficient functions. This is what lets a term be assembled piece
by piece without ever unfolding the pieces. -/
lemma reprTab_append (s t : Tab) : reprTab (s ++ t) = reprTab s + reprTab t := by
  induction s with
  | nil => rw [List.nil_append, reprTab, zero_add]
  | cons p s ih => rw [List.cons_append, reprTab, reprTab, ih, add_assoc]

/-- **A table's representation is the coefficient function of its evaluation.** Every coefficient
statement about `evalTab` is therefore a statement about `reprTab`, and conversely. -/
lemma reprTab_eq_coeff (t : Tab) : reprTab t = (evalTab t).coeff := by
  rw [evalTab_eq_reprTab, MonoidAlgebra.coeff_ofCoeff]

/-- **A table's representation is homogeneous**: scaling every coefficient scales the coefficient
function. -/
lemma reprTab_smulTab (c : ℚ) (t : Tab) : reprTab (smulTab c t) = c • reprTab t := by
  rw [reprTab_eq_coeff, reprTab_eq_coeff, evalTab_smulTab, MonoidAlgebra.coeff_smul]

/-- **The coefficient of a table's representation, pointwise**: the rows whose word is `l`, with
their coefficients. With this, `reprTab` comparisons are sums over `List` and `ℚ` only, so a table
identity can be checked word by word without any `Decidable`-instance rewriting. -/
lemma reprTab_apply_eq (t : Tab) (l : List (Fin 2)) :
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

/-! ### Evaluating a table in an algebra

The two lemmas below read `wordAlgebraLift a b` off a monomial and off a table, so a statement
*about tables* becomes a statement about `𝔸`. Only the forward direction is needed: the evaluation
is a ring homomorphism, so an identity of tables carries over by `map_zero` and friends, and no
injectivity is involved. -/

/-- **The evaluation of a monomial**: `a` and `b` replace the two letters, and the coefficient comes
out as the scalar. At `l = [0]`, `q = 1` (and likewise `l = [1]`) this is
`wordAlgebraLift a b (mono [0] 1) = a`, which is how the two generators are identified. -/
theorem wordAlgebraLift_mono {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸)
    (l : List (Fin 2)) (q : ℚ) :
    wordAlgebraLift a b (mono l q) = q • (l.map ![a, b]).prod := by
  have h : wordAlgebraLift a b (MonoidAlgebra.of ℚ (FreeMonoid (Fin 2)) (FreeMonoid.ofList l))
      = (l.map ![a, b]).prod := by
    rw [wordAlgebraLift, MonoidAlgebra.lift_of, FreeMonoid.lift_ofList]
  rw [mono, map_smul, h]

/-- **The evaluation of a table**: the rows are evaluated one by one and summed. This is the
statement that defines a degree-`k` term written as `wordAlgebraLift a b (evalTab t)`. -/
theorem wordAlgebraLift_evalTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) (t : Tab) :
    wordAlgebraLift a b (evalTab t) = (t.map fun p => p.2 • (p.1.map ![a, b]).prod).sum := by
  induction t with
  | nil => rw [evalTab_nil, map_zero, List.map_nil, List.sum_nil]
  | cons p t ih =>
      rw [evalTab_cons, map_add, ih, List.map_cons, List.sum_cons, wordAlgebraLift_mono]

/-! ### Collapsing a table to one row per word

A table built by `mulTab` / `powTab` repeats words: the product of two tables has one row per pair
of rows, and many of those pairs give the same word. `collapse` merges them, so that the result has
one row per word and a coefficient comparison becomes a handful of small `ℚ` sums rather than one
sum over the whole product.

This is what makes the comparison affordable. `ℚ` has no kernel reduction, so a single `norm_num`
call over the thousands of terms of a raw product table runs past the default heartbeat budget,
while a collapsed table of at most `2 ^ k` rows is cheap. The merge tests only *word* equality,
which `List (Fin 2)` decides by kernel reduction, so `collapse` is computable and its lemmas are
plain inductions. -/

/-- Add one row to an accumulator, merging it with an equal word. The merged row carries `p.1`
as its word, which is the same word by the branch condition, so no projection is needed. -/
def addRow (p : List (Fin 2) × ℚ) : Tab → Tab
  | [] => [p]
  | r :: t => if r.1 = p.1 then (p.1, r.2 + p.2) :: t else r :: addRow p t

/-- Merge every row of a table into an accumulator, one row at a time. -/
def collapseAux : Tab → Tab → Tab
  | [], acc => acc
  | p :: t, acc => collapseAux t (addRow p acc)

/-- **The support-pinned normal form of a table**: one row per word. -/
def collapse (t : Tab) : Tab := collapseAux t []

/-- **Adding a row does not change the coefficient function.** -/
lemma reprTab_addRow (p : List (Fin 2) × ℚ) (acc : Tab) :
    reprTab (addRow p acc) = reprTab (p :: acc) := by
  induction acc with
  | nil => simp only [addRow, reprTab, add_zero]
  | cons r t ih =>
      rw [addRow]
      split_ifs with h
      · simp only [reprTab, h]
        rw [Finsupp.single_add]
        abel
      · simp only [reprTab]
        rw [ih]
        simp only [reprTab]
        abel

/-- **Collapsing does not change the coefficient function.** -/
lemma reprTab_collapseAux (t acc : Tab) :
    reprTab (collapseAux t acc) = reprTab acc + reprTab t := by
  induction t generalizing acc with
  | nil => simp only [collapseAux, reprTab, add_zero]
  | cons p t ih =>
      rw [collapseAux, ih, reprTab_addRow]
      simp only [reprTab]
      abel

/-- **A table and its collapsed form have the same coefficient function**: the criterion of this
file, in the form a degree-`k` identity is settled by. -/
lemma reprTab_collapse (t : Tab) : reprTab (collapse t) = reprTab t := by
  rw [collapse, reprTab_collapseAux]
  simp only [reprTab, zero_add]

/-- **A table and its collapsed form evaluate equally.** -/
lemma evalTab_collapse (t : Tab) : evalTab (collapse t) = evalTab t := by
  rw [evalTab_eq_reprTab, evalTab_eq_reprTab, reprTab_collapse]

end

end FQFP.BCH.WordAlgebra
