/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.WordAlgebra
public import FQFP.BCH.FreeMonoidInstances
public import FQFP.BCH.SmallSDischarge

/-!
# The degree-6 cancellation identity, as a table identity

`SmallSDischarge.lean` states the degree-6 cancellation behind `bchSexticTerm` as a polynomial
identity in a general noncommutative ring:

    ½·W6 + ⅓·y3₆ - ¼·y4₆ + ⅕·y5₆ - ⅙·z⁶ - bchSexticTerm = 0.

Proving it there needs `noncomm_ring` on hundreds of monomials at once, which does not fit the
default heartbeat budget (see `artifacts/bch-port.md` §3.3quater). This file proves it in the free
word algebra instead, where the identity turns out to be an identity of *tables* — lists of
`(word, coefficient)` rows — and therefore of `List` and `ℚ` only.

`scripts/check_sextic_free_identity.py` verifies independently that the Dynkin/Ree side, built from
`z` and `T_k = Σ_n aⁿb^(k−n)/(n!(k−n)!)` by positive compositions, gives exactly the 28 rows of
`bchSexticTermWords / bchSexticTermCoeffs`.

## Main results

* `T` — the table of the degree-`k` part of `y = exp a * exp b - 1`.
* `T_one`, `T_two`, `T_three`, `T_four` — `evalTab (T k) = bchT k` at the two generators, for
  `k = 1,…,4`.
* `sexticTable_identity` (to come) — the Dynkin/Ree combination evaluates to `T 6`.

## Implementation notes

The proof recipe for one `T k` is fixed, and the last two steps are what make it work:

1. `evalTab` and `bchT k` unfold to a sum of monomials;
2. `mono_pow`, `mono_cube`, `mono_sq`, `mono_pow_four`, `mono_pow_five` turn each power of a
   one-letter monomial into a single monomial;
3. `smul_mono_eq` pushes each scalar into the coefficient;
4. `norm_num` with `mono`, the `List.append` lemmas, `FreeMonoid.ofList_*` **and `← mul_assoc`**
   normalises the words — the `← mul_assoc` is essential: `MonoidAlgebra.single_mul_single`
   produces right-associated `FreeMonoid` products while the table words are left-associated, and
   `abel` will not see the two sides as equal until both are in the same association;
5. `abel` reorders the summands.

The cost of steps 4 and 5 does not grow with the degree.
-/

@[expose] public section

namespace FQFP.BCH.SexticTable

noncomputable section

open FQFP.BCH
open FQFP.BCH.WordAlgebra

/-- **The degree-`k` part of `y = exp a * exp b - 1`**: the words `aⁿb^(k−n)` with coefficient
`1/(n!(k−n)!)`. -/
def T : (k : ℕ) → Tab
  | 0 => []
  | 1 => [([0], 1), ([1], 1)]
  | 2 => [([0, 0], 1 / 2), ([0, 1], 1), ([1, 1], 1 / 2)]
  | 3 => [([0, 0, 0], 1 / 6), ([0, 0, 1], 1 / 2), ([0, 1, 1], 1 / 2), ([1, 1, 1], 1 / 6)]
  | 4 => [([0, 0, 0, 0], 1 / 24), ([0, 0, 0, 1], 1 / 6), ([0, 0, 1, 1], 1 / 4),
          ([0, 1, 1, 1], 1 / 6), ([1, 1, 1, 1], 1 / 24)]
  | 5 => [([0, 0, 0, 0, 0], 1 / 120), ([0, 0, 0, 0, 1], 1 / 24), ([0, 0, 0, 1, 1], 1 / 12),
          ([0, 0, 1, 1, 1], 1 / 12), ([0, 1, 1, 1, 1], 1 / 24), ([1, 1, 1, 1, 1], 1 / 120)]
  | 6 => [([0, 0, 0, 0, 0, 0], 1 / 720), ([0, 0, 0, 0, 0, 1], 1 / 120),
          ([0, 0, 0, 0, 1, 1], 1 / 48), ([0, 0, 0, 1, 1, 1], 1 / 36),
          ([0, 0, 1, 1, 1, 1], 1 / 48), ([0, 1, 1, 1, 1, 1], 1 / 120),
          ([1, 1, 1, 1, 1, 1], 1 / 720)]
  | _ => []

/-- A square of a one-letter monomial, in list form. -/
lemma mono_sq (k : Fin 2) : (mono [k] 1) ^ 2 = mono [k, k] 1 := by
  rw [mono_pow, List.replicate_succ, List.replicate_one]

/-- A cube of a one-letter monomial, in list form. -/
lemma mono_cube (k : Fin 2) : (mono [k] 1) ^ 3 = mono [k, k, k] 1 := by
  rw [mono_pow, List.replicate_succ, List.replicate_succ, List.replicate_one]

/-- The fourth power of a one-letter monomial, in list form. -/
lemma mono_pow_four (k : Fin 2) : (mono [k] 1) ^ 4 = mono [k, k, k, k] 1 := by
  rw [mono_pow, List.replicate_succ, List.replicate_succ, List.replicate_succ,
    List.replicate_one]

/-- The fifth power of a one-letter monomial, in list form. -/
lemma mono_pow_five (k : Fin 2) : (mono [k] 1) ^ 5 = mono [k, k, k, k, k] 1 := by
  rw [mono_pow, List.replicate_succ, List.replicate_succ, List.replicate_succ,
    List.replicate_succ, List.replicate_one]

/-- A scalar multiple of a monomial, with the scalar pushed into the coefficient. -/
lemma smul_mono_eq (c : ℚ) (l : List (Fin 2)) (q : ℚ) :
    c • mono l q = mono l (c * q) := by
  rw [mono, mono, smul_smul]

/-- Normalise a word written out of single letters. -/
lemma ofList_pair : FreeMonoid.ofList [0, 1] = (FreeMonoid.of 0 : FreeMonoid (Fin 2))
    * FreeMonoid.of 1 := by
  rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]

/-- **The degree-1 table evaluates to `z = a + b`.** -/
lemma T_one : evalTab (T 1) = mono [0] 1 + mono [1] 1 := by
  rw [T, evalTab, List.map_cons, List.map_cons, List.map_nil, List.sum_cons, List.sum_cons,
    List.sum_nil, add_zero]

/-- **The degree-2 table evaluates to the degree-2 part of `y` at the two generators.** -/
lemma T_two : evalTab (T 2) = bchT2 (mono [0] 1) (mono [1] 1) := by
  rw [T, bchT2, evalTab]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [mono_sq 0, mono_sq 1, mono_mul, smul_mono_eq, smul_mono_eq]
  norm_num [mono, List.nil_append, List.cons_append, List.singleton_append, List.append_nil,
    FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]
  abel

/-- **The degree-3 table evaluates to the degree-3 part of `y` at the two generators.** -/
lemma T_three : evalTab (T 3) = bchT3 (mono [0] 1) (mono [1] 1) := by
  rw [T, bchT3, evalTab]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [mono_cube 0, mono_pow 0 2, mono_pow 1 2, mono_cube 1, mono_mul, mono_mul,
    smul_mono_eq, smul_mono_eq, smul_mono_eq, smul_mono_eq]
  norm_num [mono, List.nil_append, List.cons_append, List.singleton_append, List.append_nil,
    FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]
  abel

/-- **The degree-4 table evaluates to the degree-4 part of `y` at the two generators.** -/
lemma T_four : evalTab (T 4) = bchT4 (mono [0] 1) (mono [1] 1) := by
  rw [T, bchT4, evalTab]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [mono_pow_four 0, mono_cube 0, mono_sq 0, mono_sq 1, mono_cube 1, mono_pow_four 1]
  norm_num [smul_mono_eq, mono, ← mul_assoc, List.nil_append, List.cons_append,
    List.singleton_append, FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]
  abel

/-- **The degree-5 table evaluates to the degree-5 part of `y` at the two generators.** -/
lemma T_five : evalTab (T 5) = bchT5 (mono [0] 1) (mono [1] 1) := by
  rw [T, bchT5, evalTab]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [mono_pow_five 0, mono_pow_four 0, mono_cube 0, mono_sq 0,
    mono_pow_five 1, mono_pow_four 1, mono_cube 1, mono_sq 1]
  norm_num [smul_mono_eq, mono, ← mul_assoc, List.nil_append, List.cons_append,
    List.singleton_append, FreeMonoid.ofList_cons, FreeMonoid.ofList_singleton]
  abel

/-- **`z · T₅`** evaluates to the product `z * y_d5`. -/
lemma Z_mul_T5 :
    evalTab (mulTab (T 1) (T 5)) = (mono [0] 1 + mono [1] 1) * bchT5 (mono [0] 1) (mono [1] 1) := by
  rw [evalTab_mulTab, T_one, T_five]

/-- **`T₂ · T₄`** evaluates to the product `y_d2 * y_d4`. -/
lemma T2_mul_T4 :
    evalTab (mulTab (T 2) (T 4))
      = bchT2 (mono [0] 1) (mono [1] 1) * bchT4 (mono [0] 1) (mono [1] 1) := by
  rw [evalTab_mulTab, T_two, T_four]

/-! ### The degree-6 tables

`SmallSDischarge.septic_pure_identity` is the degree-6 cancellation

    ½·W6 + ⅓·(y³)_d6 - ¼·(y⁴)_d6 + ⅕·(y⁵)_d6 - ⅙·z⁶ - bchSexticTerm = 0.

Each of its six pieces is a table here, built from the `T k` tables by the operations of
`WordAlgebra`, so that the identity becomes a statement about tables:

* `w6Tab` — `W6 = 2·y_d6 - (y²)_d6`;
* `y36Tab`, `y46Tab`, `y56Tab` — the degree-6 parts of `y³`, `y⁴`, `y⁵`;
* `z6Tab` — `z⁶`;
* `sexticTab` — `bchSexticTerm` itself;
* `dynkin6Tab` — the whole left-hand side.

The `evalTab_*` lemmas below say that each table *is* the ring expression it mirrors, and they are
what carries the table identity back to `𝔸` through `wordAlgebraLift_evalTab`.

`bchSexticTerm` is stated for a `NormedRing`, so unlike the other five pieces it cannot be
evaluated at `mono [0] 1` / `mono [1] 1` (the free word algebra is not normed); `sexticTab` is
therefore bridged to it in an arbitrary `𝔸` rather than in the free algebra. -/

/-- `![mono [0] 1, mono [1] 1]` is the pair of free generators. -/
lemma mono_pair_eq_freeGen :
    (![mono [0] 1, mono [1] 1] : Fin 2 → MonoidAlgebra ℚ (FreeMonoid (Fin 2))) = freeGen := by
  funext i
  fin_cases i <;> exact mono_singleton _

/-- The degree-6 `W6` table, mirroring `bchW6`. -/
def w6Tab : Tab :=
  smulTab ((360 : ℚ)⁻¹) [([0, 0, 0, 0, 0, 0], 1)] ++
    smulTab ((60 : ℚ)⁻¹) [([0, 0, 0, 0, 0, 1], 1)] ++
    smulTab ((24 : ℚ)⁻¹) [([0, 0, 0, 0, 1, 1], 1)] ++
    smulTab ((18 : ℚ)⁻¹) [([0, 0, 0, 1, 1, 1], 1)] ++
    smulTab ((24 : ℚ)⁻¹) [([0, 0, 1, 1, 1, 1], 1)] ++
    smulTab ((60 : ℚ)⁻¹) [([0, 1, 1, 1, 1, 1], 1)] ++
    smulTab ((360 : ℚ)⁻¹) [([1, 1, 1, 1, 1, 1], 1)] ++
    smulTab (-1) (mulTab (T 1) (T 5)) ++ smulTab (-1) (mulTab (T 2) (T 4)) ++
    smulTab (-1) (mulTab (T 3) (T 3)) ++ smulTab (-1) (mulTab (T 4) (T 2)) ++
    smulTab (-1) (mulTab (T 5) (T 1))

/-- **`W6` as a table**: `evalTab w6Tab = bchW6 (mono [0] 1) (mono [1] 1)`. -/
lemma evalTab_w6Tab : evalTab w6Tab = bchW6 (mono [0] 1) (mono [1] 1) := by
  simp only [w6Tab, bchW6, bchZ, evalTab_append, evalTab_smulTab, evalTab_mulTab, evalTab_cons,
    evalTab_nil, add_zero, T_one, T_five, T_two, T_four, T_three, mono_pow, mono_mul,
    smul_mono_eq, mul_one, neg_one_smul, List.replicate_succ, List.replicate_zero,
    List.cons_append, List.nil_append, sub_eq_add_neg, neg_add, add_assoc]

/-- The degree-6 `(y³)_d6` table, mirroring `bchY36`. -/
def y36Tab : Tab :=
  mulTab (powTab (T 1) 2) (T 4) ++ mulTab (mulTab (T 1) (T 4)) (T 1) ++
    mulTab (T 4) (powTab (T 1) 2) ++ mulTab (mulTab (T 1) (T 2)) (T 3) ++
    mulTab (mulTab (T 1) (T 3)) (T 2) ++ mulTab (mulTab (T 2) (T 1)) (T 3) ++
    mulTab (mulTab (T 2) (T 3)) (T 1) ++ mulTab (mulTab (T 3) (T 1)) (T 2) ++
    mulTab (mulTab (T 3) (T 2)) (T 1) ++ powTab (T 2) 3

/-- **`(y³)_d6` as a table**: `evalTab y36Tab = bchY36 (mono [0] 1) (mono [1] 1)`. -/
lemma evalTab_y36Tab : evalTab y36Tab = bchY36 (mono [0] 1) (mono [1] 1) := by
  simp only [y36Tab, bchY36, bchZ, evalTab_append, evalTab_mulTab, evalTab_powTab,
    T_one, T_two, T_three, T_four]

/-- The degree-6 `(y⁴)_d6` table, mirroring `bchY46`. -/
def y46Tab : Tab :=
  mulTab (powTab (T 1) 3) (T 3) ++ mulTab (mulTab (powTab (T 1) 2) (T 3)) (T 1) ++
    mulTab (mulTab (T 1) (T 3)) (powTab (T 1) 2) ++ mulTab (T 3) (powTab (T 1) 3) ++
    mulTab (powTab (T 1) 2) (powTab (T 2) 2) ++
    mulTab (mulTab (mulTab (T 1) (T 2)) (T 1)) (T 2) ++
    mulTab (mulTab (T 1) (powTab (T 2) 2)) (T 1) ++
    mulTab (mulTab (T 2) (powTab (T 1) 2)) (T 2) ++
    mulTab (mulTab (mulTab (T 2) (T 1)) (T 2)) (T 1) ++
    mulTab (powTab (T 2) 2) (powTab (T 1) 2)

/-- **`(y⁴)_d6` as a table**: `evalTab y46Tab = bchY46 (mono [0] 1) (mono [1] 1)`. -/
lemma evalTab_y46Tab : evalTab y46Tab = bchY46 (mono [0] 1) (mono [1] 1) := by
  simp only [y46Tab, bchY46, bchZ, evalTab_append, evalTab_mulTab, evalTab_powTab,
    T_one, T_two, T_three]

/-- The degree-6 `(y⁵)_d6` table, mirroring `bchY56`. -/
def y56Tab : Tab :=
  mulTab (powTab (T 1) 4) (T 2) ++ mulTab (mulTab (powTab (T 1) 3) (T 2)) (T 1) ++
    mulTab (mulTab (powTab (T 1) 2) (T 2)) (powTab (T 1) 2) ++
    mulTab (mulTab (T 1) (T 2)) (powTab (T 1) 3) ++ mulTab (T 2) (powTab (T 1) 4)

/-- **`(y⁵)_d6` as a table**: `evalTab y56Tab = bchY56 (mono [0] 1) (mono [1] 1)`. -/
lemma evalTab_y56Tab : evalTab y56Tab = bchY56 (mono [0] 1) (mono [1] 1) := by
  simp only [y56Tab, bchY56, bchZ, evalTab_append, evalTab_mulTab, evalTab_powTab,
    T_one, T_two]

/-- The degree-6 `z⁶` table, mirroring `bchZ · bchZ ^ 5`. -/
def z6Tab : Tab := powTab (T 1) 6

/-- The `z⁶` table's evaluation at the two generators: `z = a + b` raised to the sixth. -/
lemma evalTab_z6Tab : evalTab z6Tab = bchZ (mono [0] 1) (mono [1] 1) ^ 6 := by
  rw [z6Tab, evalTab_powTab, T_one, bchZ]

/-- **`bchSexticTerm`'s table**: `bchSexticTerm` is *defined* by evaluating `bchSexticTermTable`, so
this is the table itself, not a copy of it. -/
def sexticTab : Tab := bchSexticTermTable

/-- **The evaluation of the sextic table is `bchSexticTerm` itself**: with `sexticTab` being
`bchSexticTermTable` this is `rfl`-level, which is the point of defining the term from its table. -/
theorem wordAlgebraLift_sexticTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab sexticTab) = bchSexticTerm a b :=
  rfl

/-- **The degree-6 Dynkin side as a table**: the left-hand side of `septic_pure_identity`.

Marked `irreducible` on purpose: it is a ~1000-row term, and the coefficient comparison below
compares goals whose type mentions it, so letting `whnf` and `isDefEq` unfold it would put the whole
table into every type comparison. The proofs unfold it explicitly where they need to. -/
@[irreducible] def dynkin6Tab : Tab :=
  smulTab ((2 : ℚ)⁻¹) w6Tab ++ smulTab ((3 : ℚ)⁻¹) y36Tab ++
    smulTab (-(4 : ℚ)⁻¹) y46Tab ++ smulTab ((5 : ℚ)⁻¹) y56Tab ++
    smulTab (-(6 : ℚ)⁻¹) z6Tab ++ smulTab (-1) sexticTab

/-! ### Carrying the table identity into `𝔸`

`wordAlgebraLift_sexticTab` above is `rfl`, because `bchSexticTerm` *is* its table evaluated. The
bridges below do the same for the other five pieces, by evaluating the free-algebra statement
`evalTab_*` and then pushing `wordAlgebraLift` through the ring expression with `map_*`. Together
with `wordAlgebraLift_dynkin6Tab` they carry the table identity `evalTab dynkin6Tab = 0` into the
statement of `septic_pure_identity`. -/

/-- The evaluation of the `W6` table is `bchW6`. -/
theorem wordAlgebraLift_evalTab_w6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab w6Tab) = bchW6 a b := by
  rw [evalTab_w6Tab]
  simp only [bchW6, bchZ, bchT2, bchT3, bchT4, bchT5]
  simp

/-- The evaluation of the `(y³)_d6` table is `bchY36`. -/
theorem wordAlgebraLift_evalTab_y36Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab y36Tab) = bchY36 a b := by
  rw [evalTab_y36Tab]
  simp only [bchY36, bchZ, bchT2, bchT3, bchT4]
  simp

/-- The evaluation of the `(y⁴)_d6` table is `bchY46`. -/
theorem wordAlgebraLift_evalTab_y46Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab y46Tab) = bchY46 a b := by
  rw [evalTab_y46Tab]
  simp only [bchY46, bchZ, bchT2, bchT3]
  simp

/-- The evaluation of the `(y⁵)_d6` table is `bchY56`. -/
theorem wordAlgebraLift_evalTab_y56Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab y56Tab) = bchY56 a b := by
  rw [evalTab_y56Tab]
  simp only [bchY56, bchZ, bchT2]
  simp

/-- The evaluation of the `z⁶` table is `bchZ` raised to the sixth. -/
theorem wordAlgebraLift_evalTab_z6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab z6Tab) = bchZ a b ^ 6 := by
  rw [evalTab_z6Tab]
  simp only [bchZ]
  simp

/-- **The degree-6 left-hand side, evaluated in an arbitrary `ℚ`-algebra.** -/
theorem wordAlgebraLift_dynkin6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    wordAlgebraLift a b (evalTab dynkin6Tab)
      = (2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b - (4 : ℚ)⁻¹ • bchY46 a b +
        (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 - bchSexticTerm a b := by
  unfold dynkin6Tab
  simp only [evalTab_append, evalTab_smulTab, map_add, map_smul]
  rw [wordAlgebraLift_evalTab_w6Tab, wordAlgebraLift_evalTab_y36Tab,
    wordAlgebraLift_evalTab_y46Tab, wordAlgebraLift_evalTab_y56Tab,
    wordAlgebraLift_evalTab_z6Tab, wordAlgebraLift_sexticTab]
  simp only [sub_eq_add_neg, neg_smul, one_smul]

/-! ### The coefficient comparison

The identity is now a statement about one table, and a table is its coefficient function. So the
comparison is: every coefficient of `dynkin6Tab` vanishes. `reprTab_eq_zero_of_length` splits that
into the two facts below — the rows are all six letters long, and a six-letter word is one of the
`2 ^ 6` `fin_cases` cases — so the unfolding is done once per word and nowhere else.

The unfolding genuinely has ~1000 nested `List.cons` cells, which is what the `maxRecDepth` below is
for. It is a *tactic recursion depth* limit on walking that term, not a search budget, and no
heartbeat budget is raised. -/

set_option maxRecDepth 100000

/-- A list of length six is six letters. -/
private lemma length_eq_six {α : Type*} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rcases t with _ | ⟨g, t⟩
    · exact ⟨a, b, c, d, e, f, rfl⟩
    · simp at h

/-- **Every row of the degree-6 table is a six-letter word.** Each piece is read off by `List.all`,
which costs one pass over that piece's rows and no coefficient arithmetic; `dynkin6Tab` is then the
combination of the six, so the whole table is never unfolded here. -/
lemma dynkin6Tab_rows_length : ∀ p ∈ dynkin6Tab, p.1.length = 6 := by
  have hw6 : ∀ p ∈ w6Tab, p.1.length = 6 := by
    have hall : w6Tab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  have hy36 : ∀ p ∈ y36Tab, p.1.length = 6 := by
    have hall : y36Tab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  have hy46 : ∀ p ∈ y46Tab, p.1.length = 6 := by
    have hall : y46Tab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  have hy56 : ∀ p ∈ y56Tab, p.1.length = 6 := by
    have hall : y56Tab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  have hz6 : ∀ p ∈ z6Tab, p.1.length = 6 := by
    have hall : z6Tab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  have hsex : ∀ p ∈ sexticTab, p.1.length = 6 := by
    have hall : sexticTab.all (fun p => p.1.length == 6) = true := by decide
    exact fun p hp => by simpa using (List.all_eq_true.mp hall) p hp
  unfold dynkin6Tab
  exact append_words_length
    (append_words_length
      (append_words_length
        (append_words_length
          (append_words_length (smulTab_words_length hw6) (smulTab_words_length hy36))
          (smulTab_words_length hy46))
        (smulTab_words_length hy56))
      (smulTab_words_length hz6))
    (smulTab_words_length hsex)

/-- The unfolding every degree-6 coefficient goal goes through: the six piece tables are expanded
and `norm_num` cancels the `ℚ` coefficients. It is a `macro` because the same three steps are needed
once per word, and the words are 64 *separate* declarations on purpose — see the theorem below. -/
macro "sexticCoeff" : tactic =>
  `(tactic|
    (rw [reprTab_apply_eq]
     simp only [dynkin6Tab, w6Tab, y36Tab, y46Tab, y56Tab, z6Tab, sexticTab, bchSexticTermTable,
      smulTab, mulTab, powTab, unitTab, T, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, List.append_nil]
     norm_num))

/-! The 64 coefficients, one declaration each: `sexticCoeff` is the whole proof. They are `private`
because they are one computation split 64 ways, not an API. -/
private lemma reprTab_dynkin6Tab_word_0 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_1 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_2 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_3 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_4 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_5 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_6 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_7 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 0, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_8 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_9 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_10 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_11 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_12 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_13 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_14 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_15 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 0, 1, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_16 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_17 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_18 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_19 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_20 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_21 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_22 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_23 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 0, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_24 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_25 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_26 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_27 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_28 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_29 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_30 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_31 :
    reprTab dynkin6Tab (FreeMonoid.ofList [0, 1, 1, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_32 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_33 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_34 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_35 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_36 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_37 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_38 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_39 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 0, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_40 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_41 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_42 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_43 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_44 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_45 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_46 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_47 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 0, 1, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_48 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_49 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_50 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_51 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_52 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_53 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_54 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_55 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 0, 1, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_56 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 0, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_57 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 0, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_58 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 0, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_59 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 0, 1, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_60 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 1, 0, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_61 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 1, 0, 1]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_62 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 1, 1, 0]) = 0 := by
  sexticCoeff

private lemma reprTab_dynkin6Tab_word_63 :
    reprTab dynkin6Tab (FreeMonoid.ofList [1, 1, 1, 1, 1, 1]) = 0 := by
  sexticCoeff

/-- **Every six-letter word's coefficient in `dynkin6Tab` vanishes.** The 64 cases are the 64
declarations above; `first` picks the one whose word matches, so this term is 64 references rather
than 64 unfoldings of the table. -/
theorem reprTab_dynkin6Tab_words (a b c d e f : Fin 2) :
    reprTab dynkin6Tab (FreeMonoid.ofList [a, b, c, d, e, f]) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f
  · exact reprTab_dynkin6Tab_word_0
  · exact reprTab_dynkin6Tab_word_1
  · exact reprTab_dynkin6Tab_word_2
  · exact reprTab_dynkin6Tab_word_3
  · exact reprTab_dynkin6Tab_word_4
  · exact reprTab_dynkin6Tab_word_5
  · exact reprTab_dynkin6Tab_word_6
  · exact reprTab_dynkin6Tab_word_7
  · exact reprTab_dynkin6Tab_word_8
  · exact reprTab_dynkin6Tab_word_9
  · exact reprTab_dynkin6Tab_word_10
  · exact reprTab_dynkin6Tab_word_11
  · exact reprTab_dynkin6Tab_word_12
  · exact reprTab_dynkin6Tab_word_13
  · exact reprTab_dynkin6Tab_word_14
  · exact reprTab_dynkin6Tab_word_15
  · exact reprTab_dynkin6Tab_word_16
  · exact reprTab_dynkin6Tab_word_17
  · exact reprTab_dynkin6Tab_word_18
  · exact reprTab_dynkin6Tab_word_19
  · exact reprTab_dynkin6Tab_word_20
  · exact reprTab_dynkin6Tab_word_21
  · exact reprTab_dynkin6Tab_word_22
  · exact reprTab_dynkin6Tab_word_23
  · exact reprTab_dynkin6Tab_word_24
  · exact reprTab_dynkin6Tab_word_25
  · exact reprTab_dynkin6Tab_word_26
  · exact reprTab_dynkin6Tab_word_27
  · exact reprTab_dynkin6Tab_word_28
  · exact reprTab_dynkin6Tab_word_29
  · exact reprTab_dynkin6Tab_word_30
  · exact reprTab_dynkin6Tab_word_31
  · exact reprTab_dynkin6Tab_word_32
  · exact reprTab_dynkin6Tab_word_33
  · exact reprTab_dynkin6Tab_word_34
  · exact reprTab_dynkin6Tab_word_35
  · exact reprTab_dynkin6Tab_word_36
  · exact reprTab_dynkin6Tab_word_37
  · exact reprTab_dynkin6Tab_word_38
  · exact reprTab_dynkin6Tab_word_39
  · exact reprTab_dynkin6Tab_word_40
  · exact reprTab_dynkin6Tab_word_41
  · exact reprTab_dynkin6Tab_word_42
  · exact reprTab_dynkin6Tab_word_43
  · exact reprTab_dynkin6Tab_word_44
  · exact reprTab_dynkin6Tab_word_45
  · exact reprTab_dynkin6Tab_word_46
  · exact reprTab_dynkin6Tab_word_47
  · exact reprTab_dynkin6Tab_word_48
  · exact reprTab_dynkin6Tab_word_49
  · exact reprTab_dynkin6Tab_word_50
  · exact reprTab_dynkin6Tab_word_51
  · exact reprTab_dynkin6Tab_word_52
  · exact reprTab_dynkin6Tab_word_53
  · exact reprTab_dynkin6Tab_word_54
  · exact reprTab_dynkin6Tab_word_55
  · exact reprTab_dynkin6Tab_word_56
  · exact reprTab_dynkin6Tab_word_57
  · exact reprTab_dynkin6Tab_word_58
  · exact reprTab_dynkin6Tab_word_59
  · exact reprTab_dynkin6Tab_word_60
  · exact reprTab_dynkin6Tab_word_61
  · exact reprTab_dynkin6Tab_word_62
  · exact reprTab_dynkin6Tab_word_63

/-- **The degree-6 coefficient comparison**: the Dynkin side is zero in the free word algebra. -/
theorem reprTab_dynkin6Tab_eq_zero : reprTab dynkin6Tab = 0 := by
  refine reprTab_eq_zero_of_length dynkin6Tab_rows_length fun l hl => ?_
  obtain ⟨a, b, c, d, e, f, rfl⟩ := length_eq_six hl
  exact reprTab_dynkin6Tab_words a b c d e f

/-- **The degree-6 cancellation, in the free word algebra**: the left-hand side is zero. -/
theorem evalTab_dynkin6Tab : evalTab dynkin6Tab = 0 := by
  rw [evalTab_eq_reprTab, ← MonoidAlgebra.ofCoeff_zero, MonoidAlgebra.ofCoeff_inj]
  exact reprTab_dynkin6Tab_eq_zero

/-- **The degree-6 pure identity**: the degree-6 part of `½W6 + ⅓y3₆ - ¼y4₆ + ⅕y5₆ - ⅙z⁶`, written
in `z = a + b` and the degree-2/3/4/5 parts `T₂`…`T₅` of `y = exp a * exp b - 1`, minus
`bchSexticTerm a b`, is zero.

This is the degree-6 cancellation behind `pieceB_septic_decomp`, and the companion of
`SmallSDischarge.sextic_pure_identity` (degree 5). It is proved here rather than in
`SmallSDischarge.lean` because its proof evaluates each piece through the `T` tables above, and that
file is one of this one's imports. -/
theorem septic_pure_identity {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b - (4 : ℚ)⁻¹ • bchY46 a b +
      (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 - bchSexticTerm a b = 0 := by
  rw [← wordAlgebraLift_dynkin6Tab, evalTab_dynkin6Tab, map_zero]

end

end FQFP.BCH.SexticTable
