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

/-- `bchSexticTerm` as a table, over `bchSexticTermWords` and `bchSexticTermCoeffs`. -/
def sexticTab : Tab :=
  List.ofFn fun i : Fin 28 => (List.ofFn (bchSexticTermWords i), bchSexticTermCoeffs i)

/-- **The degree-6 Dynkin side as a table**: the left-hand side of `septic_pure_identity`. -/
def dynkin6Tab : Tab :=
  smulTab ((2 : ℚ)⁻¹) w6Tab ++ smulTab ((3 : ℚ)⁻¹) y36Tab ++
    smulTab (-(4 : ℚ)⁻¹) y46Tab ++ smulTab ((5 : ℚ)⁻¹) y56Tab ++
    smulTab (-(6 : ℚ)⁻¹) z6Tab ++ smulTab (-1) sexticTab

end

end FQFP.BCH.SexticTable
