/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms
public import FQFP.BCH.WordExpansion
public import FQFP.BCH.WordAlgebra

/-!
# The small-`s` discharge: pure cancellation identities

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:37-786`). This file grows
slice by slice; see `artifacts/bch-port.md` §3.3bis for the plan (`P0`…`P4`).

## What these identities are

Write `z = a + b` and let `T_k` be the degree-`k` part of `y = exp a * exp b - 1`. The Dynkin/Ree
form of `log (exp a * exp b)` expresses its degree-`k` part through the `y_j`, and the pure
identities here say that this expression agrees with the explicit word formula of `BCHTerms.lean`:
for degrees 4, 5, 6, 7, 8 respectively

    ½·W + ⅓·y³ - ¼·y⁴ + … - bch*Term a b = 0.

They are the degree-`k` cancellation step behind `pieceB_{sextic,septic,octic,nonic}_decomp`, which
is why they are stated with rational coefficients only: the target's scalar interface is `ℚ`
(`bch*Term` is a `ℚ`-algebra element, not a `𝕂`-one).

## How they are proved

Each identity is settled by **computation**. The graded pieces are collected into a *table* of
`(word, integer coefficient)` rows — the paper's rational coefficients cleared by `K ^ k` — and
comparing the two sides becomes a `List` and `ℤ` computation that a single `decide` performs.
`WordAlgebra.lean` supplies the table algebra and `bchTTable` below supplies the one table all the
identities share. `artifacts/abstractions/wordalgebra-int.md` records why this replaced the
`noncomm_ring` route.

## Status

The degree-4, -5 and -6 pairs are ported and proved, all three in this file. The degree-6 proof used
to live in `SexticTable.lean`: it could not be stated here because it needs the `bchTTable` of `y`
below, and that file had to import this one for the `bchZ` / `bchT k` pieces. Merging them removed
that circularity. The degree-7 and -8 pairs are not ported yet; they follow the same template.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

open WordAlgebra

variable {𝔸 : Type*}

/-! ### The shared degree-`k` toolbox

Every identity below writes the degree-`k` part of `y = exp a * exp b - 1` as a combination of the
graded pieces `T₂, …, T_k`, and each `T_n` is the same object at every degree. Declaring them once,
here, means the degree-5 and degree-6 statements share one definition instead of repeating six
`let`-bound expansions apiece.

These are `def`s rather than a `let` chain inside each statement on purpose: elaborating a
statement whose type is a `let` nested six to nine deep costs superlinearly in `isDefEq`/`whnf`, and
that cost is paid before a single tactic runs. Naming the pieces makes the type cheap. -/

/-- The degree-1 part of `y = exp a * exp b - 1`, i.e. `z = a + b`.

Only addition is used, so this is stated for a bare `Add` — the natural level for a sum. -/
def bchZ {𝔸 : Type*} [Add 𝔸] (a b : 𝔸) : 𝔸 := a + b

/-- The degree-2 part `T₂` of `y = exp a * exp b - 1`. -/
def bchT2 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2

/-- The degree-3 part `T₃` of `y = exp a * exp b - 1`. -/
def bchT3 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (6 : ℚ)⁻¹ • a ^ 3 + (2 : ℚ)⁻¹ • (a ^ 2 * b) + (2 : ℚ)⁻¹ • (a * b ^ 2) +
    (6 : ℚ)⁻¹ • b ^ 3

/-- The degree-4 part `T₄` of `y = exp a * exp b - 1`. -/
def bchT4 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (24 : ℚ)⁻¹ • a ^ 4 + (6 : ℚ)⁻¹ • (a ^ 3 * b) + (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) +
    (6 : ℚ)⁻¹ • (a * b ^ 3) + (24 : ℚ)⁻¹ • b ^ 4

/-- The degree-5 part `T₅` of `y = exp a * exp b - 1`. -/
def bchT5 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (120 : ℚ)⁻¹ • a ^ 5 + (24 : ℚ)⁻¹ • (a ^ 4 * b) + (12 : ℚ)⁻¹ • (a ^ 3 * b ^ 2) +
    (12 : ℚ)⁻¹ • (a ^ 2 * b ^ 3) + (24 : ℚ)⁻¹ • (a * b ^ 4) + (120 : ℚ)⁻¹ • b ^ 5

/-! ### The table of `y`

Every identity below is settled by computation: the graded pieces are collected into a *table* of
`(word, integer coefficient)` rows, and the coefficient comparison becomes a `List` and `ℤ`
computation that `decide` performs.

A table stores the paper's rational coefficients cleared by `K ^ k` (`K = 210`), so only integer
scalars are available in it; the rational coefficients `1/2, 1/3, …` of the Dynkin/Ree form are
cleared first, by multiplying the identity through by `lcm(1, …, d)`. The bridge lemmas below say
what each table evaluates to, and they are the only place the `K`-factors are discharged. -/

/-- **The degree-`k` part of `y = exp a * exp b - 1`**, as a table: the words `aⁿb^(k−n)` with
coefficient `K ^ k / (n! (k−n)!)`, i.e. the paper's `1/(n!(k−n)!)` cleared by `K ^ k`. -/
def bchTTable : (k : ℕ) → KTab
  | 0 => []
  | 1 => [([0], 210), ([1], 210)]
  | 2 => [([0, 0], 22050), ([0, 1], 44100), ([1, 1], 22050)]
  | 3 => [([0, 0, 0], 1543500), ([0, 0, 1], 4630500), ([0, 1, 1], 4630500),
          ([1, 1, 1], 1543500)]
  | 4 => [([0, 0, 0, 0], 81033750), ([0, 0, 0, 1], 324135000), ([0, 0, 1, 1], 486202500),
          ([0, 1, 1, 1], 324135000), ([1, 1, 1, 1], 81033750)]
  | 5 => [([0, 0, 0, 0, 0], 3403417500), ([0, 0, 0, 0, 1], 17017087500),
          ([0, 0, 0, 1, 1], 34034175000), ([0, 0, 1, 1, 1], 34034175000),
          ([0, 1, 1, 1, 1], 17017087500), ([1, 1, 1, 1, 1], 3403417500)]
  | 6 => [([0, 0, 0, 0, 0, 0], 119119612500), ([0, 0, 0, 0, 0, 1], 714717675000),
          ([0, 0, 0, 0, 1, 1], 1786794187500), ([0, 0, 0, 1, 1, 1], 2382392250000),
          ([0, 0, 1, 1, 1, 1], 1786794187500), ([0, 1, 1, 1, 1, 1], 714717675000),
          ([1, 1, 1, 1, 1, 1], 119119612500)]
  | _ => []

/-- **The degree-1 table evaluates to `z = a + b`.** -/
lemma evalKTab_bchTTable_one {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 1) = bchZ a b := by
  rw [bchTTable, bchZ]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one]
  norm_num

/-- **The degree-2 table evaluates to `T₂`.** -/
lemma evalKTab_bchTTable_two {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 2) = bchT2 a b := by
  rw [bchTTable, bchT2]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-- **The degree-3 table evaluates to `T₃`.** -/
lemma evalKTab_bchTTable_three {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 3) = bchT3 a b := by
  rw [bchTTable, bchT3]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-- **The degree-4 table evaluates to `T₄`.** -/
lemma evalKTab_bchTTable_four {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 4) = bchT4 a b := by
  rw [bchTTable, bchT4]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-- **The degree-5 table evaluates to `T₅`.** -/
lemma evalKTab_bchTTable_five {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 5) = bchT5 a b := by
  rw [bchTTable, bchT5]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-- **The degree-6 table evaluates to the degree-6 part of `y`.** There is no ring-level `bchT6` —
`bchW6` spells the `y₆` sum out where it first needs it — so this is that sum. -/
lemma evalKTab_bchTTable_six {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 6)
      = (720 : ℚ)⁻¹ • a ^ 6 + (120 : ℚ)⁻¹ • (a ^ 5 * b) + (48 : ℚ)⁻¹ • (a ^ 4 * b ^ 2) +
        (36 : ℚ)⁻¹ • (a ^ 3 * b ^ 3) + (48 : ℚ)⁻¹ • (a ^ 2 * b ^ 4) +
        (120 : ℚ)⁻¹ • (a * b ^ 5) + (720 : ℚ)⁻¹ • b ^ 6 := by
  rw [bchTTable]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-! ### Degree 4: the cancellation behind `bchQuarticTerm` -/

/-- **The degree-4 pure identity, with the denominators cleared**: 24 times

    Y₄ - ½(Y₁Y₃ + Y₂² + Y₃Y₁) + ⅓(Y₁²Y₂ + Y₁Y₂Y₁ + Y₂Y₁²) - ¼Y₁⁴ + C₄

is zero, where `z = a + b` and `U = 2ab + a² + b² = 2Y₂`. Stated over a bare `Ring` (the scalar is
`Nat`-valued, so no `ℚ` is needed) and proved by `noncomm_ring`. -/
theorem quintic_pure_identity_cleared [Ring 𝔸] (a b : 𝔸) :
    (a ^ 4 + 4 • (a ^ 3 * b) + 6 • (a ^ 2 * b ^ 2) + 4 • (a * b ^ 3) + b ^ 4) -
    2 • ((a + b) * (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) +
         (a ^ 3 + 3 • (a ^ 2 * b) + 3 • (a * b ^ 2) + b ^ 3) * (a + b)) -
    3 • ((2 • (a * b) + a ^ 2 + b ^ 2) * (2 • (a * b) + a ^ 2 + b ^ 2)) +
    4 • ((a + b) ^ 2 * (2 • (a * b) + a ^ 2 + b ^ 2) +
         (a + b) * (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) +
         (2 • (a * b) + a ^ 2 + b ^ 2) * (a + b) ^ 2) -
    6 • (a + b) ^ 4 +
    (b * (a * (a * b - b * a) - (a * b - b * a) * a) -
     (a * (a * b - b * a) - (a * b - b * a) * a) * b) = 0 := by
  noncomm_ring

/-- **The degree-4 pure identity**, with the `ℚ` scalars of the Dynkin/Ree form: the degree-4 part
of `½y² - ⅓y³ + ¼y⁴` written out in `z` and `T₂`, `T₃`, `T₄`, minus `bchQuarticTerm a b`, is zero.

This is the `ℚ`-scaled companion of `quintic_pure_identity_cleared` (multiply by `24`); the source
needs no heartbeat bump for it, and neither does this port. -/
theorem quintic_pure_identity [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (24 : ℚ)⁻¹ • a ^ 4 + (24 : ℚ)⁻¹ • b ^ 4 +
    (6 : ℚ)⁻¹ • (a * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b) +
    (4 : ℚ)⁻¹ • (a ^ 2 * b ^ 2) -
    (2 : ℚ)⁻¹ • ((a + b) * ((6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (2 : ℚ)⁻¹ • (a ^ 2 * b)) +
      ((6 : ℚ)⁻¹ • a ^ 3 + (6 : ℚ)⁻¹ • b ^ 3 +
        (2 : ℚ)⁻¹ • (a * b ^ 2) + (2 : ℚ)⁻¹ • (a ^ 2 * b)) * (a + b)) -
    (2 : ℚ)⁻¹ • (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) ^ 2 +
    (3 : ℚ)⁻¹ • ((a + b) ^ 2 * (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) +
      (a + b) * (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) * (a + b) +
      (a * b + (2 : ℚ)⁻¹ • a ^ 2 + (2 : ℚ)⁻¹ • b ^ 2) * (a + b) ^ 2) -
    (4 : ℚ)⁻¹ • (a + b) ^ 4 - bchQuarticTerm a b = 0 := by
  unfold bchQuarticTerm
  simp only [pow_succ, pow_zero, one_mul, ← mul_assoc, mul_add, Algebra.mul_smul_comm, add_mul,
    smul_add, Algebra.smul_mul_assoc, smul_smul, mul_sub, sub_mul, smul_sub, neg_sub]
  module

/-! ### Degree 5: the cancellation behind `bchQuinticTerm` -/

/-- `W5 = 2·y_d5 - (y²)_d5`, the degree-5 start of the Dynkin/Ree form. -/
def bchW5 {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (60 : ℚ)⁻¹ • a ^ 5 + (60 : ℚ)⁻¹ • b ^ 5 + (12 : ℚ)⁻¹ • (a * b ^ 4) +
    (12 : ℚ)⁻¹ • (a ^ 4 * b) + (6 : ℚ)⁻¹ • (a ^ 2 * b ^ 3) + (6 : ℚ)⁻¹ • (a ^ 3 * b ^ 2) -
    (bchZ a b * bchT4 a b + bchT4 a b * bchZ a b) -
    (bchT2 a b * bchT3 a b + bchT3 a b * bchT2 a b)

/-- The degree-5 part `(y³)_d5` of `y³`: the six ways to split `5` into three positive parts. -/
def bchY35 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 2 * bchT3 a b + bchZ a b * bchT3 a b * bchZ a b + bchT3 a b * bchZ a b ^ 2 +
    bchZ a b * bchT2 a b ^ 2 + bchT2 a b * bchZ a b * bchT2 a b + bchT2 a b ^ 2 * bchZ a b

/-- The degree-5 part `(y⁴)_d5` of `y⁴`: the four ways to split `5` into four positive parts. -/
def bchY45 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 3 * bchT2 a b + bchZ a b ^ 2 * bchT2 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b ^ 2 + bchT2 a b * bchZ a b ^ 3

/-! #### The degree-5 tables

The five pieces as tables, so that `sextic_pure_identity` below is a computation. Four of them are
built here from `bchTTable`; the fifth, `bchQuinticTermTable`, is the term's own data and lives next
to `bchQuinticTerm` in `BCHTerms.lean`. -/

/-- The degree-5 `W5` table, mirroring `bchW5`. -/
def w5Tab : KTab :=
  smulKTab 2 (bchTTable 5) ++ smulKTab (-1) (mulKTab (bchTTable 1) (bchTTable 4)) ++
    smulKTab (-1) (mulKTab (bchTTable 2) (bchTTable 3)) ++
    smulKTab (-1) (mulKTab (bchTTable 3) (bchTTable 2)) ++
    smulKTab (-1) (mulKTab (bchTTable 4) (bchTTable 1))

/-- **`W5` as a table**: `evalKTab a b w5Tab = bchW5 a b`. -/
lemma evalKTab_w5Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b w5Tab = bchW5 a b := by
  simp only [w5Tab, bchW5, bchZ, evalKTab_append, evalKTab_smulKTab, evalKTab_mulKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, evalKTab_bchTTable_five, bchZ, bchT5]
  simp only [smul_add, smul_smul]
  norm_num
  abel

/-- The degree-5 `(y³)_d5` table, mirroring `bchY35`. -/
def y35Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 2) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (bchTTable 3) (powKTab (bchTTable 1) 2) ++
    mulKTab (bchTTable 1) (powKTab (bchTTable 2) 2) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (powKTab (bchTTable 2) 2) (bchTTable 1)

/-- **`(y³)_d5` as a table**: `evalKTab a b y35Tab = bchY35 a b`. -/
lemma evalKTab_y35Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y35Tab = bchY35 a b := by
  simp only [y35Tab, bchY35, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three, bchZ]

/-- The degree-5 `(y⁴)_d5` table, mirroring `bchY45`. -/
def y45Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 3) (bchTTable 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (powKTab (bchTTable 1) 2) ++
    mulKTab (bchTTable 2) (powKTab (bchTTable 1) 3)

/-- **`(y⁴)_d5` as a table**: `evalKTab a b y45Tab = bchY45 a b`. -/
lemma evalKTab_y45Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y45Tab = bchY45 a b := by
  simp only [y45Tab, bchY45, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, bchZ]

/-- The degree-5 `z⁵` table, mirroring `(bchZ a b) ^ 5`. -/
def z5Tab : KTab := powKTab (bchTTable 1) 5

/-- **The `z⁵` table's evaluation**: `z = a + b` raised to the fifth. -/
lemma evalKTab_z5Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b z5Tab = bchZ a b ^ 5 := by
  rw [z5Tab, evalKTab_powKTab, evalKTab_bchTTable_one]

/-- **The degree-5 Dynkin side as a table**: the left-hand side of `sextic_pure_identity`,
multiplied through by `lcm(1, …, 5) = 60` so that the multipliers are integers. -/
def dynkin5Tab : KTab :=
  smulKTab 30 w5Tab ++ smulKTab 20 y35Tab ++ smulKTab (-15) y45Tab ++
    smulKTab 12 z5Tab ++ smulKTab (-60) bchQuinticTermTable

/-- **The degree-5 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `60` times the
Dynkin/Ree expression of `sextic_pure_identity`. -/
theorem evalKTab_dynkin5Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin5Tab
      = (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b -
          (4 : ℚ)⁻¹ • bchY45 a b + (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b) := by
  rw [dynkin5Tab]
  simp only [evalKTab_append, evalKTab_smulKTab]
  rw [evalKTab_w5Tab, evalKTab_y35Tab, evalKTab_y45Tab, evalKTab_z5Tab,
    evalKTab_bchQuinticTermTable]
  rw [show (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b -
        (4 : ℚ)⁻¹ • bchY45 a b + (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b)
      = (30 : ℚ) • bchW5 a b + (20 : ℚ) • bchY35 a b - (15 : ℚ) • bchY45 a b +
        (12 : ℚ) • bchZ a b ^ 5 - (60 : ℚ) • bchQuinticTerm a b from by
    module]
  norm_num
  abel

set_option maxRecDepth 10000 in
/-- **The degree-5 coefficient comparison**: collapsing the left-hand side leaves no nonzero
coefficient. This single `decide` is the whole computation. -/
theorem collapseK_dynkin5Tab_all_zero :
    (collapseK dynkin5Tab).all (fun p => p.2 == 0) = true := by
  decide

/-- **The degree-5 cancellation, as a table identity**: the collapsed left-hand side evaluates to
zero in any `ℚ`-algebra. -/
theorem evalKTab_dynkin5Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin5Tab = 0 := by
  rw [← evalKTab_collapseK]
  exact evalKTab_eq_zero_of_all_beq a b _ collapseK_dynkin5Tab_all_zero

/-- **The degree-5 pure identity**: the degree-5 part of `½W5 + ⅓y3₅ - ¼y4₅ + ⅕z⁵`, written in
`z = a + b` and the degree-2/3/4 parts `T₂`, `T₃`, `T₄` of `y = exp a * exp b - 1`, minus
`bchQuinticTerm a b`, is zero.

This is the degree-5 cancellation behind `pieceB_sextic_decomp`, and the companion of
`septic_pure_identity` (degree 6) below. -/
theorem sextic_pure_identity {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b - (4 : ℚ)⁻¹ • bchY45 a b +
      (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b = 0 := by
  have h := evalKTab_dynkin5Tab (𝔸 := 𝔸) a b
  rw [evalKTab_dynkin5Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h60 | hX
  · exact absurd h60 (by norm_num)
  · exact hX

/-! ### Degree 6: the cancellation behind `bchSexticTerm` -/

/-- `W6 = 2·y_d6 - (y²)_d6`, the degree-6 start of the Dynkin/Ree form. -/
def bchW6 {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (360 : ℚ)⁻¹ • a ^ 6 + (60 : ℚ)⁻¹ • (a ^ 5 * b) + (24 : ℚ)⁻¹ • (a ^ 4 * b ^ 2) +
    (18 : ℚ)⁻¹ • (a ^ 3 * b ^ 3) + (24 : ℚ)⁻¹ • (a ^ 2 * b ^ 4) + (60 : ℚ)⁻¹ • (a * b ^ 5) +
    (360 : ℚ)⁻¹ • b ^ 6 -
    (bchZ a b * bchT5 a b + bchT2 a b * bchT4 a b + bchT3 a b * bchT3 a b +
      bchT4 a b * bchT2 a b + bchT5 a b * bchZ a b)

/-- The degree-6 part `(y³)_d6` of `y³`: the ten ways to split `6` into three positive parts. -/
def bchY36 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 2 * bchT4 a b + bchZ a b * bchT4 a b * bchZ a b + bchT4 a b * bchZ a b ^ 2 +
    bchZ a b * bchT2 a b * bchT3 a b + bchZ a b * bchT3 a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchT3 a b + bchT2 a b * bchT3 a b * bchZ a b +
    bchT3 a b * bchZ a b * bchT2 a b + bchT3 a b * bchT2 a b * bchZ a b + bchT2 a b ^ 3

/-- The degree-6 part `(y⁴)_d6` of `y⁴`: the ten ways to split `6` into four positive parts. -/
def bchY46 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 3 * bchT3 a b + bchZ a b ^ 2 * bchT3 a b * bchZ a b +
    bchZ a b * bchT3 a b * bchZ a b ^ 2 + bchT3 a b * bchZ a b ^ 3 +
    bchZ a b ^ 2 * bchT2 a b ^ 2 + bchZ a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT2 a b ^ 2 * bchZ a b + bchT2 a b * bchZ a b ^ 2 * bchT2 a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchZ a b + bchT2 a b ^ 2 * bchZ a b ^ 2

/-- The degree-6 part `(y⁵)_d6` of `y⁵`: the five ways to split `6` into five positive parts. -/
def bchY56 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 4 * bchT2 a b + bchZ a b ^ 3 * bchT2 a b * bchZ a b +
    bchZ a b ^ 2 * bchT2 a b * bchZ a b ^ 2 + bchZ a b * bchT2 a b * bchZ a b ^ 3 +
    bchT2 a b * bchZ a b ^ 4

/-! ### Degree 6: the cancellation behind `bchSexticTerm`

`septic_pure_identity` is the degree-6 cancellation

    ½·W6 + ⅓·(y³)_d6 - ¼·(y⁴)_d6 + ⅕·(y⁵)_d6 - ⅙·z⁶ - bchSexticTerm = 0.

Each of its six pieces is a table here, built from `bchTTable` by the operations of
`WordAlgebra`, so that the identity becomes a statement about tables:

* `w6Tab` — `W6 = 2·y_d6 - (y²)_d6`;
* `y36Tab`, `y46Tab`, `y56Tab` — the degree-6 parts of `y³`, `y⁴`, `y⁵`;
* `z6Tab` — `z⁶`;
* `sexticTab` — `bchSexticTerm` itself;
* `dynkin6Tab` — the whole left-hand side.

Every piece is written in the same order and with the same shape as its ring-level counterpart
above, so its bridge is a `simp only` that pushes `evalKTab` through the table operations,
discharges the `K ^ 6` factors with `norm_num`, and reorders with `abel`. -/

/-- The degree-6 `W6` table, mirroring `bchW6`. -/
def w6Tab : KTab :=
  smulKTab 2 (bchTTable 6) ++ smulKTab (-1) (mulKTab (bchTTable 1) (bchTTable 5)) ++
    smulKTab (-1) (mulKTab (bchTTable 2) (bchTTable 4)) ++
    smulKTab (-1) (mulKTab (bchTTable 3) (bchTTable 3)) ++
    smulKTab (-1) (mulKTab (bchTTable 4) (bchTTable 2)) ++
    smulKTab (-1) (mulKTab (bchTTable 5) (bchTTable 1))

/-- **`W6` as a table**: `evalKTab a b w6Tab = bchW6 a b`. -/
lemma evalKTab_w6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b w6Tab = bchW6 a b := by
  simp only [w6Tab, bchW6, bchZ, evalKTab_append, evalKTab_smulKTab, evalKTab_mulKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, evalKTab_bchTTable_five, evalKTab_bchTTable_six, bchZ]
  simp only [smul_add, smul_smul]
  norm_num
  abel

/-- The degree-6 `(y³)_d6` table, mirroring `bchY36`. -/
def y36Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 2) (bchTTable 4) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 4)) (bchTTable 1) ++
    mulKTab (bchTTable 4) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 2)) (bchTTable 1) ++
    powKTab (bchTTable 2) 3

/-- **`(y³)_d6` as a table**: `evalKTab a b y36Tab = bchY36 a b`. -/
lemma evalKTab_y36Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y36Tab = bchY36 a b := by
  simp only [y36Tab, bchY36, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, bchZ]

/-- The degree-6 `(y⁴)_d6` table, mirroring `bchY46`. -/
def y46Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 3) (bchTTable 3) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (powKTab (bchTTable 1) 2) ++
    mulKTab (bchTTable 3) (powKTab (bchTTable 1) 3) ++
    mulKTab (powKTab (bchTTable 1) 2) (powKTab (bchTTable 2) 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 1) (powKTab (bchTTable 2) 2)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 2) (powKTab (bchTTable 1) 2)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (powKTab (bchTTable 2) 2) (powKTab (bchTTable 1) 2)

/-- **`(y⁴)_d6` as a table**: `evalKTab a b y46Tab = bchY46 a b`. -/
lemma evalKTab_y46Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y46Tab = bchY46 a b := by
  simp only [y46Tab, bchY46, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three, bchZ]

/-- The degree-6 `(y⁵)_d6` table, mirroring `bchY56`. -/
def y56Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 4) (bchTTable 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 3) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (powKTab (bchTTable 1) 3) ++
    mulKTab (bchTTable 2) (powKTab (bchTTable 1) 4)

/-- **`(y⁵)_d6` as a table**: `evalKTab a b y56Tab = bchY56 a b`. -/
lemma evalKTab_y56Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y56Tab = bchY56 a b := by
  simp only [y56Tab, bchY56, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, bchZ]

/-- The degree-6 `z⁶` table, mirroring `(bchZ a b) ^ 6`. -/
def z6Tab : KTab := powKTab (bchTTable 1) 6

/-- **The `z⁶` table's evaluation**: `z = a + b` raised to the sixth. -/
lemma evalKTab_z6Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b z6Tab = bchZ a b ^ 6 := by
  rw [z6Tab, evalKTab_powKTab, evalKTab_bchTTable_one]

/-- **`bchSexticTerm`'s table**: `bchSexticTerm` is *defined* by evaluating
`bchSexticTermTable`, so this is the table itself, not a copy of it. -/
def sexticTab : KTab := bchSexticTermTable

/-- **The evaluation of the sextic table is `bchSexticTerm` itself**: with `sexticTab` being
`bchSexticTermTable` this is `rfl`-level, which is the point of defining the term from its table. -/
theorem evalKTab_sexticTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b sexticTab = bchSexticTerm a b :=
  rfl

/-- **The degree-6 Dynkin side as a table**: the left-hand side of `septic_pure_identity`,
multiplied through by `lcm(1, …, 6) = 60` so that the multipliers are integers.

Unlike the table of the rational version of this proof, this one is deliberately *not*
`irreducible`: it is unfolded exactly once, by the `decide` below, and nothing else compares goals
whose type mentions it. -/
def dynkin6Tab : KTab :=
  smulKTab 30 w6Tab ++ smulKTab 20 y36Tab ++ smulKTab (-15) y46Tab ++
    smulKTab 12 y56Tab ++ smulKTab (-10) z6Tab ++ smulKTab (-60) sexticTab

/-- **The degree-6 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `60` times the
Dynkin/Ree expression of `septic_pure_identity`. The factor `60` is what clears the rational
scalars `½ … ⅙` before the `K`-scaling. -/
theorem evalKTab_dynkin6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin6Tab
      = (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b -
          (4 : ℚ)⁻¹ • bchY46 a b + (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 -
          bchSexticTerm a b) := by
  rw [dynkin6Tab]
  simp only [evalKTab_append, evalKTab_smulKTab]
  rw [evalKTab_w6Tab, evalKTab_y36Tab, evalKTab_y46Tab, evalKTab_y56Tab, evalKTab_z6Tab,
    evalKTab_sexticTab]
  rw [show (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b -
        (4 : ℚ)⁻¹ • bchY46 a b + (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 -
        bchSexticTerm a b)
      = (30 : ℚ) • bchW6 a b + (20 : ℚ) • bchY36 a b - (15 : ℚ) • bchY46 a b +
        (12 : ℚ) • bchY56 a b - (10 : ℚ) • bchZ a b ^ 6 - (60 : ℚ) • bchSexticTerm a b from by
    module]
  norm_num
  abel

set_option maxRecDepth 10000 in
/-- **The degree-6 coefficient comparison**: collapsing the left-hand side leaves no nonzero
coefficient. This single `decide` is the whole computation.

The unfolding genuinely has ~1000 nested `List.cons` cells, which is what the `maxRecDepth` is for:
a *tactic recursion depth* limit on walking that term, not a search budget. No heartbeat budget is
raised. -/
theorem collapseK_dynkin6Tab_all_zero :
    (collapseK dynkin6Tab).all (fun p => p.2 == 0) = true := by
  decide

/-- **The degree-6 cancellation, as a table identity**: the collapsed left-hand side evaluates to
zero in any `ℚ`-algebra. -/
theorem evalKTab_dynkin6Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin6Tab = 0 := by
  rw [← evalKTab_collapseK]
  exact evalKTab_eq_zero_of_all_beq a b _ collapseK_dynkin6Tab_all_zero

/-- **The degree-6 pure identity**: the degree-6 part of `½W6 + ⅓y3₆ - ¼y4₆ + ⅕y5₆ - ⅙z⁶`, written
in `z = a + b` and the degree-2/3/4/5 parts `T₂`…`T₅` of `y = exp a * exp b - 1`, minus
`bchSexticTerm a b`, is zero.

This is the degree-6 cancellation behind `pieceB_septic_decomp`, and the companion of
`sextic_pure_identity` (degree 5) above. -/
theorem septic_pure_identity {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b - (4 : ℚ)⁻¹ • bchY46 a b +
      (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 - bchSexticTerm a b = 0 := by
  have h := evalKTab_dynkin6Tab (𝔸 := 𝔸) a b
  rw [evalKTab_dynkin6Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h60 | hX
  · exact absurd h60 (by norm_num)
  · exact hX

end FQFP.BCH
