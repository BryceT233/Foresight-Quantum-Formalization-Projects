/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms
public import FQFP.BCH.WordExpansion

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

## Status

The degree-4 and degree-5 pairs are ported and proved. The degree-6 pair is proved in
`SexticTable.lean`, which is where the `T` tables and the coefficient comparison live; the identity
cannot be stated here because its proof needs those tables, and `SexticTable.lean` already imports
this file for the `bchZ` / `bchT k` pieces below. The `bchZ`, `bchT k`, `bchW6`, `bchY36`, `bchY46`
and `bchY56` pieces it uses stay here.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

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

/-- **The degree-5 pure identity**: the degree-5 part of `½W5 + ⅓y3₅ - ¼y4₅ + ⅕z⁵`, written in
`z = a + b` and the degree-2/3/4 parts `T₂`, `T₃`, `T₄` of `y = exp a * exp b - 1`, minus
`bchQuinticTerm a b`, is zero.

Unlike the source's, the target's `bchQuinticGroup*` are `Finset.sum`s over word data, so the group
sums have to be expanded into monomials between `unfold` and `noncomm_ring`: without that step the
scalar equalities are stated against the *unexpanded* sums and leave false residual goals such as
`-1 / 720 = 0`. With it, no heartbeat bump is needed. -/
theorem sextic_pure_identity [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b - (4 : ℚ)⁻¹ • bchY45 a b +
      (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b = 0 := by
  simp only [bchW5, bchZ, bchT4, bchT2, bchT3, bchY35, smul_add, bchY45, bchQuinticTerm,
    bchQuinticGroup1, wordEval, Nat.succ_eq_add_one, Nat.reduceAdd, bchQuinticGroup1Words,
    Fin.isValue, List.ofFn_succ, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Fin.sum_univ_succ, Matrix.cons_val_one, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_const, Finset.card_singleton, one_smul, neg_add_rev,
    bchQuinticGroup4, bchQuinticGroup4Words, bchQuinticGroup6, bchQuinticGroup6Words,
    bchQuinticGroup24, bchQuinticGroup24Words]
  noncomm_ring; module

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

/-! **The degree-6 pure identity** is stated and proved in `SexticTable.lean` as
`septic_pure_identity`: the degree-6 part of `½W6 + ⅓y3₆ - ¼y4₆ + ⅕y5₆ - ⅙z⁶`, written in
`z = a + b` and the degree-2/3/4/5 parts `T₂`…`T₅` of `y = exp a * exp b - 1`, minus
`bchSexticTerm a b`, is zero.

It lives there rather than here because its proof evaluates each piece through the `T` tables of
`SexticTable.lean`, and that file imports this one for the pieces above. -/

end FQFP.BCH
