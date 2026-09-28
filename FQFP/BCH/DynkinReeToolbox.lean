/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.BCHTerms

/-!
# The Dynkin/Ree toolbox: the graded pieces of `y = exp a * exp b - 1`

Write `z = a + b` and let `T_k` be the degree-`k` part of `y = exp a * exp b - 1`. The Dynkin/Ree
form of `log (exp a * exp b)` expresses the degree-`k` part of `log (1 + y)` through the `y_j`, and
the *pure identity* of degree `k` says that this expression agrees with the explicit word formula of
`BCHTerms.lean`:

    ½·W_k + ⅓·(y³)_k - ¼·(y⁴)_k + … ± (1/k)·z^k - bch⟨k⟩Term = 0.

This file is the toolbox every degree shares: the `z` and `T₂, …, T₇` of the ring level, their table
form `bchTTable`, and the bridge saying the table evaluates to the ring expression. The identities
themselves live one degree to a file (`DynkinReeQuintic.lean` … `DynkinReeSeptic.lean`), because
each is a self-contained computation whose only shared input is what is below.

Degree 8 shares the same shape but is deferred, so `T₈` is not here: it would be used by nothing
else. See `artifacts/abstractions/deg8-split.md`.

## Why the pieces are `def`s and not `let`s

A statement whose type is a `let` chain nested six to nine deep costs superlinearly in
`isDefEq`/`whnf`, and that cost is paid before a single tactic runs. Naming the pieces makes the
type cheap, and it also puts each piece in exactly one home: `T₂` is defined once, here, and every
degree uses that definition.

## Why the numeric coefficients live in a table

The Dynkin/Ree expression has rational coefficients `1/2, 1/3, …`, and `ℚ` has no kernel reduction,
so a coefficient comparison over `ℚ` can only be driven by `norm_num`, one small expression at a
time. `WordAlgebra.lean` replaces the coefficients by integers: a degree-`d` table stores `K ^ d`
times its rational coefficients, with `K = 210`, and integer arithmetic *is* kernel-reducible.
`bchTTable` is the degree-`k` part of `y` in that form, and `evalKTab_bchTTable_*` below say what it
evaluates to.

## Provenance

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:37-786`): the source
states each identity inline as a `let` chain over an arbitrary `RCLike 𝕂`. The statements here are
the same identities with the pieces named and the scalar interface narrowed to `ℚ`. The range covers
degrees 4–8; degree 8 is deferred (`artifacts/abstractions/deg8-split.md`), so `T₈` is absent and
the degrees built on this file are 4–7.
`quintic_pure_identity` is the degree-4 cancellation, and it is the one identity of the family that
is *not* proved through a table: it is stated over a bare `Ring` (its scalars are `Nat`-valued),
while `evalKTab` needs `[Algebra ℚ 𝔸]`. Its companion `quintic_pure_identity_cleared` is the same
identity multiplied through by `24`.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

open WordAlgebra

variable {𝔸 : Type*}

/-! ### The graded pieces of `y = exp a * exp b - 1`

Each `T_n` is the same object at every degree, so declaring them once — here — means the degree-5
through degree-8 identities share one definition instead of repeating six `let`-bound expansions
apiece. -/

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

/-- The degree-6 part `T₆` of `y = exp a * exp b - 1`. -/
def bchT6 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (720 : ℚ)⁻¹ • (a ^ 6) + (120 : ℚ)⁻¹ • (a ^ 5 * b) + (48 : ℚ)⁻¹ • (a ^ 4 * b ^ 2) +
    (36 : ℚ)⁻¹ • (a ^ 3 * b ^ 3) + (48 : ℚ)⁻¹ • (a ^ 2 * b ^ 4) + (120 : ℚ)⁻¹ • (a * b ^ 5) +
    (720 : ℚ)⁻¹ • (b ^ 6)

/-- The degree-7 part `T₇` of `y = exp a * exp b - 1`. -/
def bchT7 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  (5040 : ℚ)⁻¹ • (a ^ 7) + (720 : ℚ)⁻¹ • (a ^ 6 * b) + (240 : ℚ)⁻¹ • (a ^ 5 * b ^ 2) +
    (144 : ℚ)⁻¹ • (a ^ 4 * b ^ 3) + (144 : ℚ)⁻¹ • (a ^ 3 * b ^ 4) + (240 : ℚ)⁻¹ • (a ^ 2 * b ^ 5) +
    (720 : ℚ)⁻¹ • (a * b ^ 6) + (5040 : ℚ)⁻¹ • (b ^ 7)

/-! ### The table of `y`

A table stores the paper's rational coefficients cleared by `K ^ k` (`K = 210`), so only integer
scalars are available in it; the rational coefficients `1/2, 1/3, …` of the Dynkin/Ree form are
cleared first, by multiplying the identity through by `lcm(1, …, d)`. The bridge lemmas below say
what the table evaluates to, and they are the only place the `K`-factors are discharged. -/

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
  | 7 => [([0, 0, 0, 0, 0, 0, 0], 3573588375000), ([0, 0, 0, 0, 0, 0, 1], 25015118625000),
          ([0, 0, 0, 0, 0, 1, 1], 75045355875000), ([0, 0, 0, 0, 1, 1, 1], 125075593125000),
          ([0, 0, 0, 1, 1, 1, 1], 125075593125000), ([0, 0, 1, 1, 1, 1, 1], 75045355875000),
          ([0, 1, 1, 1, 1, 1, 1], 25015118625000), ([1, 1, 1, 1, 1, 1, 1], 3573588375000)]
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

/-- **The degree-6 table evaluates to `T₆`.** -/
lemma evalKTab_bchTTable_six {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 6) = bchT6 a b := by
  rw [bchTTable, bchT6]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-- **The degree-7 table evaluates to `T₇`.** -/
lemma evalKTab_bchTTable_seven {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b (bchTTable 7) = bchT7 a b := by
  rw [bchTTable, bchT7]
  simp only [evalKTab, K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.prod_cons, List.prod_nil, mul_one, pow_succ, mul_assoc]
  norm_num
  abel

/-! ### Degree 4: the cancellation behind `bchQuarticTerm`

The degree-4 identity is the one member of the family that is **not** proved through a table. It is
stated over a bare `Ring` — its scalar multipliers are `Nat`-valued after multiplication by `24`, so
no `ℚ` is needed — while `evalKTab` requires `[Algebra ℚ 𝔸]`. It therefore lives here, next to the
pieces it is stated in terms of, and is settled by `noncomm_ring`. -/

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

This is the `ℚ`-scaled companion of `quintic_pure_identity_cleared` (multiply by `24`). -/
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

end FQFP.BCH
