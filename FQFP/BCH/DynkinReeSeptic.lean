/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.DynkinReeSextic

/-!
# Degree 7: the cancellation behind `bchSepticTerm`

The pure identity of this file is `octic_pure_identity` — the name is the source's, and it is one
ahead of the degree it settles; see `DynkinReeToolbox.lean` for the family and the naming. It says
that the degree-7 part of the Dynkin/Ree form vanishes:

    ½·W7 + ⅓·(y³)_d7 - ¼·(y⁴)_d7 + ⅕·(y⁵)_d7 - ⅙·(y⁶)_d7 + (1/7)·z⁷ - bchSepticTerm = 0,

where `z = a + b`, `T_k` is the degree-`k` part of `y = exp a * exp b - 1`,
`W7 = 2·y_d7 - (y²)_d7`, and each `(y^m)_d7` is the sum over the positive compositions of `7` into
`m` parts, in lexicographic order — written in that same order at the ring level and as a table.

## How the coefficient comparison is split

One `decide` over the whole left-hand side does *not* fit the default budget at this degree: the
table has 3390 raw rows against the 128 words, and a single goal over that exceeds it (measured; see
`artifacts/abstractions/wordalgebra-is-int.md`). Degrees 4–6 therefore each collapse their whole
left-hand side in one goal, and this file cannot.

The comparison is instead run **piece by piece**, with `collapseK_append` from `WordAlgebra.lean`
as the single step: collapse the first piece, merge the next one into that accumulator, and so on.
Every intermediate table then stays at **one row per word** (128 rows here), so the largest goal
sees a piece and an accumulator rather than the whole chain — which is what keeps the computation
inside the default heartbeat budget without a literal normal form for any piece.

The last step is one `decide` on the accumulated 128-row table: `evalKTab_dynkin7Tab_eq_zero` turns
"the accumulation leaves no nonzero coefficient" into "the evaluation is zero in any `ℚ`-algebra",
and `octic_pure_identity` divides out `420 = lcm(1, …, 7)`.

Writing the pieces as literal normal forms — the shape this file used before — needs a 256-row
literal `def` at degree 8, which exceeds the budget on its own. The split above needs none, and is
therefore also the shape the degree-8 identity is built on.

## Provenance

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:229-436`). The source
states the identity as an inline expansion over an arbitrary `RCLike 𝕂` with
`set_option maxHeartbeats 64000000`; the statement here is the same identity with the pieces named,
and no heartbeat budget is raised.

**Assisted by Deepseek Harness**
-/

@[expose] public section

namespace FQFP.BCH

open WordAlgebra

variable {𝔸 : Type*}

/-- `W7 = 2·y_d7 - (y²)_d7`, the degree-7 start of the Dynkin/Ree form. -/
def bchW7 {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  2 • bchT7 a b -
    (bchZ a b * bchT6 a b + bchT2 a b * bchT5 a b + bchT3 a b * bchT4 a b + bchT4 a b * bchT3 a b +
        bchT5 a b * bchT2 a b + bchT6 a b * bchZ a b)

/-- The degree-7 part `(y^3)_d7` of `y^3`: the 15 ways to split `7` into 3 positive parts. -/
def bchY37 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 2 * bchT5 a b + bchZ a b * bchT2 a b * bchT4 a b + bchZ a b * bchT3 a b * bchT3 a b +
    bchZ a b * bchT4 a b * bchT2 a b + bchZ a b * bchT5 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT4 a b + bchT2 a b * bchT2 a b * bchT3 a b +
    bchT2 a b * bchT3 a b * bchT2 a b + bchT2 a b * bchT4 a b * bchZ a b +
    bchT3 a b * bchZ a b * bchT3 a b + bchT3 a b * bchT2 a b * bchT2 a b +
    bchT3 a b * bchT3 a b * bchZ a b + bchT4 a b * bchZ a b * bchT2 a b +
    bchT4 a b * bchT2 a b * bchZ a b + bchT5 a b * bchZ a b ^ 2

/-- The degree-7 part `(y^4)_d7` of `y^4`: the 20 ways to split `7` into 4 positive parts. -/
def bchY47 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 3 * bchT4 a b + bchZ a b ^ 2 * bchT2 a b * bchT3 a b +
    bchZ a b ^ 2 * bchT3 a b * bchT2 a b + bchZ a b ^ 2 * bchT4 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT3 a b + bchZ a b * bchT2 a b * bchT2 a b * bchT2 a b +
    bchZ a b * bchT2 a b * bchT3 a b * bchZ a b + bchZ a b * bchT3 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT3 a b * bchT2 a b * bchZ a b + bchZ a b * bchT4 a b * bchZ a b ^ 2 +
    bchT2 a b * bchZ a b ^ 2 * bchT3 a b + bchT2 a b * bchZ a b * bchT2 a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchT3 a b * bchZ a b + bchT2 a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchT2 a b * bchT2 a b * bchT2 a b * bchZ a b + bchT2 a b * bchT3 a b * bchZ a b ^ 2 +
    bchT3 a b * bchZ a b ^ 2 * bchT2 a b + bchT3 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchT3 a b * bchT2 a b * bchZ a b ^ 2 + bchT4 a b * bchZ a b ^ 3

/-- The degree-7 part `(y^5)_d7` of `y^5`: the 15 ways to split `7` into 5 positive parts. -/
def bchY57 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 4 * bchT3 a b + bchZ a b ^ 3 * bchT2 a b * bchT2 a b +
    bchZ a b ^ 3 * bchT3 a b * bchZ a b + bchZ a b ^ 2 * bchT2 a b * bchZ a b * bchT2 a b +
    bchZ a b ^ 2 * bchT2 a b * bchT2 a b * bchZ a b + bchZ a b ^ 2 * bchT3 a b * bchZ a b ^ 2 +
    bchZ a b * bchT2 a b * bchZ a b ^ 2 * bchT2 a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchT2 a b * bchZ a b ^ 2 + bchZ a b * bchT3 a b * bchZ a b ^ 3 +
    bchT2 a b * bchZ a b ^ 3 * bchT2 a b + bchT2 a b * bchZ a b ^ 2 * bchT2 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchZ a b ^ 2 + bchT2 a b * bchT2 a b * bchZ a b ^ 3 +
    bchT3 a b * bchZ a b ^ 4

/-- The degree-7 part `(y^6)_d7` of `y^6`: the 6 ways to split `7` into 6 positive parts. -/
def bchY67 {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  bchZ a b ^ 5 * bchT2 a b + bchZ a b ^ 4 * bchT2 a b * bchZ a b +
    bchZ a b ^ 3 * bchT2 a b * bchZ a b ^ 2 + bchZ a b ^ 2 * bchT2 a b * bchZ a b ^ 3 +
    bchZ a b * bchT2 a b * bchZ a b ^ 4 + bchT2 a b * bchZ a b ^ 5

/-! ### The degree-7 tables -/

/-- The degree-7 `W7` table, mirroring `bchW7`. -/
def w7Tab : KTab :=
  smulKTab 2 (bchTTable 7) ++
    (smulKTab (-1) (mulKTab (bchTTable 1) (bchTTable 6)) ++
      smulKTab (-1) (mulKTab (bchTTable 2) (bchTTable 5)) ++
      smulKTab (-1) (mulKTab (bchTTable 3) (bchTTable 4)) ++
      smulKTab (-1) (mulKTab (bchTTable 4) (bchTTable 3)) ++
      smulKTab (-1) (mulKTab (bchTTable 5) (bchTTable 2)) ++
      smulKTab (-1) (mulKTab (bchTTable 6) (bchTTable 1)))

/-- The degree-7 `(y^3)_d7` table, mirroring `bchY37`. -/
def y37Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 2) (bchTTable 5) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 4) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 4)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 5)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 4) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 2)) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 3)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 4)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 1)) (bchTTable 3) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 2)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 4) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (mulKTab (bchTTable 4) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (bchTTable 5) (powKTab (bchTTable 1) 2)

/-- The degree-7 `(y^4)_d7` table, mirroring `bchY47`. -/
def y47Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 3) (bchTTable 4) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (bchTTable 3) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 3)) (bchTTable 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 4)) (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 3) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 4)) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 2) (powKTab (bchTTable 1) 2)) (bchTTable 3) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 2)) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 3)) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 3) (powKTab (bchTTable 1) 2)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 3) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (bchTTable 3) (bchTTable 2)) (powKTab (bchTTable 1) 2) ++
    mulKTab (bchTTable 4) (powKTab (bchTTable 1) 3)

/-- The degree-7 `(y^5)_d7` table, mirroring `bchY57`. -/
def y57Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 4) (bchTTable 3) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 3) (bchTTable 2)) (bchTTable 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 3) (bchTTable 3)) (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (bchTTable 1))
      (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (bchTTable 2))
      (bchTTable 1) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 3)) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (powKTab (bchTTable 1) 2))
      (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2))
      (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (bchTTable 2))
      (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 3)) (powKTab (bchTTable 1) 3) ++
    mulKTab (mulKTab (bchTTable 2) (powKTab (bchTTable 1) 3)) (bchTTable 2) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (powKTab (bchTTable 1) 2)) (bchTTable 2))
      (bchTTable 1) ++
    mulKTab (mulKTab (mulKTab (bchTTable 2) (bchTTable 1)) (bchTTable 2))
      (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (bchTTable 2) (bchTTable 2)) (powKTab (bchTTable 1) 3) ++
    mulKTab (bchTTable 3) (powKTab (bchTTable 1) 4)

/-- The degree-7 `(y^6)_d7` table, mirroring `bchY67`. -/
def y67Tab : KTab :=
  mulKTab (powKTab (bchTTable 1) 5) (bchTTable 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 4) (bchTTable 2)) (bchTTable 1) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 3) (bchTTable 2)) (powKTab (bchTTable 1) 2) ++
    mulKTab (mulKTab (powKTab (bchTTable 1) 2) (bchTTable 2)) (powKTab (bchTTable 1) 3) ++
    mulKTab (mulKTab (bchTTable 1) (bchTTable 2)) (powKTab (bchTTable 1) 4) ++
    mulKTab (bchTTable 2) (powKTab (bchTTable 1) 5)

/-- The degree-7 `z⁷` table, mirroring `(bchZ a b) ^ 7`. -/
def z7Tab : KTab := powKTab (bchTTable 1) 7

/-- **`W7` as a table**: `evalKTab a b w7Tab = bchW7 a b`. -/
lemma evalKTab_w7Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b w7Tab = bchW7 a b := by
  simp only [w7Tab, bchW7, bchZ, evalKTab_append, evalKTab_smulKTab, evalKTab_mulKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, evalKTab_bchTTable_five, evalKTab_bchTTable_six,
    evalKTab_bchTTable_seven, bchZ]
  norm_cast; norm_num
  abel

/-- **`(y³)_d7` as a table**: `evalKTab a b y37Tab = bchY37 a b`. -/
lemma evalKTab_y37Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y37Tab = bchY37 a b := by
  simp only [y37Tab, bchY37, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, evalKTab_bchTTable_five, bchZ]

/-- **`(y⁴)_d7` as a table**: `evalKTab a b y47Tab = bchY47 a b`. -/
lemma evalKTab_y47Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y47Tab = bchY47 a b := by
  simp only [y47Tab, bchY47, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three,
    evalKTab_bchTTable_four, bchZ]

/-- **`(y⁵)_d7` as a table**: `evalKTab a b y57Tab = bchY57 a b`. -/
lemma evalKTab_y57Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y57Tab = bchY57 a b := by
  simp only [y57Tab, bchY57, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, evalKTab_bchTTable_three, bchZ]

/-- **`(y⁶)_d7` as a table**: `evalKTab a b y67Tab = bchY67 a b`. -/
lemma evalKTab_y67Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b y67Tab = bchY67 a b := by
  simp only [y67Tab, bchY67, bchZ, evalKTab_append, evalKTab_mulKTab, evalKTab_powKTab]
  simp only [evalKTab_bchTTable_one, evalKTab_bchTTable_two, bchZ]

/-- **The `z⁷` table's evaluation**: `z = a + b` raised to the seventh. -/
lemma evalKTab_z7Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b z7Tab = bchZ a b ^ 7 := by
  rw [z7Tab, evalKTab_powKTab, evalKTab_bchTTable_one]

/-- **`bchSepticTerm`'s table**: `bchSepticTerm` is *defined* by evaluating
`bchSepticTermTable`, so this is the table itself, not a copy of it. -/
def septicTab : KTab := bchSepticTermTable

/-- **The evaluation of the septic table is `bchSepticTerm` itself.** -/
theorem evalKTab_septicTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b septicTab = bchSepticTerm a b :=
  rfl

/-- **The degree-7 Dynkin side as a table**: the left-hand side of `octic_pure_identity`,
multiplied through by `lcm(1, …, 7) = 420` so that the multipliers are integers. -/
def dynkin7Tab : KTab :=
  smulKTab 210 w7Tab ++ smulKTab 140 y37Tab ++ smulKTab (-105) y47Tab ++
    smulKTab 84 y57Tab ++ smulKTab (-70) y67Tab ++ smulKTab 60 z7Tab ++
    smulKTab (-420) septicTab

/-- **The degree-7 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `420` times the
Dynkin/Ree expression of `octic_pure_identity`. -/
theorem evalKTab_dynkin7Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin7Tab
      = (420 : ℚ) • ((2 : ℚ)⁻¹ • bchW7 a b + (3 : ℚ)⁻¹ • bchY37 a b -
          (4 : ℚ)⁻¹ • bchY47 a b + (5 : ℚ)⁻¹ • bchY57 a b - (6 : ℚ)⁻¹ • bchY67 a b +
          (7 : ℚ)⁻¹ • bchZ a b ^ 7 - bchSepticTerm a b) := by
  rw [dynkin7Tab]
  simp only [evalKTab_append, evalKTab_smulKTab]
  rw [evalKTab_w7Tab, evalKTab_y37Tab, evalKTab_y47Tab, evalKTab_y57Tab, evalKTab_y67Tab,
    evalKTab_z7Tab, evalKTab_septicTab]
  rw [show (420 : ℚ) • ((2 : ℚ)⁻¹ • bchW7 a b + (3 : ℚ)⁻¹ • bchY37 a b -
        (4 : ℚ)⁻¹ • bchY47 a b + (5 : ℚ)⁻¹ • bchY57 a b - (6 : ℚ)⁻¹ • bchY67 a b +
        (7 : ℚ)⁻¹ • bchZ a b ^ 7 - bchSepticTerm a b)
      = (210 : ℚ) • bchW7 a b + (140 : ℚ) • bchY37 a b - (105 : ℚ) • bchY47 a b +
        (84 : ℚ) • bchY57 a b - (70 : ℚ) • bchY67 a b + (60 : ℚ) • bchZ a b ^ 7 -
        (420 : ℚ) • bchSepticTerm a b from by
    module]
  norm_num
  abel

/-! ### The coefficient comparison, one piece at a time

`dynkin7Tab` is a `++`-chain of seven scaled piece tables. Rather than collapsing the chain in one
goal, each piece is collapsed on its own and merged into the running accumulator, which stays at one
row per word (128 here) throughout. `septicTab` is already in normal form — it *is*
`bchSepticTermTable`, one row per word — so it needs no collapse of its own. -/

/-- **The accumulated normal form of the degree-7 comparison**, one `def` per piece: each stage
collapses the next scaled piece into the running accumulator, and every stage is a 128-row table
(one row per word). Naming the stages is what keeps the elaboration of the fold cheap — a single
nested `collapseAuxK` term seven deep is re-reduced at each enclosing `whnf`, which is exactly the
kind of cost `DynkinReeToolbox.lean` avoids by naming the pieces `T₂ … T₇`.

`septicTab` is already in normal form — it *is* `bchSepticTermTable`, one row per word — so the last
stage needs no collapse of its own. -/
def dynkin7Acc1 : KTab := collapseK (smulKTab 210 w7Tab)

/-- Stage 2 of the degree-7 accumulation. -/
def dynkin7Acc2 : KTab := collapseAuxK (smulKTab 140 y37Tab) dynkin7Acc1

/-- Stage 3 of the degree-7 accumulation. -/
def dynkin7Acc3 : KTab := collapseAuxK (smulKTab (-105) y47Tab) dynkin7Acc2

/-- Stage 4 of the degree-7 accumulation. -/
def dynkin7Acc4 : KTab := collapseAuxK (smulKTab 84 y57Tab) dynkin7Acc3

/-- Stage 5 of the degree-7 accumulation. -/
def dynkin7Acc5 : KTab := collapseAuxK (smulKTab (-70) y67Tab) dynkin7Acc4

/-- Stage 6 of the degree-7 accumulation. -/
def dynkin7Acc6 : KTab := collapseAuxK (smulKTab 60 z7Tab) dynkin7Acc5

/-- **The accumulated normal form of the degree-7 comparison**: every piece of `dynkin7Tab`
collapsed in order and merged. -/
def dynkin7Norm : KTab := collapseAuxK (smulKTab (-420) septicTab) dynkin7Acc6

set_option maxRecDepth 100000 in
/-- **The degree-7 coefficient comparison**: the accumulated normal form has no nonzero
coefficient. `dynkin7Norm` already *is* a collapsed table — every stage of the fold merged its rows
by word — so this is one check of 128 coefficients, with no collapse to redo.

`decide +kernel` rather than plain `decide`: the default evaluator runs out of budget on the
reduction `dynkin7Norm` denotes, while the kernel's own reduction — which is what `rfl` and `decide`
check against anyway — completes it. No heartbeat budget is raised.

The `maxRecDepth` is a *tactic recursion depth* limit on walking the ~1000 nested `List.cons` cells
of the accumulated table, not a search or heartbeat budget. -/
theorem dynkin7Norm_all_zero :
    dynkin7Norm.all (fun p => p.2 == 0) = true := by
  decide +kernel

/-- **The degree-7 cancellation, as a table identity.** -/
theorem evalKTab_dynkin7Norm_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin7Norm = 0 :=
  evalKTab_eq_zero_of_all_beq a b _ dynkin7Norm_all_zero

/-- **`dynkin7Tab` evaluates to its accumulated normal form**: `dynkin7Norm` is exactly the
piece-by-piece collapse of `dynkin7Tab`, so the two evaluate equally.

The proof is the split itself: `collapseK_append` peels one scaled piece off the chain at a time,
and `evalKTab_congr_collapseK` carries the resulting table identity back to the evaluation. -/
theorem evalKTab_dynkin7Tab_eq_dynkin7Norm {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin7Tab = evalKTab a b dynkin7Norm := by
  have h : collapseK dynkin7Tab = dynkin7Norm := by
    rw [dynkin7Tab]
    simp only [collapseK_append]
    rw [← dynkin7Acc1, ← dynkin7Acc2, ← dynkin7Acc3, ← dynkin7Acc4, ← dynkin7Acc5,
      ← dynkin7Acc6, ← dynkin7Norm]
  rw [evalKTab_congr_collapseK a b h]

/-- **The degree-7 cancellation, in the free word algebra**: the left-hand side is zero. -/
theorem evalKTab_dynkin7Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    evalKTab a b dynkin7Tab = 0 := by
  rw [evalKTab_dynkin7Tab_eq_dynkin7Norm, evalKTab_dynkin7Norm_eq_zero]

/-- **The degree-7 pure identity**: the degree-7 part of
`½W7 + ⅓y3₇ - ¼y4₇ + ⅕y5₇ - ⅙y6₇ + z⁷/7`, written in `z = a + b` and the degree-2/3/4/5/6 parts
`T₂`…`T₆` of `y = exp a * exp b - 1`, minus `bchSepticTerm a b`, is zero.

This is the degree-7 cancellation behind `pieceB_octic_decomp`, and the companion of
`septic_pure_identity` (degree 6). The name is the source's and is one ahead of the degree. -/
theorem octic_pure_identity {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW7 a b + (3 : ℚ)⁻¹ • bchY37 a b - (4 : ℚ)⁻¹ • bchY47 a b +
      (5 : ℚ)⁻¹ • bchY57 a b - (6 : ℚ)⁻¹ • bchY67 a b + (7 : ℚ)⁻¹ • bchZ a b ^ 7 -
      bchSepticTerm a b = 0 := by
  have h := evalKTab_dynkin7Tab (𝔸 := 𝔸) a b
  rw [evalKTab_dynkin7Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h420 | hX
  · exact absurd h420 (by norm_num)
  · exact hX

end FQFP.BCH
