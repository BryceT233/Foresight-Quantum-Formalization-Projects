/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.DynkinReeToolbox

/-!
# Degree 5: the cancellation behind `bchQuinticTerm`

The pure identity of this file is `sextic_pure_identity` — the name is the source's, and it is one
ahead of the degree it settles; see `DynkinReeToolbox.lean` for the family and the naming. It says
that the degree-5 part of the Dynkin/Ree form vanishes:

    ½·W5 + ⅓·(y³)_d5 - ¼·(y⁴)_d5 + ⅕·z⁵ - bchQuinticTerm = 0,

where `z = a + b`, `T_k` is the degree-`k` part of `y = exp a * exp b - 1`,
`W5 = 2·y_d5 - (y²)_d5`, and `(y^m)_d5` is the degree-5 part of `y^m` — the sum over the positive
compositions of `5` into `m` parts, in lexicographic order.

## How it is proved

By computation. Each piece is a *table* (`w5Tab`, `y35Tab`, `y45Tab`, `z5Tab`, and
`bchQuinticTermTable` from `BCHTerms.lean`), the whole left-hand side multiplied through by
`lcm(1, …, 5) = 60` is `dynkin5Tab`, and comparing the two sides becomes one `decide` on a `List`
and `ℤ` computation: 310 raw rows against the 32 words of degree 5. The bridge lemmas
`eval_*` are the only place the `coefficientScale`-factors are discharged, and
`eval_dynkin5Tab_eq_zero` carries the table identity back to an arbitrary `ℚ`-algebra.

## Provenance

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:81-143`). The source
states the identity inline as a `let` chain over an arbitrary `RCLike 𝕂`; the statement here is the
same identity with the pieces named in `DynkinReeToolbox.lean`.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

variable {𝔸 : Type*}

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

/-! ### The degree-5 tables

The five pieces as tables, so that the coefficient comparison is a computation. Four of them are
built here from `bchTTable`; the fifth, `bchQuinticTermTable`, is the term's own data and lives next
to `bchQuinticTerm` in `BCHTerms.lean`. -/

/-- The degree-5 `W5` table, mirroring `bchW5`. -/
def w5Tab : WordTable.Table (Fin 2) :=
  smul 2 (bchTTable 5) ++ smul (-1) (mul (bchTTable 1) (bchTTable 4)) ++
    smul (-1) (mul (bchTTable 2) (bchTTable 3)) ++
    smul (-1) (mul (bchTTable 3) (bchTTable 2)) ++
    smul (-1) (mul (bchTTable 4) (bchTTable 1))

/-- **`W5` as a table**: `eval coefficientScale ![a, b] w5Tab = bchW5 a b`. -/
lemma eval_w5Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] w5Tab = bchW5 a b := by
  simp only [w5Tab, bchW5, bchZ, eval_append, eval_smul, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, eval_bchTTable_five, bchZ, bchT5]
  simp only [smul_add, smul_smul]
  norm_num
  abel

/-- The degree-5 `(y³)_d5` table, mirroring `bchY35`. -/
def y35Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 2) (bchTTable 3) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1) ++
    mul (bchTTable 3) (pow (bchTTable 1) 2) ++
    mul (bchTTable 1) (pow (bchTTable 2) 2) ++
    mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2) ++
    mul (pow (bchTTable 2) 2) (bchTTable 1)

/-- **`(y³)_d5` as a table**: `eval coefficientScale ![a, b] y35Tab = bchY35 a b`. -/
lemma eval_y35Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y35Tab = bchY35 a b := by
  simp only [y35Tab, bchY35, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, bchZ]

/-- The degree-5 `(y⁴)_d5` table, mirroring `bchY45`. -/
def y45Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 3) (bchTTable 2) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (pow (bchTTable 1) 2) ++
    mul (bchTTable 2) (pow (bchTTable 1) 3)

/-- **`(y⁴)_d5` as a table**: `eval coefficientScale ![a, b] y45Tab = bchY45 a b`. -/
lemma eval_y45Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y45Tab = bchY45 a b := by
  simp only [y45Tab, bchY45, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, bchZ]

/-- The degree-5 `z⁵` table, mirroring `(bchZ a b) ^ 5`. -/
def z5Tab : WordTable.Table (Fin 2) := pow (bchTTable 1) 5

/-- **The `z⁵` table's evaluation**: `z = a + b` raised to the fifth. -/
lemma eval_z5Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] z5Tab = bchZ a b ^ 5 := by
  rw [z5Tab, eval_pow, eval_bchTTable_one]

/-- **The degree-5 Dynkin side as a table**: the left-hand side of `sextic_pure_identity`,
multiplied through by `lcm(1, …, 5) = 60` so that the multipliers are integers. -/
def dynkin5Tab : WordTable.Table (Fin 2) :=
  smul 30 w5Tab ++ smul 20 y35Tab ++ smul (-15) y45Tab ++
    smul 12 z5Tab ++ smul (-60) bchQuinticTermTable

/-- **The degree-5 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `60` times the
Dynkin/Ree expression of `sextic_pure_identity`. -/
theorem eval_dynkin5Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin5Tab
      = (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b -
          (4 : ℚ)⁻¹ • bchY45 a b + (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b) := by
  rw [dynkin5Tab]
  simp only [eval_append, eval_smul]
  rw [eval_w5Tab, eval_y35Tab, eval_y45Tab, eval_z5Tab,
    eval_bchQuinticTermTable]
  rw [show (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b -
        (4 : ℚ)⁻¹ • bchY45 a b + (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b)
      = (30 : ℚ) • bchW5 a b + (20 : ℚ) • bchY35 a b - (15 : ℚ) • bchY45 a b +
        (12 : ℚ) • bchZ a b ^ 5 - (60 : ℚ) • bchQuinticTerm a b from by
    module]
  norm_num
  abel

set_option maxRecDepth 10000 in
/-- **The degree-5 coefficient comparison**: collapsing the left-hand side leaves no nonzero
coefficient. This single `decide` is the whole computation: 310 raw rows against the 32 words. -/
theorem collapse_dynkin5Tab_all_zero :
    (collapse dynkin5Tab).all (fun p => p.2 == 0) = true := by
  decide

/-- **The degree-5 cancellation, as a table identity**: the collapsed left-hand side evaluates to
zero in any `ℚ`-algebra. -/
theorem eval_dynkin5Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin5Tab = 0 := by
  rw [← eval_collapse]
  exact eval_eq_zero_of_all_beq coefficientScale ![a, b] _ collapse_dynkin5Tab_all_zero

/-- **The degree-5 pure identity**: the degree-5 part of `½W5 + ⅓y3₅ - ¼y4₅ + ⅕z⁵`, written in
`z = a + b` and the degree-2/3/4 parts `T₂`, `T₃`, `T₄` of `y = exp a * exp b - 1`, minus
`bchQuinticTerm a b`, is zero.

This is the degree-5 cancellation behind `pieceB_sextic_decomp`. The name is the source's and is
one ahead of the degree; the companion at degree 6 is `septic_pure_identity` in
`DynkinReeSextic.lean`. -/
theorem sextic_pure_identity {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW5 a b + (3 : ℚ)⁻¹ • bchY35 a b - (4 : ℚ)⁻¹ • bchY45 a b +
      (5 : ℚ)⁻¹ • bchZ a b ^ 5 - bchQuinticTerm a b = 0 := by
  have h := eval_dynkin5Tab (𝔸 := 𝔸) a b
  rw [eval_dynkin5Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h60 | hX
  · exact absurd h60 (by norm_num)
  · exact hX

end FQFP.BCH
