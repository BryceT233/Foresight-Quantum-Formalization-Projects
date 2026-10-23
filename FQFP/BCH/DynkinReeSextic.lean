/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.DynkinReeQuintic

/-!
# Degree 6: the cancellation behind `bchSexticTerm`

The pure identity of this file is `septic_pure_identity` — the name is the source's, and it is one
ahead of the degree it settles; see `DynkinReeToolbox.lean` for the family and the naming. It says
that the degree-6 part of the Dynkin/Ree form vanishes:

    ½·W6 + ⅓·(y³)_d6 - ¼·(y⁴)_d6 + ⅕·(y⁵)_d6 - ⅙·z⁶ - bchSexticTerm = 0,

where `z = a + b`, `T_k` is the degree-`k` part of `y = exp a * exp b - 1`, `W6 = 2·y_d6 - (y²)_d6`,
and `(y^m)_d6` is the degree-6 part of `y^m` — the sum over the positive compositions of `6` into
`m` parts, in lexicographic order.

## How it is proved

By computation, exactly as at degree 5. Each of the six pieces is a table (`w6Tab`, `y36Tab`,
`y46Tab`, `y56Tab`, `z6Tab`, and `sexticTab`, which *is* `bchSexticTermTable`), the left-hand side
multiplied through by `lcm(1, …, 6) = 60` is `dynkin6Tab`, and the coefficient comparison is one
`decide`: 984 raw rows against the 64 words of degree 6.

The `maxRecDepth` on that `decide` is a *tactic recursion depth* limit on walking the ~1000 nested
`List.cons` cells of the collapsed table, not a search or heartbeat budget.

## Provenance

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:144-228`). The source
states the identity inline as a `let` chain over an arbitrary `RCLike 𝕂` with
`set_option maxHeartbeats 64000000`; the statement here is the same identity with the pieces named,
and no heartbeat budget is raised.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

variable {𝔸 : Type*}

/-- `W6 = 2·y_d6 - (y²)_d6`, the degree-6 start of the Dynkin/Ree form. -/
def bchW6 {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) : 𝔸 :=
  2 • bchT6 a b -
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

/-! ### The degree-6 tables

Every piece is written in the same order and with the same shape as its ring-level counterpart
above, so its bridge is a `simp only` that pushes `eval` through the table operations,
discharges the `coefficientScale ^ 6` factors with `norm_num`, and reorders with `abel`. -/

/-- The degree-6 `W6` table, mirroring `bchW6`. -/
def w6Tab : WordTable.Table (Fin 2) :=
  smul 2 (bchTTable 6) ++ smul (-1) (mul (bchTTable 1) (bchTTable 5)) ++
    smul (-1) (mul (bchTTable 2) (bchTTable 4)) ++
    smul (-1) (mul (bchTTable 3) (bchTTable 3)) ++
    smul (-1) (mul (bchTTable 4) (bchTTable 2)) ++
    smul (-1) (mul (bchTTable 5) (bchTTable 1))

/-- **`W6` as a table**: `eval coefficientScale ![a, b] w6Tab = bchW6 a b`. -/
lemma eval_w6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] w6Tab = bchW6 a b := by
  simp only [w6Tab, bchW6, bchZ, eval_append, eval_smul, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, eval_bchTTable_five, eval_bchTTable_six, bchZ]
  norm_cast; norm_num
  abel

/-- The degree-6 `(y³)_d6` table, mirroring `bchY36`. -/
def y36Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 2) (bchTTable 4) ++
    mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 1) ++
    mul (bchTTable 4) (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 1) ++
    pow (bchTTable 2) 3

/-- **`(y³)_d6` as a table**: `eval coefficientScale ![a, b] y36Tab = bchY36 a b`. -/
lemma eval_y36Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y36Tab = bchY36 a b := by
  simp only [y36Tab, bchY36, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, bchZ]

/-- The degree-6 `(y⁴)_d6` table, mirroring `bchY46`. -/
def y46Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 3) (bchTTable 3) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (pow (bchTTable 1) 2) ++
    mul (bchTTable 3) (pow (bchTTable 1) 3) ++
    mul (pow (bchTTable 1) 2) (pow (bchTTable 2) 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (bchTTable 1) (pow (bchTTable 2) 2)) (bchTTable 1) ++
    mul (mul (bchTTable 2) (pow (bchTTable 1) 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (pow (bchTTable 2) 2) (pow (bchTTable 1) 2)

/-- **`(y⁴)_d6` as a table**: `eval coefficientScale ![a, b] y46Tab = bchY46 a b`. -/
lemma eval_y46Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y46Tab = bchY46 a b := by
  simp only [y46Tab, bchY46, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, bchZ]

/-- The degree-6 `(y⁵)_d6` table, mirroring `bchY56`. -/
def y56Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 4) (bchTTable 2) ++
    mul (mul (pow (bchTTable 1) 3) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (pow (bchTTable 1) 3) ++
    mul (bchTTable 2) (pow (bchTTable 1) 4)

/-- **`(y⁵)_d6` as a table**: `eval coefficientScale ![a, b] y56Tab = bchY56 a b`. -/
lemma eval_y56Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y56Tab = bchY56 a b := by
  simp only [y56Tab, bchY56, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, bchZ]

/-- The degree-6 `z⁶` table, mirroring `(bchZ a b) ^ 6`. -/
def z6Tab : WordTable.Table (Fin 2) := pow (bchTTable 1) 6

/-- **The `z⁶` table's evaluation**: `z = a + b` raised to the sixth. -/
lemma eval_z6Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] z6Tab = bchZ a b ^ 6 := by
  rw [z6Tab, eval_pow, eval_bchTTable_one]

/-- **`bchSexticTerm`'s table**: `bchSexticTerm` is *defined* by evaluating
`bchSexticTermTable`, so this is the table itself, not a copy of it. -/
def sexticTab : WordTable.Table (Fin 2) := bchSexticTermTable

/-- **The evaluation of the sextic table is `bchSexticTerm` itself**: with `sexticTab` being
`bchSexticTermTable` this is `rfl`-level, which is the point of defining the term from its table. -/
theorem eval_sexticTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] sexticTab = bchSexticTerm a b :=
  rfl

/-- **The degree-6 Dynkin side as a table**: the left-hand side of `septic_pure_identity`,
multiplied through by `lcm(1, …, 6) = 60` so that the multipliers are integers.

Unlike the table of the rational version of this proof, this one is deliberately *not*
`irreducible`: it is unfolded exactly once, by the `decide` below, and nothing else compares goals
whose type mentions it. -/
def dynkin6Tab : WordTable.Table (Fin 2) :=
  smul 30 w6Tab ++ smul 20 y36Tab ++ smul (-15) y46Tab ++
    smul 12 y56Tab ++ smul (-10) z6Tab ++ smul (-60) sexticTab

/-- **The degree-6 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `60` times the
Dynkin/Ree expression of `septic_pure_identity`. The factor `60` is what clears the rational
scalars `½ … ⅙` before the `coefficientScale`-scaling. -/
theorem eval_dynkin6Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin6Tab
      = (60 : ℚ) • ((2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b -
          (4 : ℚ)⁻¹ • bchY46 a b + (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 -
          bchSexticTerm a b) := by
  rw [dynkin6Tab]
  simp only [eval_append, eval_smul]
  rw [eval_w6Tab, eval_y36Tab, eval_y46Tab, eval_y56Tab, eval_z6Tab,
    eval_sexticTab]
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
theorem collapse_dynkin6Tab_all_zero :
    (collapse dynkin6Tab).all (fun p => p.2 == 0) = true := by
  decide

/-- **The degree-6 cancellation, as a table identity**: the collapsed left-hand side evaluates to
zero in any `ℚ`-algebra. -/
theorem eval_dynkin6Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin6Tab = 0 := by
  rw [← eval_collapse]
  exact eval_eq_zero_of_all_beq coefficientScale ![a, b] _ collapse_dynkin6Tab_all_zero

/-- **The degree-6 pure identity**: the degree-6 part of `½W6 + ⅓y3₆ - ¼y4₆ + ⅕y5₆ - ⅙z⁶`,
written in `z = a + b` and the degree-2/3/4/5 parts `T₂`…`T₅` of `y = exp a * exp b - 1`, minus
`bchSexticTerm a b`, is zero.

This is the degree-6 cancellation behind `pieceB_septic_decomp`. The name is the source's and is one
ahead of the degree; the companion at degree 5 is `sextic_pure_identity` in
`DynkinReeQuintic.lean`. -/
theorem septic_pure_identity {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW6 a b + (3 : ℚ)⁻¹ • bchY36 a b - (4 : ℚ)⁻¹ • bchY46 a b +
      (5 : ℚ)⁻¹ • bchY56 a b - (6 : ℚ)⁻¹ • bchZ a b ^ 6 - bchSexticTerm a b = 0 := by
  have h := eval_dynkin6Tab (𝔸 := 𝔸) a b
  rw [eval_dynkin6Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h60 | hX
  · exact absurd h60 (by norm_num)
  · exact hX

end FQFP.BCH
