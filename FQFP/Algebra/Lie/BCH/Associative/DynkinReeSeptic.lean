/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Associative.DynkinReeSextic
public import FQFP.Algebra.Word.BinaryTable

/-!
# Degree 7: the cancellation behind `bchSepticTerm`

The pure identity of this file is `octic_pure_identity` — the name is the source's, and it is one
ahead of the degree it settles; see `DynkinReeToolbox.lean` for the family and the naming. It says
that the degree-7 part of the Dynkin/Ree form vanishes:

    ½·W7 + ⅓·(y³)_d7 - ¼·(y⁴)_d7 + ⅕·(y⁵)_d7 - ⅙·(y⁶)_d7 + (1/7)·z⁷ - bchSepticTerm = 0,

where `z = a + b`, `T_k` is the degree-`k` part of `y = exp a * exp b - 1`,
`W7 = 2·y_d7 - (y²)_d7`, and each `(y^m)_d7` is the sum over the positive compositions of `7` into
`m` parts, in lexicographic order — written in that same order at the ring level and as a table.

## Coefficient computation

`BinaryWordTable.collect` inserts each row along its binary word path. Unlike the old
linear-list accumulator, insertion never scans the other words already collected.
`BinaryWordTable.eval_table_eq_zero` transports the checked integer coefficients to any
rational algebra. The final identity and coefficient data are unchanged.

Profiling and the degree-eight coefficient stress check are recorded in
`artifacts/bch/performance-and-unused-code-2026-10-23.md`.

## Provenance

Ported from `Lean-BCH/BCH/SmallSDischarge.lean` (`BCH/SmallSDischarge.lean:229-436`). The source
states the identity as an inline expansion over an arbitrary `RCLike 𝕂` with
`set_option maxHeartbeats 64000000`; the statement here is the same identity with the pieces named,
and no heartbeat budget is raised.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

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
def w7Tab : WordTable.Table (Fin 2) :=
  smul 2 (bchTTable 7) ++
    (smul (-1) (mul (bchTTable 1) (bchTTable 6)) ++
      smul (-1) (mul (bchTTable 2) (bchTTable 5)) ++
      smul (-1) (mul (bchTTable 3) (bchTTable 4)) ++
      smul (-1) (mul (bchTTable 4) (bchTTable 3)) ++
      smul (-1) (mul (bchTTable 5) (bchTTable 2)) ++
      smul (-1) (mul (bchTTable 6) (bchTTable 1)))

/-- The degree-7 `(y^3)_d7` table, mirroring `bchY37`. -/
def y37Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 2) (bchTTable 5) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 4) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 3) ++
    mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 2) ++
    mul (mul (bchTTable 1) (bchTTable 5)) (bchTTable 1) ++
    mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 4) ++
    mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (bchTTable 2) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (bchTTable 3) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (bchTTable 4) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (bchTTable 4) (bchTTable 2)) (bchTTable 1) ++
    mul (bchTTable 5) (pow (bchTTable 1) 2)

/-- The degree-7 `(y^4)_d7` table, mirroring `bchY47`. -/
def y47Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 3) (bchTTable 4) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (bchTTable 1) (bchTTable 4)) (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 2) (pow (bchTTable 1) 2)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (bchTTable 2) (bchTTable 3)) (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 3) (pow (bchTTable 1) 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (bchTTable 3) (bchTTable 2)) (pow (bchTTable 1) 2) ++
    mul (bchTTable 4) (pow (bchTTable 1) 3)

/-- The degree-7 `(y^5)_d7` table, mirroring `bchY57`. -/
def y57Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 4) (bchTTable 3) ++
    mul (mul (pow (bchTTable 1) 3) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (pow (bchTTable 1) 3) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (bchTTable 1))
      (bchTTable 2) ++
    mul (mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (bchTTable 2))
      (bchTTable 1) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 3)) (pow (bchTTable 1) 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (pow (bchTTable 1) 2))
      (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2))
      (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2))
      (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (pow (bchTTable 1) 3) ++
    mul (mul (bchTTable 2) (pow (bchTTable 1) 3)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (pow (bchTTable 1) 2)) (bchTTable 2))
      (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2))
      (pow (bchTTable 1) 2) ++
    mul (mul (bchTTable 2) (bchTTable 2)) (pow (bchTTable 1) 3) ++
    mul (bchTTable 3) (pow (bchTTable 1) 4)

/-- The degree-7 `(y^6)_d7` table, mirroring `bchY67`. -/
def y67Tab : WordTable.Table (Fin 2) :=
  mul (pow (bchTTable 1) 5) (bchTTable 2) ++
    mul (mul (pow (bchTTable 1) 4) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (pow (bchTTable 1) 3) (bchTTable 2)) (pow (bchTTable 1) 2) ++
    mul (mul (pow (bchTTable 1) 2) (bchTTable 2)) (pow (bchTTable 1) 3) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (pow (bchTTable 1) 4) ++
    mul (bchTTable 2) (pow (bchTTable 1) 5)

/-- The degree-7 `z⁷` table, mirroring `(bchZ a b) ^ 7`. -/
def z7Tab : WordTable.Table (Fin 2) := pow (bchTTable 1) 7

/-- **`W7` as a table**: `eval coefficientScale ![a, b] w7Tab = bchW7 a b`. -/
lemma eval_w7Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] w7Tab = bchW7 a b := by
  simp only [w7Tab, bchW7, bchZ, eval_append, eval_smul, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, eval_bchTTable_five, eval_bchTTable_six,
    eval_bchTTable_seven, bchZ]
  norm_cast; norm_num
  abel

/-- **`(y³)_d7` as a table**: `eval coefficientScale ![a, b] y37Tab = bchY37 a b`. -/
lemma eval_y37Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y37Tab = bchY37 a b := by
  simp only [y37Tab, bchY37, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, eval_bchTTable_five, bchZ]

/-- **`(y⁴)_d7` as a table**: `eval coefficientScale ![a, b] y47Tab = bchY47 a b`. -/
lemma eval_y47Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y47Tab = bchY47 a b := by
  simp only [y47Tab, bchY47, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, bchZ]

/-- **`(y⁵)_d7` as a table**: `eval coefficientScale ![a, b] y57Tab = bchY57 a b`. -/
lemma eval_y57Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y57Tab = bchY57 a b := by
  simp only [y57Tab, bchY57, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, bchZ]

/-- **`(y⁶)_d7` as a table**: `eval coefficientScale ![a, b] y67Tab = bchY67 a b`. -/
lemma eval_y67Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] y67Tab = bchY67 a b := by
  simp only [y67Tab, bchY67, bchZ, eval_append, eval_mul, eval_pow]
  simp only [eval_bchTTable_one, eval_bchTTable_two, bchZ]

/-- **The `z⁷` table's evaluation**: `z = a + b` raised to the seventh. -/
lemma eval_z7Tab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] z7Tab = bchZ a b ^ 7 := by
  rw [z7Tab, eval_pow, eval_bchTTable_one]

/-- **`bchSepticTerm`'s table**: `bchSepticTerm` is *defined* by evaluating
`bchSepticTermTable`, so this is the table itself, not a copy of it. -/
def septicTab : WordTable.Table (Fin 2) := bchSepticTermTable

/-- **The evaluation of the septic table is `bchSepticTerm` itself.** -/
theorem eval_septicTab {𝔸 : Type*} [Semiring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] septicTab = bchSepticTerm a b :=
  rfl

/-- **The degree-7 Dynkin side as a table**: the left-hand side of `octic_pure_identity`,
multiplied through by `lcm(1, …, 7) = 420` so that the multipliers are integers. -/
def dynkin7Tab : WordTable.Table (Fin 2) :=
  smul 210 w7Tab ++ smul 140 y37Tab ++ smul (-105) y47Tab ++
    smul 84 y57Tab ++ smul (-70) y67Tab ++ smul 60 z7Tab ++
    smul (-420) septicTab

/-- **The degree-7 left-hand side, evaluated in an arbitrary `ℚ`-algebra**: `420` times the
Dynkin/Ree expression of `octic_pure_identity`. -/
theorem eval_dynkin7Tab {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin7Tab
      = (420 : ℚ) • ((2 : ℚ)⁻¹ • bchW7 a b + (3 : ℚ)⁻¹ • bchY37 a b -
          (4 : ℚ)⁻¹ • bchY47 a b + (5 : ℚ)⁻¹ • bchY57 a b - (6 : ℚ)⁻¹ • bchY67 a b +
          (7 : ℚ)⁻¹ • bchZ a b ^ 7 - bchSepticTerm a b) := by
  rw [dynkin7Tab]
  simp only [eval_append, eval_smul]
  rw [eval_w7Tab, eval_y37Tab, eval_y47Tab, eval_y57Tab, eval_y67Tab,
    eval_z7Tab, eval_septicTab]
  module

/-! ### Prefix-tree coefficient comparison -/

/-- The binary prefix tree of the degree-seven comparison has only zero coefficients. -/
theorem dynkin7Tab_isZero :
    BinaryWordTable.isZero (BinaryWordTable.collect dynkin7Tab) = true := by
  decide +kernel

/-- The degree-seven coefficient certificate evaluates to zero. -/
theorem eval_dynkin7Tab_eq_zero {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    eval coefficientScale ![a, b] dynkin7Tab = 0 :=
  BinaryWordTable.eval_table_eq_zero _ _ _ dynkin7Tab_isZero

/-- **The degree-7 pure identity**: the degree-7 part of
`½W7 + ⅓y3₇ - ¼y4₇ + ⅕y5₇ - ⅙y6₇ + z⁷/7`, written in `z = a + b` and the degree-2/3/4/5/6 parts
`T₂`…`T₆` of `y = exp a * exp b - 1`, minus `bchSepticTerm a b`, is zero.

This is the degree-7 cancellation behind `pieceB_octic_decomp`, and the companion of
`septic_pure_identity` (degree 6). The name is the source's and is one ahead of the degree. -/
theorem octic_pure_identity {𝔸 : Type*} [Ring 𝔸] [Algebra ℚ 𝔸] (a b : 𝔸) :
    (2 : ℚ)⁻¹ • bchW7 a b + (3 : ℚ)⁻¹ • bchY37 a b - (4 : ℚ)⁻¹ • bchY47 a b +
      (5 : ℚ)⁻¹ • bchY57 a b - (6 : ℚ)⁻¹ • bchY67 a b + (7 : ℚ)⁻¹ • bchZ a b ^ 7 -
      bchSepticTerm a b = 0 := by
  have h := eval_dynkin7Tab (𝔸 := 𝔸) a b
  rw [eval_dynkin7Tab_eq_zero] at h
  rcases smul_eq_zero.mp h.symm with h420 | hX
  · exact absurd h420 (by norm_num)
  · exact hX

end FQFP.BCH
