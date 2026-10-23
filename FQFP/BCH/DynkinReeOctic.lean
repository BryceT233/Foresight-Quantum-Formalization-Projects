/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.DynkinReeToolbox
public import FQFP.BCH.Algebra.BinaryWordTable

/-!
# Degree-eight BCH coefficient identity

`bchOcticTerm_eq` identifies the eighth homogeneous BCH term with the eighth-degree
part of the logarithm series of `exp a * exp b`. Products remain in their original order.
The powers `y³` through `y⁷` contribute respectively 21, 35, 35, 21, and 7 positive
compositions of eight. The coefficient check uses `BinaryWordTable` prefix trees.

This is the identity called `nonic_pure_identity` in
`Lean-BCH/BCH/SmallSDischarge.lean`: the source name refers to the following remainder
order. Its ring expression is preserved, with the rational coefficients interpreted
in an arbitrary rational algebra. No norm or completeness assumptions are needed.
-/

@[expose] public section

namespace FQFP.BCH

open WordTable

/-! ### Homogeneous pieces -/

/-- Twice the eighth component of `y`, minus the eighth component of `y²`. -/
def bchW8 {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) : A :=
  2 • bchT8 a b -
    (bchZ a b * bchT7 a b + bchT2 a b * bchT6 a b + bchT3 a b * bchT5 a b +
      bchT4 a b * bchT4 a b + bchT5 a b * bchT3 a b + bchT6 a b * bchT2 a b +
      bchT7 a b * bchZ a b)

/-- The eighth homogeneous component of `y^3`, with 21 ordered products. -/
def bchY38 {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  bchZ a b * bchZ a b * bchT6 a b +
    bchZ a b * bchT2 a b * bchT5 a b +
    bchZ a b * bchT3 a b * bchT4 a b +
    bchZ a b * bchT4 a b * bchT3 a b +
    bchZ a b * bchT5 a b * bchT2 a b +
    bchZ a b * bchT6 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT5 a b +
    bchT2 a b * bchT2 a b * bchT4 a b +
    bchT2 a b * bchT3 a b * bchT3 a b +
    bchT2 a b * bchT4 a b * bchT2 a b +
    bchT2 a b * bchT5 a b * bchZ a b +
    bchT3 a b * bchZ a b * bchT4 a b +
    bchT3 a b * bchT2 a b * bchT3 a b +
    bchT3 a b * bchT3 a b * bchT2 a b +
    bchT3 a b * bchT4 a b * bchZ a b +
    bchT4 a b * bchZ a b * bchT3 a b +
    bchT4 a b * bchT2 a b * bchT2 a b +
    bchT4 a b * bchT3 a b * bchZ a b +
    bchT5 a b * bchZ a b * bchT2 a b +
    bchT5 a b * bchT2 a b * bchZ a b +
    bchT6 a b * bchZ a b * bchZ a b

/-- The eighth homogeneous component of `y^4`, with 35 ordered products. -/
def bchY48 {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  bchZ a b * bchZ a b * bchZ a b * bchT5 a b +
    bchZ a b * bchZ a b * bchT2 a b * bchT4 a b +
    bchZ a b * bchZ a b * bchT3 a b * bchT3 a b +
    bchZ a b * bchZ a b * bchT4 a b * bchT2 a b +
    bchZ a b * bchZ a b * bchT5 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT4 a b +
    bchZ a b * bchT2 a b * bchT2 a b * bchT3 a b +
    bchZ a b * bchT2 a b * bchT3 a b * bchT2 a b +
    bchZ a b * bchT2 a b * bchT4 a b * bchZ a b +
    bchZ a b * bchT3 a b * bchZ a b * bchT3 a b +
    bchZ a b * bchT3 a b * bchT2 a b * bchT2 a b +
    bchZ a b * bchT3 a b * bchT3 a b * bchZ a b +
    bchZ a b * bchT4 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT4 a b * bchT2 a b * bchZ a b +
    bchZ a b * bchT5 a b * bchZ a b * bchZ a b +
    bchT2 a b * bchZ a b * bchZ a b * bchT4 a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchT3 a b +
    bchT2 a b * bchZ a b * bchT3 a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchT4 a b * bchZ a b +
    bchT2 a b * bchT2 a b * bchZ a b * bchT3 a b +
    bchT2 a b * bchT2 a b * bchT2 a b * bchT2 a b +
    bchT2 a b * bchT2 a b * bchT3 a b * bchZ a b +
    bchT2 a b * bchT3 a b * bchZ a b * bchT2 a b +
    bchT2 a b * bchT3 a b * bchT2 a b * bchZ a b +
    bchT2 a b * bchT4 a b * bchZ a b * bchZ a b +
    bchT3 a b * bchZ a b * bchZ a b * bchT3 a b +
    bchT3 a b * bchZ a b * bchT2 a b * bchT2 a b +
    bchT3 a b * bchZ a b * bchT3 a b * bchZ a b +
    bchT3 a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchT3 a b * bchT2 a b * bchT2 a b * bchZ a b +
    bchT3 a b * bchT3 a b * bchZ a b * bchZ a b +
    bchT4 a b * bchZ a b * bchZ a b * bchT2 a b +
    bchT4 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchT4 a b * bchT2 a b * bchZ a b * bchZ a b +
    bchT5 a b * bchZ a b * bchZ a b * bchZ a b

/-- The eighth homogeneous component of `y^5`, with 35 ordered products. -/
def bchY58 {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT4 a b +
    bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchT3 a b +
    bchZ a b * bchZ a b * bchZ a b * bchT3 a b * bchT2 a b +
    bchZ a b * bchZ a b * bchZ a b * bchT4 a b * bchZ a b +
    bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchT3 a b +
    bchZ a b * bchZ a b * bchT2 a b * bchT2 a b * bchT2 a b +
    bchZ a b * bchZ a b * bchT2 a b * bchT3 a b * bchZ a b +
    bchZ a b * bchZ a b * bchT3 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchZ a b * bchT3 a b * bchT2 a b * bchZ a b +
    bchZ a b * bchZ a b * bchT4 a b * bchZ a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchT3 a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT2 a b * bchT2 a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT3 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT2 a b * bchT2 a b * bchT2 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchT3 a b * bchZ a b * bchZ a b +
    bchZ a b * bchT3 a b * bchZ a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT3 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchZ a b * bchT3 a b * bchT2 a b * bchZ a b * bchZ a b +
    bchZ a b * bchT4 a b * bchZ a b * bchZ a b * bchZ a b +
    bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchT3 a b +
    bchT2 a b * bchZ a b * bchZ a b * bchT2 a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchZ a b * bchT3 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchT2 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT3 a b * bchZ a b * bchZ a b +
    bchT2 a b * bchT2 a b * bchZ a b * bchZ a b * bchT2 a b +
    bchT2 a b * bchT2 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchT2 a b * bchT2 a b * bchT2 a b * bchZ a b * bchZ a b +
    bchT2 a b * bchT3 a b * bchZ a b * bchZ a b * bchZ a b +
    bchT3 a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b +
    bchT3 a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b +
    bchT3 a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b +
    bchT3 a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b +
    bchT4 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b

/-- The eighth homogeneous component of `y^6`, with 21 ordered products. -/
def bchY68 {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT3 a b +
    bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchT2 a b +
    bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT3 a b * bchZ a b +
    bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchT2 a b +
    bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchT2 a b * bchZ a b +
    bchZ a b * bchZ a b * bchZ a b * bchT3 a b * bchZ a b * bchZ a b +
    bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchT2 a b +
    bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchT2 a b * bchZ a b +
    bchZ a b * bchZ a b * bchT2 a b * bchT2 a b * bchZ a b * bchZ a b +
    bchZ a b * bchZ a b * bchT3 a b * bchZ a b * bchZ a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b +
    bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b +
    bchZ a b * bchT2 a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b +
    bchZ a b * bchT3 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b +
    bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b +
    bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b +
    bchT2 a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b +
    bchT2 a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b +
    bchT2 a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b +
    bchT3 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b

/-- The eighth homogeneous component of `y^7`, with 7 ordered products. -/
def bchY78 {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) : A :=
  bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b +
    bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b +
    bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b +
    bchZ a b * bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b +
    bchZ a b * bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b +
    bchZ a b * bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b +
    bchT2 a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b * bchZ a b

/-! ### Integer tables and evaluation -/

/-- Integer table of `bchW8`, at the shared coefficient scale. -/
def w8Tab : WordTable.Table (Fin 2) :=
  smul 2 (bchTTable 8) ++
    (smul (-1) (mul (bchTTable 1) (bchTTable 7)) ++
      smul (-1) (mul (bchTTable 2) (bchTTable 6)) ++
      smul (-1) (mul (bchTTable 3) (bchTTable 5)) ++
      smul (-1) (mul (bchTTable 4) (bchTTable 4)) ++
      smul (-1) (mul (bchTTable 5) (bchTTable 3)) ++
      smul (-1) (mul (bchTTable 6) (bchTTable 2)) ++
      smul (-1) (mul (bchTTable 7) (bchTTable 1)))

/-- Integer table of the eighth component of `y^3`. -/
def y38Tab : WordTable.Table (Fin 2) :=
    mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 6) ++
    mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 5) ++
    mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 4) ++
    mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 3) ++
    mul (mul (bchTTable 1) (bchTTable 5)) (bchTTable 2) ++
    mul (mul (bchTTable 1) (bchTTable 6)) (bchTTable 1) ++
    mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 5) ++
    mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 4) ++
    mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 3) ++
    mul (mul (bchTTable 2) (bchTTable 4)) (bchTTable 2) ++
    mul (mul (bchTTable 2) (bchTTable 5)) (bchTTable 1) ++
    mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 4) ++
    mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (bchTTable 3) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (bchTTable 3) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (bchTTable 4) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (bchTTable 4) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (bchTTable 4) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (bchTTable 5) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (bchTTable 5) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (bchTTable 6) (bchTTable 1)) (bchTTable 1)

/-- Integer table of the eighth component of `y^4`. -/
def y48Tab : WordTable.Table (Fin 2) :=
    mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 5) ++
    mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 4) ++
    mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 3)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 4)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 5)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 4) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 1) (bchTTable 5)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 4) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 2) (bchTTable 4)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 3) (bchTTable 3)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 4) (bchTTable 1)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (bchTTable 4) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 4) (bchTTable 2)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (bchTTable 5) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)

/-- Integer table of the eighth component of `y^5`. -/
def y58Tab : WordTable.Table (Fin 2) :=
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable 4) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable 3) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 3)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 4)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 3)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 3)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 4)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 3)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 2)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 1) (bchTTable 4)) (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable 3) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 3)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 3)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 2)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 2) (bchTTable 3)) (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 3) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (bchTTable 4) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)

/-- Integer table of the eighth component of `y^6`. -/
def y68Tab : WordTable.Table (Fin 2) :=
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 3) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    2)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    3)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable
    1)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable
    2)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 3)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable
    2)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 2)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 3)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    2)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 2)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 2)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 3)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    2)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 2)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 2)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 2)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (bchTTable 3) (bchTTable 1)) (bchTTable 1)) (bchTTable 1)) (bchTTable
    1)) (bchTTable 1)

/-- Integer table of the eighth component of `y^7`. -/
def y78Tab : WordTable.Table (Fin 2) :=
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1))
    (bchTTable 1)) (bchTTable 1)) (bchTTable 2) ++
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1))
    (bchTTable 1)) (bchTTable 2)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 1))
    (bchTTable 2)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 1)) (bchTTable 2))
    (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 1)) (bchTTable 2)) (bchTTable 1))
    (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (mul (bchTTable 1) (bchTTable 2)) (bchTTable 1)) (bchTTable 1))
    (bchTTable 1)) (bchTTable 1)) (bchTTable 1) ++
    mul (mul (mul (mul (mul (mul (bchTTable 2) (bchTTable 1)) (bchTTable 1)) (bchTTable 1))
    (bchTTable 1)) (bchTTable 1)) (bchTTable 1)

/-- Integer table of the eighth power of the linear component. -/
def z8Tab : WordTable.Table (Fin 2) := pow (bchTTable 1) 8

/-- The `W8` table evaluates to its ring expression. -/
lemma eval_w8Tab {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] w8Tab = bchW8 a b := by
  simp only [w8Tab, bchW8, bchZ, eval_append, eval_smul, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three,
    eval_bchTTable_four, eval_bchTTable_five, eval_bchTTable_six,
    eval_bchTTable_seven, eval_bchTTable_eight, bchZ]
  norm_cast
  norm_num
  abel

/-- The table for the eighth component of `y^3` evaluates to its ordered product sum. -/
lemma eval_y38Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] y38Tab = bchY38 a b := by
  simp only [y38Tab, bchY38, eval_append, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, eval_bchTTable_four,
    eval_bchTTable_five, eval_bchTTable_six]

/-- The table for the eighth component of `y^4` evaluates to its ordered product sum. -/
lemma eval_y48Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] y48Tab = bchY48 a b := by
  simp only [y48Tab, bchY48, eval_append, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, eval_bchTTable_four,
    eval_bchTTable_five]

/-- The table for the eighth component of `y^5` evaluates to its ordered product sum. -/
lemma eval_y58Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] y58Tab = bchY58 a b := by
  simp only [y58Tab, bchY58, eval_append, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three, eval_bchTTable_four]

/-- The table for the eighth component of `y^6` evaluates to its ordered product sum. -/
lemma eval_y68Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] y68Tab = bchY68 a b := by
  simp only [y68Tab, bchY68, eval_append, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two, eval_bchTTable_three]

/-- The table for the eighth component of `y^7` evaluates to its ordered product sum. -/
lemma eval_y78Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] y78Tab = bchY78 a b := by
  simp only [y78Tab, bchY78, eval_append, eval_mul]
  simp only [eval_bchTTable_one, eval_bchTTable_two]

/-- The table of `z⁸` evaluates to the eighth power of `z`. -/
lemma eval_z8Tab {A : Type*} [Semiring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] z8Tab = bchZ a b ^ 8 := by
  rw [z8Tab, eval_pow, eval_bchTTable_one]

/-- The eighth logarithm component minus the eighth BCH term, multiplied by `840`. -/
def dynkin8Tab : WordTable.Table (Fin 2) :=
  smul 420 w8Tab ++ smul 280 y38Tab ++ smul (-210) y48Tab ++
    smul 168 y58Tab ++ smul (-140) y68Tab ++ smul 120 y78Tab ++
    smul (-105) z8Tab ++ smul (-840) bchOcticTermTable

/-- The certificate evaluates to `840` times the desired cancellation. -/
theorem eval_dynkin8Tab {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] dynkin8Tab = (840 : ℚ) •
      ((2 : ℚ)⁻¹ • bchW8 a b + (3 : ℚ)⁻¹ • bchY38 a b -
        (4 : ℚ)⁻¹ • bchY48 a b + (5 : ℚ)⁻¹ • bchY58 a b -
        (6 : ℚ)⁻¹ • bchY68 a b + (7 : ℚ)⁻¹ • bchY78 a b -
        (8 : ℚ)⁻¹ • bchZ a b ^ 8 - bchOcticTerm a b) := by
  simp only [dynkin8Tab, eval_append, eval_smul, eval_w8Tab, eval_y38Tab,
    eval_y48Tab, eval_y58Tab, eval_y68Tab, eval_y78Tab, eval_z8Tab,
    bchOcticTerm]
  module

/-! ### Prefix-tree certificate and the identity -/

set_option maxRecDepth 20000 in
/-- Every coefficient of the eighth-degree comparison vanishes.
The local recursion limit accommodates the raw list's more than 11000 rows. -/
theorem dynkin8Tab_isZero :
    BinaryWordTable.isZero (BinaryWordTable.collect dynkin8Tab) = true := by
  decide +kernel

/-- The eighth-degree certificate evaluates to zero in every rational algebra. -/
theorem eval_dynkin8Tab_eq_zero {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    eval coefficientScale ![a, b] dynkin8Tab = 0 :=
  BinaryWordTable.eval_table_eq_zero _ _ _ dynkin8Tab_isZero

/-- The eighth BCH term is the eighth homogeneous component of the logarithm series.
This is the pure degree-eight identity, with no analytic assumptions. -/
theorem bchOcticTerm_eq {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    bchOcticTerm a b =
      (2 : ℚ)⁻¹ • bchW8 a b + (3 : ℚ)⁻¹ • bchY38 a b -
        (4 : ℚ)⁻¹ • bchY48 a b + (5 : ℚ)⁻¹ • bchY58 a b -
        (6 : ℚ)⁻¹ • bchY68 a b + (7 : ℚ)⁻¹ • bchY78 a b -
        (8 : ℚ)⁻¹ • bchZ a b ^ 8 := by
  have h := eval_dynkin8Tab (A := A) a b
  rw [eval_dynkin8Tab_eq_zero] at h
  have hzero := (smul_eq_zero.mp h.symm).resolve_left (by norm_num)
  exact (sub_eq_zero.mp hzero).symm

end FQFP.BCH
