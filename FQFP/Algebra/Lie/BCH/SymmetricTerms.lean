/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Lie.BCH.SymmetricQuintic

/-!
# Low-degree symmetric BCH Lie polynomials

This module defines the cubic Lie polynomial and re-exports the quintic polynomial from
`FQFP.Algebra.Lie.BCH.SymmetricQuintic`.

## Main definitions

* `FQFP.symmetricBchCubicLieTerm` gives the cubic Lie coefficient of the symmetric exponential
  product.
-/

@[expose] public section

namespace FQFP

/-- The cubic Hall expression for the symmetric BCH series in a rational Lie algebra.
This is the Strang coefficient `C₃` in
`log (exp (h x / 2) * exp (h y) * exp (h x / 2)) = h (x + y) + h³ C₃ + h⁵ D₅ + O(h⁷)`,
with the Hall convention `E₃ = ⁅y, x⁆`. -/
def symmetricBchCubicLieTerm {L : Type*} [LieRing L] [LieAlgebra ℚ L] (x y : L) : L :=
  (-1 / 24 : ℚ) • ⁅⁅y, x⁆, x⁆ + (-1 / 12 : ℚ) • ⁅⁅y, x⁆, y⁆

end FQFP
