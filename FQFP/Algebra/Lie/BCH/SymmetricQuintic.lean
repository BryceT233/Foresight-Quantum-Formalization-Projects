/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# The quintic symmetric BCH Lie polynomial

The six degree-five brackets in the classical Hall presentation define a polynomial in any
rational Lie algebra. The bracket orientation starts with `⁅y, x⁆`. Its coefficients are those
of the symmetric product `exp (x / 2) * exp y * exp (x / 2)` in Table IV of Casas and Murua,
*An efficient algorithm for computing the Baker–Campbell–Hausdorff series and some of its
applications*, J. Math. Phys. 50, 033513 (2009).

## Main definitions

* `FQFP.symmetricBchQuinticLieTerm`: the six-bracket quintic polynomial.

## Main results

* `FQFP.map_symmetricBchQuinticLieTerm`: compatibility with Lie homomorphisms.
* `FQFP.symmetricBchQuinticLieTerm_smul`: simultaneous degree-five homogeneity.
-/

@[expose] public section

namespace FQFP

/-- The degree-five symmetric BCH Lie polynomial, with common denominator `5760`.
This is the Strang coefficient `D₅` in
`log (exp (h x / 2) * exp (h y) * exp (h x / 2)) = h (x + y) + h³ C₃ + h⁵ D₅ + O(h⁷)`.
The six brackets correspond to classical Hall indices `9` through `14`, with
`E₃ = ⁅y, x⁆` and the recursive rule `E_i = [E_{i'}, E_{i''}]`. -/
def symmetricBchQuinticLieTerm {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (x y : L) : L :=
  let c := ⁅y, x⁆
  let cx := ⁅c, x⁆
  let cy := ⁅c, y⁆
  let cxx := ⁅cx, x⁆
  let cxy := ⁅cx, y⁆
  let cyy := ⁅cy, y⁆
  (5760 : ℚ)⁻¹ •
    (7 • ⁅cxx, x⁆ + 28 • ⁅cxx, y⁆ + 32 • ⁅cxy, y⁆ +
      8 • ⁅cyy, y⁆ + 12 • ⁅cx, c⁆ - 16 • ⁅cy, c⁆)

/-- Lie homomorphisms preserve the quintic symmetric BCH polynomial. -/
theorem map_symmetricBchQuinticLieTerm
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (f : L →ₗ⁅ℚ⁆ M) (x y : L) :
    f (symmetricBchQuinticLieTerm x y) =
      symmetricBchQuinticLieTerm (f x) (f y) := by
  simp only [symmetricBchQuinticLieTerm, map_smul, map_sub, map_add, map_nsmul,
    LieHom.map_lie]

/-- Simultaneous rational scaling has degree five. -/
theorem symmetricBchQuinticLieTerm_smul
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] (x y : L) (c : ℚ) :
    symmetricBchQuinticLieTerm (c • x) (c • y) =
      c ^ 5 • symmetricBchQuinticLieTerm x y := by
  have hbr (u v : L) (m n : ℕ) :
      ⁅c ^ m • u, c ^ n • v⁆ = c ^ (m + n) • ⁅u, v⁆ := by
    rw [smul_lie, lie_smul, smul_smul, pow_add]
  rw [show c • x = c ^ 1 • x by rw [pow_one], show c • y = c ^ 1 • y by rw [pow_one]]
  simp only [symmetricBchQuinticLieTerm, hbr, Nat.reduceAdd]
  rw [smul_comm (c ^ 5) ((5760 : ℚ)⁻¹)]
  congr 1
  simp only [smul_add, smul_sub, smul_comm (c ^ 5)]

end FQFP
