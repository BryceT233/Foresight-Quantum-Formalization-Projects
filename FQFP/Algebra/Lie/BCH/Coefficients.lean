/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SymmetricRecurrence
public import FQFP.Algebra.Lie.Hom

/-!
# BCH Lie coefficients from the symmetric homogeneous recursion

The ordinary coefficients are obtained by applying `exp(ad_x / 2)` to the
symmetric series. The definition and its naturality need only a rational Lie
algebra. Compatibility with the associative logarithm is proved separately.
-/

@[expose] public noncomputable section

namespace FQFP

open Finset

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The ordinary BCH homogeneous coefficient obtained by conjugating the symmetric series. -/
def bchLieCoeff (x y : L) (n : ℕ) : L :=
  ∑ j ∈ range (n + 1), ((2 : ℚ) ^ j * (Nat.factorial j : ℚ))⁻¹ •
    (LieAlgebra.ad ℚ L x ^ j) (symmetricBchLieCoeff x y (n - j))

/-- Lie homomorphisms preserve every ordinary BCH coefficient. -/
theorem map_bchLieCoeff {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (f : L →ₗ⁅ℚ⁆ M) (x y : L) (n : ℕ) :
    f (bchLieCoeff x y n) = bchLieCoeff (f x) (f y) n := by
  simp only [bchLieCoeff, map_sum, map_smul, LieHom.map_ad_pow_apply, map_symmetricBchLieCoeff]

end FQFP
