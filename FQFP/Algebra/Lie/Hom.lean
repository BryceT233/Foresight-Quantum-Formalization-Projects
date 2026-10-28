/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Lie homomorphisms and powers of the adjoint

Lie homomorphisms preserve iterated adjoint actions over any commutative ring.
No associative realization or rational scalar structure is required.
-/

@[expose] public section

namespace LieHom

/-- A Lie homomorphism intertwines every power of the adjoint action. -/
lemma map_ad_pow_apply {R L M : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) (x z : L) (n : ℕ) :
    f ((LieAlgebra.ad R L x ^ n) z) = (LieAlgebra.ad R M (f x) ^ n) (f z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      change f ⁅x, (LieAlgebra.ad R L x ^ n) z⁆ =
        ⁅f x, (LieAlgebra.ad R M (f x) ^ n) (f z)⁆
      rw [LieHom.map_lie, ih]

end LieHom
