/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.Algebra.Lie.Hom
import FQFP.Algebra.Lie.IteratedCommutator
import Mathlib.Data.Fin.VecNotation

/-!
# Adjoint naturality and sequence-order regressions

Run with `lake env lean FQFPTest/LieAdjoint.lean` after building `FQFP`.
-/

-- The homomorphism API works over an arbitrary commutative ring and abstract Lie algebras.
example {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing M] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) (x z : L) :
    f ((LieAlgebra.ad R L x ^ 2) z) = ⁅f x, ⁅f x, f z⁆⁆ := by
  rw [LieHom.map_ad_pow_apply]
  rfl

open TrotterError

section Sequence

variable {A : Type*} [Ring A] [Algebra ℝ A]

attribute [local instance] LieRing.ofAssociativeRing

-- No layers means the identity map.
example (b : A) : adSequenceLinear (Fin.elim0 : Fin 0 → A) Fin.elim0 b = b := rfl

-- A zero-multiplicity outer layer does not move or alter the inner bracket.
example (x y b : A) : adSequenceLinear ![x, y] ![1, 0] b = ⁅x, b⁆ := by
  simp [adSequenceLinear, adPow]

-- The last layer is outermost; reversing this order changes the stated expression.
example (x y b : A) : adSequenceLinear ![x, y] ![1, 1] b = ⁅y, ⁅x, b⁆⁆ := by
  simp [adSequenceLinear, adPow]

-- Both zero multiplicities leave the seed unchanged.
example (x y b : A) : adSequenceLinear ![x, y] ![0, 0] b = b := by
  simp [adSequenceLinear, adPow]

-- Clients get additivity from the linear-map view without a new sequence induction.
example {s : ℕ} (ops : Fin s → A) (q : Fin s → ℕ) (x y : A) :
    adSequence ops q (x + y) = adSequence ops q x + adSequence ops q y := by
  simpa only [adSequenceLinear_apply] using (adSequenceLinear ops q).map_add x y

end Sequence
