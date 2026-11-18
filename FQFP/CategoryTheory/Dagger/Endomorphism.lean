/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import Mathlib.Algebra.Star.Unitary

/-!
# Endomorphisms in a dagger category

The dagger gives the endomorphism monoid its star. Its unitary elements are precisely
the endomorphisms whose underlying arrows are unitary.
-/

@[expose] public section

namespace CategoryTheory.End

open DaggerCategory

variable {C : Type*} [Category* C] [DaggerCategory C] {X : C}

instance instStarMulOfDaggerCategory : StarMul (End X) where
  star A := .of A.asHom†
  star_involutive A := End.ext (involutive_dagger A.asHom)
  star_mul A B := End.ext (dagger_comp B.asHom A.asHom)

/-- The underlying arrow of the star is the dagger of the underlying arrow. -/
@[simp] theorem star_asHom (A : End X) : (star A).asHom = A.asHom† := rfl

/-- Unitary elements of the endomorphism monoid correspond to unitary arrows. -/
theorem mem_unitary_iff (A : End X) : A ∈ unitary (End X) ↔ IsUnitary A.asHom := by
  rw [Unitary.mem_iff, isUnitary_iff]
  simp only [End.ext_iff, mul_asHom, star_asHom, one_asHom]

instance (U : unitary (End X)) : IsUnitary U.val.asHom :=
  (mem_unitary_iff U.val).mp U.property

end CategoryTheory.End
