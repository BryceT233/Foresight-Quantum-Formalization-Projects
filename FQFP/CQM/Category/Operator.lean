/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Dagger.Endomorphism
public import FQFP.CategoryTheory.Monoidal.State

/-!
# Operators and outer products

An operator is an endomorphism of a system. In a monoidal category with a dagger,
two states determine the outer product obtained by composing a bra with a ket.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace CQM

/-- An operator on a system in a category. -/
abbrev Operator {C : Type*} [Category* C] (H : C) := End H

namespace Operator

variable {C : Type*} [Category* C] [MonoidalCategory C] [DaggerCategory C] {H : C}

/-- The outer product of states `v` and `w`, with underlying arrow `w† ≫ v`. -/
def outer (v w : State H) : Operator H := .of (w† ≫ v)

@[simp] theorem outer_asHom (v w : State H) : (outer v w).asHom = w† ≫ v := rfl

/-- Taking the adjoint of an outer product exchanges its two states. -/
@[simp] theorem star_outer (v w : State H) : star (outer v w) = outer w v := by
  apply End.ext
  simp

/-- The outer square of any state is positive. -/
instance (v : State H) : IsPositive (outer v v).asHom := IsPositive.dagger_comp v

end Operator

end CQM
