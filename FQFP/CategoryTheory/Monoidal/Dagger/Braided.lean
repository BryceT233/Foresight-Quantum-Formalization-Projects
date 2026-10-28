/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braided monoidal dagger categories

The braiding is unitary with respect to the given dagger.

## Main definitions

* `BraidedMonoidalDaggerCategory`: a monoidal dagger category with unitary braiding.
* `SymmetricMonoidalDaggerCategory`: its symmetric specialization.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

open DaggerCategory

universe u v

/-- A braided monoidal dagger category has a unitary braiding on the monoidal structure
inherited from its monoidal dagger category, as in Definition 2.37. -/
class BraidedMonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    MonoidalDaggerCategory C, BraidedCategory C where
  /-- Every component of the braiding is unitary. -/
  isUnitary_braiding (X Y : C) : IsUnitary (β_ X Y).hom

attribute [instance] BraidedMonoidalDaggerCategory.isUnitary_braiding

/-- A symmetric monoidal dagger category has a unitary symmetric braiding, as in
Definition 2.37. -/
class SymmetricMonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    BraidedMonoidalDaggerCategory C, SymmetricCategory C

end CategoryTheory
