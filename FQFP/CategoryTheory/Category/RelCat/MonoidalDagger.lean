/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Category.RelCat.Dagger
public import FQFP.CategoryTheory.Category.RelCat.Monoidal
public import FQFP.CategoryTheory.Monoidal.Dagger.Basic

/-!
# Monoidal dagger structure on relations

Relation reversal respects the cartesian tensor product.

## Main results

* `RelCat.monoidalDaggerCategory`: compatibility with tensors and structural isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.RelCat

set_option backward.isDefEq.respectTransparency.types false in
/-- The cartesian tensor product is compatible with relation reversal. -/
instance monoidalDaggerCategory : MonoidalDaggerCategory RelCat.{u} where
  dagger_tensor f g := by ext; simp
  isUnitary_associator X Y Z := isUnitary_graphFunctor_mapIso (Equiv.prodAssoc X Y Z).toIso
  isUnitary_leftUnitor X := isUnitary_graphFunctor_mapIso (Equiv.punitProd X).toIso
  isUnitary_rightUnitor X := isUnitary_graphFunctor_mapIso (Equiv.prodPUnit X).toIso

end CategoryTheory.RelCat
