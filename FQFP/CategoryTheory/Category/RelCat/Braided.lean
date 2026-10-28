/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Monoidal.Dagger.Braided
public import FQFP.CategoryTheory.Category.RelCat.MonoidalDagger
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The braided and symmetric structures on the category of relations

The braiding of `RelCat` swaps the two coordinates, and since it is the graph of an involution
it is its own inverse. This makes `RelCat` a symmetric monoidal dagger category.

## Main definitions

* `RelCat.instBraidedCategoryRelCat`, `RelCat.symmetricCategory`.
* `RelCat.symmetricMonoidalDaggerCategory`: the braiding is unitary (Definition 2.37).

## Main results

* `RelCat.rel_braiding_hom`, `RelCat.rel_braiding_inv`: the braiding on underlying relations.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

/-! ### Braided and symmetric structures -/

set_option backward.isDefEq.respectTransparency.types false in
/-- The braiding on `RelCat` is the graph of the coordinate-swap equivalence. -/
instance instBraidedCategoryRelCat : BraidedCategory RelCat.{u} where
  braiding X Y := graphFunctor.mapIso (Equiv.prodComm X Y).toIso
  braiding_naturality_left f Z := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff, and_comm]
  braiding_naturality_right X {Y Z} f := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]
  hexagon_forward X Y Z := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]
  hexagon_reverse X Y Z := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]

@[simp] lemma rel_braiding_hom : (β_ X Y).hom.rel = {p | (p.1.2, p.1.1) = p.2} := rfl

@[simp] lemma rel_braiding_inv : (β_ X Y).inv.rel = {p | (p.1.2, p.1.1) = p.2} := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Swapping coordinates twice gives the identity relation. -/
instance symmetricCategory : SymmetricCategory RelCat.{u} where
  symmetry X Y := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]

/-- The braiding of `RelCat` is unitary: it is the graph of the coordinate-swap equivalence,
which is its own converse. This is Definition 2.37 for the category of relations. -/
instance symmetricMonoidalDaggerCategory : SymmetricMonoidalDaggerCategory RelCat.{u} where
  isUnitary_braiding X Y := isUnitary_graphFunctor_mapIso (Equiv.prodComm X Y).toIso

end CategoryTheory.RelCat
