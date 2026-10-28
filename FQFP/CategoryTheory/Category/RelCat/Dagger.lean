/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import Mathlib.CategoryTheory.Category.RelCat
public import FQFP.Basic.Rel

/-!
# The dagger on relations

The dagger reverses relations. Its basic morphism API is independent of tensor products.

## Main results

* `RelCat.instDaggerCategoryRelCat`: reversal as a dagger.
* `RelCat.rel_dagger`, `RelCat.mem_dagger`: the underlying relation.
* `RelCat.isUnitary_graphFunctor_mapIso`: bijections have unitary graphs.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

/-! ### Dagger structure -/

/-- The dagger on `RelCat` reverses the underlying relation. -/
instance : DaggerCategory RelCat.{u} where
  dagger f := .ofRel (SetRel.inv f.rel)
  dagger_comp f g := Hom.ext _ _ (SetRel.inv_comp f.rel g.rel)
  dagger_id _ := Hom.ext _ _ SetRel.inv_id
  involutive_dagger _ := Hom.ext _ _ SetRel.inv_inv

@[simp] lemma rel_dagger (f : X ⟶ Y) : f†.rel = f.rel.inv := rfl

lemma mem_dagger {X Y : RelCat.{u}} (f : X ⟶ Y) (x : X) (y : Y) :
    (y, x) ∈ f†.rel ↔ (x, y) ∈ f.rel := Iff.rfl

/-- The graph of a bijection is a unitary morphism in `RelCat`. -/
theorem isUnitary_graphFunctor_mapIso {X Y : Type u} (e : X ≅ Y) :
    DaggerCategory.IsUnitary (graphFunctor.mapIso e).hom :=
  (DaggerCategory.isUnitary_hom_iff_dagger_hom_eq_inv (graphFunctor.mapIso e)).mpr <| by
    apply Hom.ext
    exact (Equiv.graph_inv e.toEquiv).symm

end CategoryTheory.RelCat
