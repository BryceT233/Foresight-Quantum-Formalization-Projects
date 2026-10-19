/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerCategory
public import FQFP.CQM.RelCat.Monoidal

/-!
# The dagger structure on the category of relations

The dagger on `RelCat` reverses the underlying relation. It is compatible with the cartesian
tensor product of `FQFP.CQM.RelCat.Monoidal`, making `RelCat` a monoidal dagger category.

## Main definitions

* `RelCat.instDaggerCategoryRelCat`: the dagger structure on `RelCat`.
* `RelCat.monoidalDaggerCategory`: `RelCat` is a monoidal dagger category.

## Main results

* `RelCat.rel_dagger`, `RelCat.mem_dagger`: the dagger on underlying relations.
* `RelCat.isUnitary_graphFunctor_mapIso`: the graph of a bijection is a unitary morphism.
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

set_option backward.isDefEq.respectTransparency.types false in
/-- The cartesian tensor product is compatible with relation reversal. -/
instance monoidalDaggerCategory : MonoidalDaggerCategory RelCat.{u} where
  dagger_tensor f g := by ext; simp
  isUnitary_associator X Y Z := isUnitary_graphFunctor_mapIso (Equiv.prodAssoc X Y Z).toIso
  isUnitary_leftUnitor X := isUnitary_graphFunctor_mapIso (Equiv.punitProd X).toIso
  isUnitary_rightUnitor X := isUnitary_graphFunctor_mapIso (Equiv.prodPUnit X).toIso

end CategoryTheory.RelCat
