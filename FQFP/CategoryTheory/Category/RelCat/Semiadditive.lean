/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Category.RelCat
public import FQFP.CategoryTheory.Semiadditive.Basic
public import FQFP.Basic.Rel

/-!
# The superposition rule on the category of relations

The morphisms of `RelCat` between two fixed objects form a commutative monoid under union of
relations, with the empty relation as unit. This is the superposition rule of the source notes
in this model, and it makes `RelCat` semiadditive. There are no additive inverses: `RelCat` is
not preadditive.

## Main definitions

* `RelCat.homZero`, `RelCat.homAdd`: the empty relation as zero, union of relations as
  addition.
* `RelCat.semiadditive`: `RelCat` is semiadditive, with union as addition.

## Main results

* `RelCat.rel_zero`, `RelCat.rel_add`: the underlying relation of a zero morphism and of a sum.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

/-! ### Superposition of relations -/

/-- The zero morphism in `RelCat` is the empty relation. -/
instance homZero : Zero (X ⟶ Y) := ⟨.ofRel ∅⟩

/-- Superposition in `RelCat` is union of relations. -/
instance homAdd : Add (X ⟶ Y) := ⟨fun f g ↦ .ofRel (f.rel ∪ g.rel)⟩

/-- Morphisms of `RelCat` form a commutative monoid under union. -/
instance homAddCommMonoid : AddCommMonoid (X ⟶ Y) where
  add_assoc f g h := Hom.ext _ _ (Set.union_assoc f.rel g.rel h.rel)
  zero_add f := Hom.ext _ _ (Set.empty_union f.rel)
  add_zero f := Hom.ext _ _ (Set.union_empty f.rel)
  add_comm f g := Hom.ext _ _ (Set.union_comm f.rel g.rel)
  nsmul := nsmulRec

/-- The relation underlying a zero morphism is empty. -/
@[simp] lemma rel_zero : (0 : X ⟶ Y).rel = ∅ := rfl

/-- The relation underlying a sum is the union of the underlying relations. -/
@[simp] lemma rel_add (f g : X ⟶ Y) : (f + g).rel = f.rel ∪ g.rel := rfl

/-- Union is a superposition rule on `RelCat`, with no additive-inverse assumption. -/
instance semiadditive : Semiadditive RelCat.{u} where
  add_comp _ _ _ f g h := Hom.ext _ _ (SetRel.union_comp f.rel g.rel h.rel)
  comp_add _ _ _ f g h := Hom.ext _ _ (SetRel.comp_union f.rel g.rel h.rel)
  zero_comp _ _ _ f := Hom.ext _ _ (SetRel.empty_comp f.rel)
  comp_zero _ _ _ f := Hom.ext _ _ (SetRel.comp_empty f.rel)

end CategoryTheory.RelCat
