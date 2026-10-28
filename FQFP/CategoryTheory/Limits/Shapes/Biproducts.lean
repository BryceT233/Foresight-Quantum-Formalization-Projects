/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Maps of explicit bilimit bicones

Lift, descend, form matrices and compare explicit bilimit witnesses without a dagger.

## Main results

* `Limits.Bicone.lift`, `Limits.Bicone.desc`: universal factorizations.
* `Limits.Bicone.matrix`, `Limits.Bicone.entry`: matrix calculus.
* `Limits.Bicone.iso`, `Limits.BinaryBicone.iso`: canonical comparisons.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.Limits.Bicone

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type*} {F : ι → C} (b : Bicone F) (hb : b.IsBilimit)

/-- The factorization into an explicit bilimit bicone. -/
def lift {X : C} (x : ∀ i, X ⟶ F i) : X ⟶ b.pt :=
  hb.isLimit.lift (Fan.mk X x)

/-- The factorization out of an explicit bilimit bicone. -/
def desc {X : C} (x : ∀ i, F i ⟶ X) : b.pt ⟶ X :=
  hb.isColimit.desc (Cofan.mk X x)

/-- A factorization into an explicit bicone recovers each component. -/
@[reassoc (attr := simp)]
lemma lift_π {X : C} (x : ∀ i, X ⟶ F i) (i : ι) :
    b.lift hb x ≫ b.π i = x i := hb.isLimit.fac _ ⟨i⟩

/-- A factorization out of an explicit bicone recovers each component. -/
@[reassoc (attr := simp)]
lemma ι_desc {X : C} (x : ∀ i, F i ⟶ X) (i : ι) :
    b.ι i ≫ b.desc hb x = x i := hb.isColimit.fac _ ⟨i⟩

section Matrix

variable {κ : Type*} {G : κ → C} (c : Bicone G) (hc : c.IsBilimit)

/-- The `(i, j)` entry of a map between two explicit bicones. -/
def entry (x : b.pt ⟶ c.pt) (i : ι) (j : κ) : F i ⟶ G j :=
  b.ι i ≫ x ≫ c.π j

/-- Assemble a matrix into a map between two explicit bilimit bicones. -/
def matrix (m : ∀ i j, F i ⟶ G j) : b.pt ⟶ c.pt :=
  b.desc hb (fun i ↦ c.lift hc (m i))

/-- The entries of an assembled matrix are its components. -/
@[simp]
lemma entry_matrix (m : ∀ i j, F i ⟶ G j) (i : ι) (j : κ) :
    b.entry c (b.matrix hb c hc m) i j = m i j := by
  simp [entry, matrix]

end Matrix

variable (c : Bicone F) (hc : c.IsBilimit)

/-- The canonical isomorphism between two explicit bilimit bicones. -/
def iso : b.pt ≅ c.pt where
  hom := b.desc hb c.ι
  inv := c.desc hc b.ι
  hom_inv_id := by
    apply hb.isColimit.hom_ext
    intro i
    change b.ι i.as ≫ b.desc hb c.ι ≫ c.desc hc b.ι = b.ι i.as ≫ 𝟙 b.pt
    simp only [← Category.assoc, ι_desc, Category.comp_id]
  inv_hom_id := by
    apply hc.isColimit.hom_ext
    intro i
    change c.ι i.as ≫ c.desc hc b.ι ≫ b.desc hb c.ι = c.ι i.as ≫ 𝟙 c.pt
    simp only [← Category.assoc, ι_desc, Category.comp_id]

/-- The comparison isomorphism preserves the projections. -/
lemma iso_hom_π (i : ι) : (b.iso hb c hc).hom ≫ c.π i = b.π i := by
  apply hb.isColimit.hom_ext
  intro j
  change b.ι j.as ≫ (b.iso hb c hc).hom ≫ c.π i = b.ι j.as ≫ b.π i
  rw [← Category.assoc, show (b.iso hb c hc).hom = b.desc hb c.ι from rfl, ι_desc]
  classical
  simp only [c.ι_π, b.ι_π]

end CategoryTheory.Limits.Bicone

namespace CategoryTheory.Limits.BinaryBicone

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {X Y : C} (b : BinaryBicone X Y) (hb : b.IsBilimit)

/-- Factor a pair of maps into an explicit binary bilimit bicone. -/
def lift {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ b.pt :=
  BinaryFan.IsLimit.lift hb.isLimit f g

/-- Factor a pair of maps out of an explicit binary bilimit bicone. -/
def desc {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : b.pt ⟶ Z :=
  BinaryCofan.IsColimit.desc hb.isColimit f g

/-- The first component of a binary bilimit lift. -/
@[reassoc (attr := simp)]
lemma lift_fst {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : b.lift hb f g ≫ b.fst = f :=
  hb.isLimit.fac _ ⟨WalkingPair.left⟩

/-- The second component of a binary bilimit lift. -/
@[reassoc (attr := simp)]
lemma lift_snd {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : b.lift hb f g ≫ b.snd = g :=
  hb.isLimit.fac _ ⟨WalkingPair.right⟩

/-- The first component of a binary bilimit descent. -/
@[reassoc (attr := simp)]
lemma inl_desc {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : b.inl ≫ b.desc hb f g = f :=
  hb.isColimit.fac _ ⟨WalkingPair.left⟩

/-- The second component of a binary bilimit descent. -/
@[reassoc (attr := simp)]
lemma inr_desc {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : b.inr ≫ b.desc hb f g = g :=
  hb.isColimit.fac _ ⟨WalkingPair.right⟩

variable (c : BinaryBicone X Y) (hc : c.IsBilimit)

/-- The canonical comparison of two binary bilimit bicones. -/
def iso : b.pt ≅ c.pt :=
  b.toBicone.iso ((b.toBiconeIsBilimit).symm hb) c.toBicone
    ((c.toBiconeIsBilimit).symm hc)

end CategoryTheory.Limits.BinaryBicone
