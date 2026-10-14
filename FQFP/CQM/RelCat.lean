/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerCategory
public import FQFP.CQM.Category.Semiadditive
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The symmetric monoidal dagger structure on the category of relations

This file equips `RelCat`, the category of types with binary relations as morphisms,
with a symmetric monoidal structure and a compatible dagger. The tensor product is the cartesian
product of types, the tensor unit is `PUnit`, the braiding swaps coordinates, and the dagger
reverses relations.

It also characterizes the dagger-derived morphism classes (`IsUnitary`, `IsIsometry`, `IsProj`,
`IsPositive`) in terms of the underlying relations.

## Main definitions

* The monoidal, braided, symmetric, and monoidal dagger category structures on `RelCat`.
* The semiadditive structure on `RelCat`, with union as addition and the empty relation as zero.
* Membership lemmas for identities, composition, tensor products, whiskering, the structural
  isomorphisms, and the dagger.

## Main results

* `isUnitary_iff_isIso`: unitary morphisms are exactly the isomorphisms.
* `isIsometry_iff_leftTotal_leftUnique`: isometries are exactly left-total, left-unique relations.
* `isProj_iff_symm_trans`: projections are exactly partial equivalence relations.
* `isPositive_iff_isSymm_reflOnDom`: positive morphisms are exactly symmetric relations that are
  reflexive on their domain.

-/

@[expose] public section

universe u

/-! ### Relations underlying dagger morphism properties -/

/-- Membership in a function graph, expressed for an arbitrary product element. -/
@[simp] theorem Function.mem_graph_iff {A B : Type*} (f : A → B) (p : A × B) :
    p ∈ f.graph ↔ f p.1 = p.2 := Iff.rfl

namespace SetRel

variable {A B : Type*}

/-- Relational composition distributes over union in its first variable. -/
lemma union_comp {C : Type*} (R S : SetRel A B) (T : SetRel B C) :
    (R ∪ S).comp T = R.comp T ∪ S.comp T := by grind

/-- Relational composition distributes over union in its second variable. -/
lemma comp_union {C : Type*} (R : SetRel A B) (S T : SetRel B C) :
    R.comp (S ∪ T) = R.comp S ∪ R.comp T := by grind

/-- Membership in an inverse relation, expressed for an arbitrary product element. -/
@[simp] theorem mem_inv_iff (R : SetRel A B) (p : B × A) :
    p ∈ R.inv ↔ (p.2, p.1) ∈ R := Iff.rfl

/-- Composing a relation with its inverse gives a symmetric relation. -/
instance comp_inv_isSymm (R : SetRel A B) : (R.comp R.inv).IsSymm where
  symm _ _ := by grind

/-- A relation composed with its inverse is the identity exactly when it is left-total
and left-unique. -/
theorem comp_inv_eq_id_iff (R : SetRel A B) : R.comp R.inv = SetRel.id ↔
    Relator.LeftTotal (fun a b ↦ (a, b) ∈ R) ∧ Relator.LeftUnique (fun a b ↦ (a, b) ∈ R) := by
  constructor
  · intro h
    constructor
    · intro a
      have haa : (a, a) ∈ R.comp R.inv := h.symm ▸ rfl
      obtain ⟨b, hab, _⟩ := haa
      exact ⟨b, hab⟩
    · intro a a' b hab ha'b
      exact mem_id.1 (h ▸ (show (a, a') ∈ R.comp R.inv from ⟨b, hab, ha'b⟩))
  · rintro ⟨htotal, hunique⟩
    ext ⟨a, a'⟩
    simp only [mem_comp, mem_inv, mem_id]
    constructor
    · rintro ⟨b, hab, ha'b⟩
      exact hunique hab ha'b
    · rintro rfl
      obtain ⟨b, hab⟩ := htotal a
      exact ⟨b, hab, hab⟩

/-- A partial equivalence relation is idempotent under relational composition. -/
theorem comp_eq_self_of_isSymm_of_isTrans (R : SetRel A A) [R.IsSymm] [R.IsTrans] :
    R.comp R = R := Set.Subset.antisymm comp_subset_self fun ⟨a, _⟩ hab ↦
  ⟨a, R.trans hab (R.symm hab), hab⟩

end SetRel

open CategoryTheory
open scoped MonoidalCategory

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

/-! ### Monoidal structure and structural membership lemmas -/

/-- The monoidal category structure on `RelCat`: the tensor product is the cartesian
product of types, and the tensor unit is `PUnit`. -/
instance instMonoidalCategoryStructRelCat : MonoidalCategoryStruct RelCat.{u} where
  tensorObj X Y := X × Y
  whiskerLeft _ _ _ f := .ofRel {((x, y₁), (x', y₂)) | x = x' ∧ (y₁, y₂) ∈ f.rel}
  whiskerRight f _ := .ofRel {((x, y), (x', y')) | (x, x') ∈ f.rel ∧ y = y'}
  tensorHom f g := .ofRel {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel}
  tensorUnit := PUnit
  associator X Y Z := graphFunctor.mapIso (Equiv.prodAssoc X Y Z).toIso
  leftUnitor X := graphFunctor.mapIso (Equiv.punitProd X).toIso
  rightUnitor X := graphFunctor.mapIso (Equiv.prodPUnit X).toIso

@[simp] lemma tensorObj_def (X Y : RelCat.{u}) : (X ⊗ Y : RelCat.{u}) = (X × Y) := rfl

@[simp] lemma tensorUnit_def : (𝟙_ RelCat.{u} : RelCat.{u}) = PUnit.{u + 1} := rfl

@[simp] lemma rel_tensorHom {X₁ Y₁ X₂ Y₂ : RelCat.{u}} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ (p.1.2, p.2.2) ∈ g.rel} := rfl

@[simp] lemma rel_whiskerLeft (f : Y ⟶ Z) :
    (X ◁ f).rel = {p | p.1.1 = p.2.1 ∧ (p.1.2, p.2.2) ∈ f.rel} := rfl

@[simp] lemma rel_whiskerRight (f : X ⟶ Y) :
    (f ▷ Z).rel = {p | (p.1.1, p.2.1) ∈ f.rel ∧ p.1.2 = p.2.2} := rfl

@[simp] lemma rel_associator_hom :
    (α_ X Y Z).hom.rel = {p | (p.1.1.1, p.1.1.2, p.1.2) = p.2} := rfl

@[simp] lemma rel_associator_inv :
    (α_ X Y Z).inv.rel = {p | ((p.1.1, p.1.2.1), p.1.2.2) = p.2} := rfl

@[simp] lemma rel_leftUnitor_hom : (λ_ X).hom.rel = {p | p.1.2 = p.2} := rfl

@[simp] lemma rel_leftUnitor_inv : (λ_ X).inv.rel = {p | (PUnit.unit, p.1) = p.2} := rfl

@[simp] lemma rel_rightUnitor_hom : (ρ_ X).hom.rel = {p | p.1.1 = p.2} := rfl

@[simp] lemma rel_rightUnitor_inv : (ρ_ X).inv.rel = {p | (p.1, PUnit.unit) = p.2} := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `RelCat` is a monoidal category. -/
instance instMonoidalCategoryRelCat : MonoidalCategory RelCat.{u} where
  tensorHom_def f g := by
    ext ⟨u, v⟩
    simp only [Set.mem_ofPred_eq, rel_tensorHom, Hom.rel_comp, rel_whiskerRight, rel_whiskerLeft]
    constructor
    · rintro ⟨hf, hg⟩
      exact ⟨(v.1, u.2), ⟨hf, rfl⟩, ⟨rfl, hg⟩⟩
    · rintro ⟨w, ⟨hf, h₂⟩, ⟨h₁, hg⟩⟩
      exact ⟨h₁ ▸ hf, h₂ ▸ hg⟩
  id_tensorHom_id X Y := by
    ext ⟨u, v⟩
    simp only [tensorObj_def, rel_tensorHom, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    ext ⟨u, w⟩
    simp; grind
  whiskerLeft_id X Y := by
    ext
    simp only [tensorObj_def, rel_whiskerLeft, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  id_whiskerRight X Y := by
    ext
    simp only [tensorObj_def, rel_whiskerRight, Hom.rel_id, SetRel.mem_id, Set.mem_ofPred_eq]
    exact Prod.ext_iff.symm
  associator_naturality f₁ f₂ f₃ := by
    ext ⟨u, v⟩
    simp [Prod.ext_iff, and_assoc]
  leftUnitor_naturality f := by
    ext ⟨u, v⟩
    simp [Prod.exists]
  rightUnitor_naturality f := by
    ext ⟨u, v⟩
    simp [Prod.exists]
  pentagon W X Y Z := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]
  triangle X Y := by
    ext ⟨u, v⟩
    simp [Prod.exists, Prod.ext_iff]

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
  DaggerCategory.isUnitary_of_dagger_eq_inv (graphFunctor.mapIso e) <| by
    apply Hom.ext
    exact (Equiv.graph_inv e.toEquiv).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The cartesian tensor product is compatible with relation reversal. -/
instance monoidalDaggerCategory : MonoidalDaggerCategory RelCat.{u} where
  dagger_tensor f g := by ext; simp
  isUnitary_associator X Y Z := isUnitary_graphFunctor_mapIso (Equiv.prodAssoc X Y Z).toIso
  isUnitary_leftUnitor X := isUnitary_graphFunctor_mapIso (Equiv.punitProd X).toIso
  isUnitary_rightUnitor X := isUnitary_graphFunctor_mapIso (Equiv.prodPUnit X).toIso

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

/-! ### Morphism properties related to the dagger category structure on `RelCat` -/

/-- In `RelCat`, a morphism is unitary exactly when it is an isomorphism. -/
theorem isUnitary_iff_isIso (f : X ⟶ Y) : DaggerCategory.IsUnitary f ↔ IsIso f := by
  refine ⟨fun h ↦ h.isIso, fun h ↦ ?_⟩
  rcases (rel_iso_iff f).1 h with ⟨e, he⟩
  rw [← he]
  exact isUnitary_graphFunctor_mapIso e

/-- In `RelCat`, an isometry is exactly a left-total, left-unique relation. -/
theorem isIsometry_iff_leftTotal_leftUnique (f : X ⟶ Y) : DaggerCategory.IsIsometry f ↔
    Relator.LeftTotal (fun x : X ↦ fun y : Y ↦ (x, y) ∈ f.rel) ∧
      Relator.LeftUnique (fun x : X ↦ fun y : Y ↦ (x, y) ∈ f.rel) := by
  rw [← SetRel.comp_inv_eq_id_iff f.rel]
  constructor
  · intro h
    simpa only [Hom.rel_comp, rel_dagger, Hom.rel_id] using
      congrArg Hom.rel h.comp_dagger_eq_id
  · intro h
    exact ⟨Hom.ext _ _ (by simpa only [Hom.rel_comp, rel_dagger, Hom.rel_id] using h)⟩

/-- In `RelCat`, a projection is exactly a symmetric and transitive relation, i.e. a partial
equivalence relation. -/
theorem isProj_iff_symm_trans (f : X ⟶ X) : DaggerCategory.IsProj f ↔
    f.rel.IsSymm ∧ f.rel.IsTrans := by
  constructor
  · intro h
    constructor
    · exact SetRel.inv_eq_self_iff.1 (congrArg Hom.rel h.selfAdjoint)
    · apply SetRel.isTrans_iff_comp_subset_self.2
      exact (congrArg Hom.rel h.idem : f.rel.comp f.rel = f.rel).le
  · rintro ⟨hsymm, htrans⟩
    constructor
    · exact Hom.ext _ _ (SetRel.comp_eq_self_of_isSymm_of_isTrans f.rel)
    · exact Hom.ext _ _ (SetRel.inv_eq_self f.rel)

/-- In `RelCat`, a positive morphism is exactly a symmetric relation that is reflexive on its
domain. -/
theorem isPositive_iff_isSymm_reflOnDom (f : X ⟶ X) : DaggerCategory.IsPositive f ↔
    f.rel.IsSymm ∧ ∀ x : X, (∃ x' : X, (x, x') ∈ f.rel) → (x, x) ∈ f.rel := by
  constructor
  · intro h
    obtain ⟨Y, g, hfg⟩ := h.out
    constructor
    · rw [hfg, Hom.rel_comp, rel_dagger]
      exact SetRel.comp_inv_isSymm g.rel
    · rintro x ⟨x', hxx'⟩
      rw [hfg, Hom.rel_comp] at hxx' ⊢
      rcases hxx' with ⟨y, hxy, _⟩
      exact ⟨y, hxy, (mem_dagger g x y).2 hxy⟩
  · rintro ⟨hsymm, hrefl⟩
    let E : RelCat.{u} := {p : X × X // p ∈ f.rel}
    let g : X ⟶ E := .ofRel {q : X × E | q.1 = q.2.1.1 ∨ q.1 = q.2.1.2}
    have hg : ∀ a e, (a, e) ∈ g.rel ↔ a = e.1.1 ∨ a = e.1.2 := fun _ _ ↦ Iff.rfl
    refine ⟨E, g, ?_⟩
    apply Hom.ext
    ext ⟨a, b⟩
    constructor
    · intro hab
      rw [Hom.rel_comp]
      exact ⟨⟨(a, b), hab⟩, .inl rfl, .inr rfl⟩
    · intro hab
      rw [Hom.rel_comp] at hab
      rcases hab with ⟨e, hae, hbe⟩
      rcases (hg a e).1 hae with (rfl | rfl) <;> rcases (hg b e).1 hbe with (rfl | rfl)
      · exact hrefl e.1.1 ⟨e.1.2, e.2⟩
      · exact e.2
      · exact hsymm.symm e.1.1 e.1.2 e.2
      · exact hrefl e.1.2 ⟨e.1.1, hsymm.symm e.1.1 e.1.2 e.2⟩

end CategoryTheory.RelCat
