/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Category.RelCat.Dagger

/-!
# Dagger-derived morphism classes in the category of relations

This file characterizes the morphism classes of `RelCat` defined by the dagger — unitaries,
isometries, projections and positive morphisms — in terms of the underlying relations.

## Main results

* `isUnitary_iff_isIso`: unitary morphisms are exactly the isomorphisms.
* `isIsometry_iff_leftTotal_leftUnique`: isometries are exactly left-total, left-unique
  relations.
* `isStarProjection_iff_symm_trans`: projections are exactly partial equivalence relations.
* `isPositive_iff_isSymm_reflOnDom`: positive morphisms are exactly symmetric relations that are
  reflexive on their domain.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.RelCat

variable {X Y Z : RelCat.{u}}

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

/-- In `RelCat`, a self-adjoint endomorphism is exactly a symmetric relation. -/
theorem isSelfAdjoint_iff_isSymm (A : End X) : IsSelfAdjoint A ↔ A.asHom.rel.IsSymm := by
  rw [End.isSelfAdjoint_iff]
  exact ⟨fun h ↦ SetRel.inv_eq_self_iff.1 (congrArg Hom.rel h),
    fun h ↦ Hom.ext _ _ (SetRel.inv_eq_self_iff.2 h)⟩

/-- In `RelCat`, a projection is exactly a symmetric and transitive relation, i.e. a partial
equivalence relation. -/
theorem isStarProjection_iff_symm_trans (P : End X) : IsStarProjection P ↔
    P.asHom.rel.IsSymm ∧ P.asHom.rel.IsTrans := by
  constructor
  · intro h
    constructor
    · exact (isSelfAdjoint_iff_isSymm P).1 h.isSelfAdjoint
    · apply SetRel.isTrans_iff_comp_subset_self.2
      exact (congrArg Hom.rel h.isIdempotentElem.asHom_comp_self).le
  · rintro ⟨hsymm, htrans⟩
    refine ⟨End.ext ?_, End.ext ?_⟩
    · exact Hom.ext _ _ (SetRel.comp_eq_self_of_isSymm_of_isTrans P.asHom.rel)
    · exact Hom.ext _ _ (SetRel.inv_eq_self P.asHom.rel)

/-- In `RelCat`, a positive morphism is exactly a symmetric relation that is reflexive on its
domain. -/
theorem isPositive_iff_isSymm_reflOnDom (A : End X) : A.IsPositive ↔
    A.asHom.rel.IsSymm ∧ ∀ x : X, (∃ x' : X, (x, x') ∈ A.asHom.rel) → (x, x) ∈ A.asHom.rel := by
  constructor
  · intro h
    constructor
    · exact (isSelfAdjoint_iff_isSymm A).1 h.isSelfAdjoint
    · rintro x ⟨x', hxx'⟩
      obtain ⟨Y, g, hfg⟩ := h
      rw [hfg, Hom.rel_comp] at hxx' ⊢
      rcases hxx' with ⟨y, hxy, _⟩
      exact ⟨y, hxy, (mem_dagger g x y).2 hxy⟩
  · rintro ⟨hsymm, hrefl⟩
    let E : RelCat.{u} := {p : X × X // p ∈ A.asHom.rel}
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
