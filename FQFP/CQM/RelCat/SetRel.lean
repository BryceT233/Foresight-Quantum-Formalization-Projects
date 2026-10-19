/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Category.RelCat

/-!
# Set-theoretic lemmas on relations

Elementary lemmas about `SetRel` that the `RelCat` instances and morphism characterizations
below rely on: composition distributing over union, and the correspondence between a relation
composed with its inverse and being left-total and left-unique.
-/

@[expose] public section

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
