/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Dagger categories and their morphisms

A dagger reverses composition, fixes identities, and is involutive.

## Main definitions

* `DaggerCategory`: a category with a dagger.
* `DaggerCategory.IsProj`, `DaggerCategory.IsIsometry`, `DaggerCategory.IsUnitary`,
  and `DaggerCategory.IsPositive`: the corresponding classes of morphisms.

## Main results

* `DaggerCategory.dagger_zero`: the dagger preserves zero morphisms.
* `DaggerCategory.IsIsometry.eq_dagger_comp_of_comp_eq`: factorization through an isometry.
* `DaggerCategory.isUnitary_hom_iff_dagger_hom_eq_inv`: characterization of unitary isomorphisms.

## Notation

* `f†` denotes the dagger of `f`.
-/

@[expose] public section

open CategoryTheory

section DaggerCategory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A category equipped with a contravariant dagger that fixes identities, reverses
composition, and is involutive. -/
class CategoryTheory.DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The contravariant dagger of a morphism, reversing its direction. -/
  dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : c₂ ⟶ c₁
  dagger_comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : dagger (f ≫ g) = dagger g ≫ dagger f
  dagger_id (c : C) : dagger (𝟙 c) = 𝟙 c
  involutive_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : dagger (dagger f) = f

/-- Notation `f†` for the dagger of a morphism `f`. -/
notation:max f "†" => DaggerCategory.dagger f

namespace CategoryTheory.DaggerCategory

attribute [simp] dagger_comp dagger_id involutive_dagger

variable [DaggerCategory C]

/-- Dagger induces an equivalence on arrows. -/
@[simps]
def daggerEquiv (c c' : C) : (c ⟶ c') ≃ (c' ⟶ c) where
  toFun := dagger
  invFun := dagger
  left_inv _ := involutive_dagger _
  right_inv _ := involutive_dagger _

/-- An idempotent self-adjoint endomorphism, i.e. a projection. -/
@[mk_iff]
class IsProj {c : C} (f : c ⟶ c) where
  idem (f) : f ≫ f = f
  selfAdjoint (f) : f† = f

attribute [simp] IsProj.selfAdjoint

@[simp]
lemma IsProj.comp_self {c : C} (f : c ⟶ c) [IsProj f] : f ≫ f = f := IsProj.idem f

lemma IsProj.id (c : C) : IsProj (𝟙 c) := ⟨by simp, by simp⟩

instance IsProj.dagger {c : C} (f : c ⟶ c) [IsProj f] : IsProj f† := by cat_disch

/-- A morphism satisfying `f ≫ f† = 𝟙`, i.e. an isometry. -/
@[mk_iff]
class IsIsometry {c₁ c₂ : C} (f : c₁ ⟶ c₂) where
  comp_dagger_eq_id (f) : f ≫ f† = 𝟙 c₁

attribute [reassoc (attr := simp)] IsIsometry.comp_dagger_eq_id

instance (c : C) : IsIsometry (𝟙 c) := ⟨by simp⟩

instance IsIsometry.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsIsometry f]
    [IsIsometry g] : IsIsometry (f ≫ g) := by simp [isIsometry_iff]

/-- An isometry is a split monomorphism with retraction its dagger. -/
instance IsIsometry.isSplitMono {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsIsometry f] : IsSplitMono f :=
  .mk' { retraction := f†, id := IsIsometry.comp_dagger_eq_id f }

/-- The composite `f† ≫ f` of an isometry is a projection (onto its image). -/
instance IsIsometry.isProj_dagger_comp {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsIsometry f] :
    IsProj (f† ≫ f) := by simp [isProj_iff]

/-- If `f` is an isometry, a factorization `m ≫ f = x` determines `m` uniquely: `m = x ≫ f†`. -/
lemma IsIsometry.eq_dagger_comp_of_comp_eq {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) [IsIsometry f]
    {m : c₃ ⟶ c₁} {x : c₃ ⟶ c₂} (h : m ≫ f = x) : m = x ≫ f† := by cat_disch

/-- An isometry that also satisfies `f† ≫ f = 𝟙`, i.e. a unitary morphism. -/
class IsUnitary {c₁ c₂ : C} (f : c₁ ⟶ c₂) extends IsIsometry f where
  dagger_comp_eq_id (f) : f† ≫ f = 𝟙 c₂

attribute [reassoc (attr := simp)] IsUnitary.dagger_comp_eq_id

lemma isUnitary_iff {c₁ c₂ : C} (f : c₁ ⟶ c₂) :
    IsUnitary f ↔ f ≫ f† = 𝟙 c₁ ∧ f† ≫ f = 𝟙 c₂ := by
  refine ⟨fun _ ↦ by simp, fun ⟨h, h'⟩ ↦ ?_⟩
  rw [← isIsometry_iff] at h
  exact IsUnitary.mk h'

instance (c : C) : IsUnitary (𝟙 c) := ⟨by simp⟩

instance IsUnitary.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsUnitary f]
    [IsUnitary g] : IsUnitary (f ≫ g) where
  dagger_comp_eq_id := by cat_disch

instance IsUnitary.dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsUnitary f† where
  comp_dagger_eq_id := by simp
  dagger_comp_eq_id := by simp

instance IsUnitary.isIso {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsIso f :=
  ⟨f†, by simp, by simp⟩

lemma IsUnitary.inv_eq_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f = f† := by
  rw [← Category.comp_id (inv f), ← IsIsometry.comp_dagger_eq_id f, ← Category.assoc]
  simp

lemma IsUnitary.inv_dagger_eq_self {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f† = f := by
  simp [inv_eq_dagger f†]

/-- An isomorphism whose forward map is unitary if and only if its dagger is its inverse. -/
theorem isUnitary_hom_iff_dagger_hom_eq_inv {c₁ c₂ : C} (e : c₁ ≅ c₂) :
    IsUnitary e.hom ↔ e.hom† = e.inv := by
  refine ⟨fun _ ↦ ?_, fun h ↦ ?_⟩
  · simp [← IsUnitary.inv_eq_dagger]
  · simp [isUnitary_iff, h]

/-- For a unitary isomorphism, the dagger of the forward map is the inverse. -/
@[simp]
lemma IsUnitary.dagger_hom_eq_inv {c₁ c₂ : C} (e : c₁ ≅ c₂) [IsUnitary e.hom] :
    e.hom† = e.inv := (isUnitary_hom_iff_dagger_hom_eq_inv e).mp inferInstance

/-- For a unitary isomorphism, the dagger of the inverse is the forward map. -/
@[simp]
lemma IsUnitary.dagger_inv_eq_hom {c₁ c₂ : C} (e : c₁ ≅ c₂) [IsUnitary e.hom] :
    e.inv† = e.hom := by
  rw [← ‹IsUnitary e.hom›.dagger_hom_eq_inv, involutive_dagger]

/-- An endomorphism of the form `g ≫ g†` for some morphism `g`, i.e. a positive morphism. -/
@[mk_iff]
class IsPositive {c : C} (f : c ⟶ c) where
  out (f) : ∃ (c' : C) (g : c ⟶ c'), f = g ≫ g†

instance IsPositive.id (c : C) : IsPositive (𝟙 c) := ⟨c, 𝟙 c, by simp⟩

instance IsPositive.comp_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) : IsPositive (f ≫ f†) :=
  ⟨c₂, f, rfl⟩

instance IsPositive.dagger_comp {c₁ c₂ : C} (f : c₁ ⟶ c₂) : IsPositive (f† ≫ f) :=
  ⟨c₁, f†, by simp⟩

instance IsPositive.dagger {c : C} (f : c ⟶ c) [IsPositive f] : IsPositive f† := by
  rcases IsPositive.out f with ⟨c', g, rfl⟩
  simpa

/-- A positive endomorphism is self-adjoint. -/
@[simp low]
lemma IsPositive.selfAdjoint {c : C} (f : c ⟶ c) [IsPositive f] : f† = f := by
  rcases IsPositive.out f with ⟨c', g, rfl⟩
  simp

open Limits

@[simp]
lemma dagger_zero [HasZeroMorphisms C] {c c' : C} : (0 : c ⟶ c')† = 0 := by
  have h : (0 : c ⟶ c') ≫ (0 : c ⟶ c')† ≫ (0 : c ⟶ c') = 0 := by simp
  have hd := congrArg dagger h
  rw [dagger_comp, dagger_comp, involutive_dagger] at hd
  simpa only [comp_zero, zero_comp] using hd.symm

lemma isZero_of_isInitial {c : C} (init : IsInitial c) : IsZero c where
  unique_to c' := ⟨isInitialEquivUnique _ _ init c'⟩
  unique_from c' := ⟨have := isInitialEquivUnique _ _ init c'; Equiv.unique (daggerEquiv ..)⟩

lemma isZero_of_isTerminal {c : C} (term : IsTerminal c) : IsZero c where
  unique_to c' := ⟨have := isTerminalEquivUnique _ _ term c'; Equiv.unique (daggerEquiv ..)⟩
  unique_from c' := ⟨isTerminalEquivUnique _ _ term c'⟩

end CategoryTheory.DaggerCategory

end DaggerCategory
