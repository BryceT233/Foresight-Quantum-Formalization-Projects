/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia, Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.State
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Dagger categories, morphisms and operators

A dagger reverses composition, fixes identities, and is involutive.

## Main definitions

* `DaggerCategory`: a category with a dagger.
* `DaggerCategory.IsIsometry` and `DaggerCategory.IsUnitary`: properties of arrows.
* `CategoryTheory.End`: the endomorphism monoid, with the dagger as its star.
* `IsStarProjection`: a self-adjoint idempotent in the endomorphism monoid.
* `CategoryTheory.End.IsPositive`: endomorphisms admitting a dagger factorization.
* `CategoryTheory.End.outer`: the outer product of states in a monoidal dagger category.

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

/-- The inverse of a unitary isomorphism is unitary. -/
instance IsUnitary.iso_inv {c₁ c₂ : C} (e : c₁ ≅ c₂) [IsUnitary e.hom] :
    IsUnitary e.inv := by
  rw [← IsUnitary.dagger_hom_eq_inv e]
  infer_instance

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

namespace CategoryTheory.MonoidalCategory.State

open DaggerCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [DaggerCategory C] {H K : C}

/-- The outer product `|v⟩⟨w|` as a morphism between the two state spaces. -/
def outerHom (v : State K) (w : State H) : H ⟶ K :=
  w† ≫ v

/-- Taking the dagger of a rectangular outer product exchanges its states. -/
lemma dagger_outerHom (v : State K) (w : State H) :
    (v.outerHom w)† = w.outerHom v := by
  simp [State.outerHom]

/-- Acting on the ket and bra of an outer product applies the corresponding processes
to the two preparations. -/
lemma dagger_comp_outerHom_comp {X Y : C} (v : State H) (w : State K) (f : K ⟶ X) (g : H ⟶ Y) :
    f† ≫ v.outerHom w ≫ g = State.outerHom (v ≫ g) (w ≫ f) := by
  simp [State.outerHom]

end CategoryTheory.MonoidalCategory.State

namespace CategoryTheory.End

open DaggerCategory

variable {C : Type*} [Category* C]

/-- Idempotence in categorical composition order. -/
theorem _root_.IsIdempotentElem.asHom_comp_self {X : C} {P : End X} (h : IsIdempotentElem P) :
    P.asHom ≫ P.asHom = P.asHom := congrArg End.asHom h.eq

variable [DaggerCategory C] {X : C}

instance instStarMulOfDaggerCategory : StarMul (End X) where
  star A := .of A.asHom†
  star_involutive A := End.ext (involutive_dagger A.asHom)
  star_mul A B := End.ext (dagger_comp B.asHom A.asHom)

/-- The underlying arrow of the star is the dagger of the underlying arrow. -/
@[simp] theorem star_asHom (A : End X) : (star A).asHom = A.asHom† := rfl

/-- An endomorphism is self-adjoint exactly when the dagger fixes its underlying arrow. -/
theorem isSelfAdjoint_iff (A : End X) : IsSelfAdjoint A ↔ A.asHom† = A.asHom :=
  End.ext_iff

/-- The dagger fixes the arrow of a self-adjoint endomorphism. -/
theorem _root_.IsSelfAdjoint.dagger_asHom {A : End X} (h : IsSelfAdjoint A) :
    A.asHom† = A.asHom := (End.isSelfAdjoint_iff A).mp h

/-- The zero arrow gives a self-adjoint endomorphism in any dagger category with zeros. -/
theorem isSelfAdjoint_of_zero [Limits.HasZeroMorphisms C] : IsSelfAdjoint (End.of (0 : X ⟶ X)) :=
  End.ext dagger_zero

/-- Unitary elements of the endomorphism monoid correspond to unitary arrows. -/
theorem mem_unitary_iff (A : End X) : A ∈ unitary (End X) ↔ IsUnitary A.asHom := by
  rw [Unitary.mem_iff, isUnitary_iff]
  simp only [End.ext_iff, mul_asHom, star_asHom, one_asHom]

instance (U : unitary (End X)) : IsUnitary U.val.asHom :=
  (mem_unitary_iff U.val).mp U.property

instance : IsUnitary (1 : End X).asHom := inferInstanceAs (IsUnitary (𝟙 X))

variable {H K : C}

/-- A positive endomorphism factors through an arbitrary object as a morphism
followed by its dagger. -/
def IsPositive (A : End H) : Prop :=
  ∃ (K : C) (g : H ⟶ K), A.asHom = g ≫ g†

theorem isPositive_iff (A : End H) :
    A.IsPositive ↔ ∃ (K : C) (g : H ⟶ K), A.asHom = g ≫ g† := Iff.rfl

/-- Every projection gives its own Gram factorization. -/
theorem _root_.IsStarProjection.isPositive {P : End H} (h : IsStarProjection P) : IsPositive P :=
  ⟨H, P.asHom, by rw [h.isSelfAdjoint.dagger_asHom, h.isIdempotentElem.asHom_comp_self]⟩

theorem IsPositive.one (H : C) : IsPositive (1 : End H) := (IsStarProjection.one (End H)).isPositive

/-- The range projection of an isometry. -/
theorem isStarProjection_dagger_comp (f : H ⟶ K) [IsIsometry f] :
    IsStarProjection (End.of (f† ≫ f)) := ⟨End.ext (by simp), End.ext (by simp)⟩

theorem IsPositive.comp_dagger (f : H ⟶ K) : IsPositive (.of (f ≫ f†)) := ⟨K, f, rfl⟩

theorem IsPositive.dagger_comp (f : H ⟶ K) : IsPositive (.of (f† ≫ f)) :=
  ⟨H, f†, by simp⟩

theorem IsPositive.star_mul_self (A : End H) : IsPositive (star A * A) :=
  IsPositive.comp_dagger A.asHom

theorem IsPositive.mul_star_self (A : End H) : IsPositive (A * star A) :=
  IsPositive.dagger_comp A.asHom

/-- A positive endomorphism is self-adjoint. -/
theorem IsPositive.isSelfAdjoint {A : End H} (h : IsPositive A) : IsSelfAdjoint A := by
  obtain ⟨K, g, hg⟩ := h
  rw [End.isSelfAdjoint_iff, hg, DaggerCategory.dagger_comp, involutive_dagger]

/-- A positive operator is fixed by the operator star. -/
theorem IsPositive.star_eq {A : End H} (h : IsPositive A) : star A = A := h.isSelfAdjoint.star_eq

theorem IsPositive.star {A : End H} (h : IsPositive A) : IsPositive (star A) :=
  h.star_eq.symm ▸ h

open MonoidalCategory

variable [MonoidalCategory C]

/-- The outer product of states `v` and `w`, with underlying arrow `w† ≫ v`. -/
def outer (v w : State H) : End H := .of (v.outerHom w)

@[simp] theorem outer_asHom (v w : State H) : (outer v w).asHom = w† ≫ v := rfl

/-- Taking the adjoint of an outer product exchanges its two states. -/
@[simp] theorem star_outer (v w : State H) : star (outer v w) = outer w v := by
  apply End.ext
  simp

/-- The outer square of any state is positive. -/
theorem isPositive_outer_self (v : State H) : IsPositive (outer v v) := IsPositive.dagger_comp v

/-- A normalized state determines the projection onto its image. -/
theorem isStarProjection_outer_self (v : State H) [IsIsometry v] :
    IsStarProjection (outer v v) := isStarProjection_dagger_comp v

end CategoryTheory.End
