/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Dagger categories

This file defines the categorical abstraction of the dagger (adjoint) operation: a
contravariant involution on morphisms that fixes identities and reverses
composition. It also introduces the standard classes of morphisms used in categorical
quantum mechanics — projections, isometries, unitaries, and positive maps — together
with monoidal dagger categories, where the dagger is compatible with the monoidal
structure, and dagger kernels, represented by limiting kernel forks with isometric inclusions.

## Main definitions

* `DaggerCategory`: a category equipped with a dagger.
* `DaggerCategory.IsProj`: an idempotent self-adjoint endomorphism, i.e. a projection.
* `DaggerCategory.IsIsometry`: a morphism `f` satisfying `f ≫ f† = 𝟙`.
* `DaggerCategory.IsUnitary`: an isometry `f` that also satisfies `f† ≫ f = 𝟙`.
* `DaggerCategory.IsPositive`: an endomorphism of the form `g ≫ g†`.
* `DaggerCategory.DaggerKernel`: a limiting isometric kernel fork.
* `DaggerCategory.HasDaggerKernel` and `DaggerCategory.HasDaggerKernels`: existence of dagger
  kernels for a particular morphism and for all morphisms, respectively.
* `DaggerCategory.daggerKernel`: a kernel selected together with its isometry and
  universal property.
* `MonoidalDaggerCategory`: a dagger category that is also monoidal, with the dagger
  compatible with the tensor product and the structural isomorphisms.

## Notation

* `f†` is notation for `DaggerCategory.dagger f`.

## Main results

* `dagger_zero`: the dagger of a zero morphism is zero.
* `isZero_of_isInitial` and `isZero_of_isTerminal`: in a dagger category, initial and
  terminal objects are zero objects.
* `DaggerCategory.IsIsometry.eq_dagger_comp_of_comp_eq`: a factorization through an
  isometry is unique, given by `x ≫ f†`.
* `DaggerCategory.kernelLift_eq_dagger_comp`: when `kernel.ι f` is an isometry, the
  canonical factorization through `kernel f` is `g ≫ (kernel.ι f)†`.
* `DaggerCategory.DaggerKernel.isUnitary_iso`: the canonical isomorphism between two dagger
  kernels of the same morphism is unitary.
* `DaggerCategory.isUnitary_kernelIso`: comparison with a chosen ordinary kernel is unitary
  when that kernel's inclusion is also an isometry.
* `DaggerCategory.eq_zero_of_comp_dagger_eq_zero`: **Lemma 2.49**, nondegeneracy, requiring only
  a dagger kernel of the dagger of the given morphism.
* `dagger_inv_eq_hom_of_isUnitary`, `dagger_hom_eq_inv_of_isUnitary`: the dagger of either
  direction of a unitary isomorphism is the other direction.
* `dagger_whiskerLeft`, `dagger_whiskerRight`: the dagger commutes with whiskering.

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
  left_inv _ := by simp
  right_inv _ := by simp

/-- An idempotent self-adjoint endomorphism, i.e. a projection. -/
class IsProj [DaggerCategory C] {c : C} (f : c ⟶ c) where
  idem (f) : f ≫ f = f
  selfAdjoint (f) : f† = f

attribute [simp] IsProj.selfAdjoint

@[simp]
lemma IsProj.comp_self {c : C} (f : c ⟶ c) [IsProj f] : f ≫ f = f := IsProj.idem f

theorem IsProj.id (c : C) : IsProj (𝟙 c) := ⟨by simp, by simp⟩

instance IsProj.dagger {c : C} (f : c ⟶ c) [IsProj f] : IsProj f† := by simpa

/-- A morphism satisfying `f ≫ f† = 𝟙`, i.e. an isometry. -/
class IsIsometry [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) where
  comp_dagger_eq_id (f) : f ≫ f† = 𝟙 c₁

attribute [reassoc (attr := simp)] IsIsometry.comp_dagger_eq_id

instance (c : C) : IsIsometry (𝟙 c) := ⟨by simp⟩

instance IsIsometry.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsIsometry f]
    [IsIsometry g] : IsIsometry (f ≫ g) where
  comp_dagger_eq_id := by
    simp only [dagger_comp, Category.assoc, IsIsometry.comp_dagger_eq_id_assoc,
      IsIsometry.comp_dagger_eq_id]

/-- An isometry is a split monomorphism with retraction its dagger. -/
instance IsIsometry.isSplitMono {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsIsometry f] : IsSplitMono f :=
  .mk' { retraction := f†, id := IsIsometry.comp_dagger_eq_id f }

/-- The composite `f† ≫ f` of an isometry is a projection (onto its image). -/
instance IsIsometry.isProj_dagger_comp {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsIsometry f] :
    IsProj (f† ≫ f) where
  idem := by
    simp only [Category.assoc,
      IsIsometry.comp_dagger_eq_id_assoc]
  selfAdjoint := by simp

/-- If `f` is an isometry, a factorization `m ≫ f = x` determines `m` uniquely: `m = x ≫ f†`. -/
lemma IsIsometry.eq_dagger_comp_of_comp_eq {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) [IsIsometry f]
    {m : c₃ ⟶ c₁} {x : c₃ ⟶ c₂} (h : m ≫ f = x) : m = x ≫ f† := by
  rw [(Category.comp_id m).symm, ← IsIsometry.comp_dagger_eq_id f, ← Category.assoc, h]

/-- An isometry that also satisfies `f† ≫ f = 𝟙`, i.e. a unitary morphism. -/
class IsUnitary [DaggerCategory C] {c₁ c₂ : C} (f : c₁ ⟶ c₂) extends IsIsometry f where
  dagger_comp_eq_id (f) : f† ≫ f = 𝟙 c₂

attribute [reassoc (attr := simp)] IsUnitary.dagger_comp_eq_id

instance (c : C) : IsUnitary (𝟙 c) := ⟨by simp⟩

instance IsUnitary.comp {c₁ c₂ c₃ : C} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) [IsUnitary f]
    [IsUnitary g] : IsUnitary (f ≫ g) where
  dagger_comp_eq_id := by
    simp only [dagger_comp, Category.assoc, IsUnitary.dagger_comp_eq_id_assoc,
      IsUnitary.dagger_comp_eq_id]

instance IsUnitary.dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsUnitary f† where
  comp_dagger_eq_id := by simp
  dagger_comp_eq_id := by simp

instance IsUnitary.isIso {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : IsIso f :=
  ⟨f†, by simp, by simp⟩

lemma IsUnitary.inv_self_eq_dagger {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f = f† := by
  rw [← Category.comp_id (inv f), ← IsIsometry.comp_dagger_eq_id f, ← Category.assoc]
  simp

lemma IsUnitary.inv_dagger_eq_self {c₁ c₂ : C} (f : c₁ ⟶ c₂) [IsUnitary f] : inv f† = f := by
  simp [inv_self_eq_dagger f†]

/-- An isomorphism whose dagger is its inverse has a unitary forward map. -/
theorem isUnitary_of_dagger_eq_inv {c₁ c₂ : C} (e : c₁ ≅ c₂) (hdag : e.hom† = e.inv) :
    DaggerCategory.IsUnitary e.hom where
  comp_dagger_eq_id := hdag ▸ e.hom_inv_id
  dagger_comp_eq_id := hdag ▸ e.inv_hom_id

/-- An endomorphism of the form `g ≫ g†` for some morphism `g`, i.e. a positive morphism. -/
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
lemma selfAdjoint_of_isPositive {c : C} (f : c ⟶ c) [IsPositive f] : f† = f := by
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

section kernel

/-- A **dagger kernel** is a limiting kernel fork whose inclusion is an isometry. -/
structure DaggerKernel [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) where
  /-- The kernel fork, including its object and inclusion. -/
  fork : KernelFork f
  /-- The universal property of the kernel fork. -/
  isLimit : IsLimit fork
  /-- The kernel inclusion is an isometry. -/
  isIsometry : IsIsometry fork.ι

namespace DaggerKernel

variable [HasZeroMorphisms C] {X Y Z : C} {f : X ⟶ Y}

/-- The object of a dagger kernel. -/
abbrev obj (k : DaggerKernel f) : C := k.fork.pt

/-- The isometric inclusion of a dagger kernel. -/
abbrev ι (k : DaggerKernel f) : k.obj ⟶ X := k.fork.ι

instance (k : DaggerKernel f) : IsIsometry k.ι := k.isIsometry

/-- The inclusion of a dagger kernel is annihilated by the given morphism. -/
@[reassoc]
lemma condition (k : DaggerKernel f) : k.ι ≫ f = 0 := k.fork.condition

/-- The factorization of a morphism through a dagger kernel. -/
def lift (k : DaggerKernel f) (g : Z ⟶ X) (hg : g ≫ f = 0) : Z ⟶ k.obj :=
  k.isLimit.lift (KernelFork.ofι g hg)

/-- The factorization through a dagger kernel recovers the given morphism. -/
@[reassoc (attr := simp)]
lemma lift_ι (k : DaggerKernel f) (g : Z ⟶ X) (hg : g ≫ f = 0) : k.lift g hg ≫ k.ι = g :=
  k.isLimit.fac (KernelFork.ofι g hg) WalkingParallelPair.zero

/-- Factorization through a dagger kernel is composition with its dagger inclusion. -/
lemma lift_eq_comp_dagger (k : DaggerKernel f) (g : Z ⟶ X) (hg : g ≫ f = 0) :
    k.lift g hg = g ≫ k.ι† :=
  IsIsometry.eq_dagger_comp_of_comp_eq k.ι (k.lift_ι g hg)

/-- The canonical isomorphism between two dagger kernels of the same morphism. -/
noncomputable def iso (k l : DaggerKernel f) : k.obj ≅ l.obj :=
  IsLimit.conePointUniqueUpToIso k.isLimit l.isLimit

/-- The canonical isomorphism between dagger kernels is unitary. -/
instance isUnitary_iso (k l : DaggerKernel f) : IsUnitary (k.iso l).hom := by
  apply isUnitary_of_dagger_eq_inv (k.iso l)
  have hi_hom : (k.iso l).hom ≫ l.ι = k.ι :=
    IsLimit.conePointUniqueUpToIso_hom_comp k.isLimit l.isLimit WalkingParallelPair.zero
  have hi_inv : (k.iso l).inv ≫ k.ι = l.ι :=
    IsLimit.conePointUniqueUpToIso_inv_comp k.isLimit l.isLimit WalkingParallelPair.zero
  calc
    _ = (k.ι ≫ l.ι†)† := by
      rw [IsIsometry.eq_dagger_comp_of_comp_eq l.ι hi_hom]
    _ = l.ι ≫ k.ι† := by simp
    _ = (k.iso l).inv := (IsIsometry.eq_dagger_comp_of_comp_eq k.ι hi_inv).symm

end DaggerKernel

/-- The existence of a dagger kernel of a morphism, without fixing an ordinary kernel. -/
class HasDaggerKernel [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There exists a limiting isometric kernel fork. -/
  exists_daggerKernel : Nonempty (DaggerKernel f)

/-- A chosen dagger kernel, selected together with its isometry and universal property. -/
noncomputable def daggerKernel [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y)
    [HasDaggerKernel f] : DaggerKernel f :=
  Classical.choice HasDaggerKernel.exists_daggerKernel

/-- A morphism with a dagger kernel also has an ordinary kernel. -/
instance [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasDaggerKernel f] : HasKernel f where
  exists_limit := ⟨⟨(daggerKernel f).fork, (daggerKernel f).isLimit⟩⟩

/-- If the chosen ordinary kernel inclusion is an isometry, factorization through it is
composition with its dagger. -/
lemma kernelLift_eq_dagger_comp [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) [HasKernel f]
    [IsIsometry (kernel.ι f)] {g : Z ⟶ X} (hg : g ≫ f = 0) :
    kernel.lift f g hg = g ≫ (kernel.ι f)† :=
  IsIsometry.eq_dagger_comp_of_comp_eq (kernel.ι f) (kernel.lift_ι f g hg)

/-- The canonical isomorphism from a chosen ordinary kernel to a dagger kernel is unitary
when the ordinary kernel inclusion is also an isometry. -/
theorem isUnitary_kernelIso [HasZeroMorphisms C] {K X Y : C} {f : X ⟶ Y} (k : K ⟶ X)
    [IsIsometry k] (comp : k ≫ f = 0) (ker : IsLimit (KernelFork.ofι k comp))
    [HasKernel f] [IsIsometry (kernel.ι f)] :
    IsUnitary (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) ker).hom := by
  let canonical : DaggerKernel f :=
    ⟨KernelFork.ofι (kernel.ι f) (kernel.condition f), kernelIsKernel f,
      show IsIsometry (kernel.ι f) from inferInstance⟩
  let candidate : DaggerKernel f :=
    ⟨KernelFork.ofι k comp, ker, show IsIsometry k from inferInstance⟩
  exact DaggerKernel.isUnitary_iso canonical candidate

attribute [local instance] HasZeroObject.zero' in
instance [HasZeroObject C] [HasZeroMorphisms C] (c : C) : IsIsometry (0 : 0 ⟶ c) where
  comp_dagger_eq_id := by simp

attribute [local instance] HasZeroObject.zero' in
/-- An isometry has a dagger kernel whose object is the zero object. -/
instance [HasZeroObject C] [HasZeroMorphisms C] {c₁ c₂ : C} (f : c₁ ⟶ c₂)
    [IsIsometry f] : HasDaggerKernel f where
  exists_daggerKernel := ⟨{
    fork := kernel.zeroKernelFork f
    isLimit := kernel.isLimitConeZeroCone f
    isIsometry := show IsIsometry (0 : 0 ⟶ c₁) from inferInstance }⟩

/-- Every morphism has a dagger kernel, as in Definition 2.46. -/
class HasDaggerKernels (C : Type u) [Category.{v} C] [DaggerCategory C] [HasZeroMorphisms C]
    : Prop where
  /-- Each morphism admits a limiting isometric kernel fork. -/
  hasDaggerKernel {X Y : C} (f : X ⟶ Y) : HasDaggerKernel f

attribute [instance] HasDaggerKernels.hasDaggerKernel

/-- A category with dagger kernels has ordinary kernels. -/
instance [HasZeroMorphisms C] [HasDaggerKernels C] : HasKernels C where
  has_limit f := inferInstanceAs (HasKernel f)

/-- **Lemma 2.49 (nondegeneracy)**: a morphism with zero dagger square is zero, provided its
dagger has a dagger kernel. -/
lemma eq_zero_of_comp_dagger_eq_zero [HasZeroMorphisms C]
    {c₁ c₂ : C} {f : c₁ ⟶ c₂} [HasDaggerKernel f†] (hf : f ≫ f† = 0) : f = 0 := by
  let k := daggerKernel f†
  have hfk : f ≫ k.ι† = 0 := by calc
    _ = (k.ι ≫ f†)† := by simp only [dagger_comp, involutive_dagger]
    _ = _ := by simp
  calc
    _ = k.lift f hf ≫ k.ι := (k.lift_ι f hf).symm
    _ = (f ≫ k.ι†) ≫ k.ι := by rw [k.lift_eq_comp_dagger]
    _ = _ := by simp [hfk]

end kernel

end CategoryTheory.DaggerCategory

namespace CategoryTheory

open DaggerCategory

variable [DaggerCategory C]

/-- For a unitary isomorphism, the dagger of the forward map is the inverse. -/
lemma dagger_hom_eq_inv_of_isUnitary {X Y : C} (e : X ≅ Y) [IsUnitary e.hom] :
    e.hom† = e.inv :=
  (IsUnitary.inv_self_eq_dagger e.hom).symm.trans
    (IsIso.inv_eq_of_hom_inv_id e.hom_inv_id)

/-- For a unitary isomorphism, the dagger of the inverse is the forward map. -/
lemma dagger_inv_eq_hom_of_isUnitary {X Y : C} (e : X ≅ Y) [IsUnitary e.hom] :
    e.inv† = e.hom := by
  rw [← dagger_hom_eq_inv_of_isUnitary e, involutive_dagger]

end CategoryTheory

open DaggerCategory MonoidalCategory

/-- A dagger category that is also monoidal, with the dagger compatible with the tensor product
and the structural isomorphisms. -/
class CategoryTheory.MonoidalDaggerCategory (C : Type u) [Category.{v} C] extends
    DaggerCategory C, MonoidalCategory C where
  dagger_tensor {H₁ H₂ K₁ K₂ : C} (f₁ : H₁ ⟶ K₁) (f₂ : H₂ ⟶ K₂) : (f₁ ⊗ₘ f₂)† = f₁† ⊗ₘ f₂†
  isUnitary_associator (H₁ H₂ H₃ : C) : DaggerCategory.IsUnitary (α_ H₁ H₂ H₃).hom
  isUnitary_leftUnitor (H : C) : DaggerCategory.IsUnitary (λ_ H).hom
  isUnitary_rightUnitor (H : C) : DaggerCategory.IsUnitary (ρ_ H).hom

attribute [simp] MonoidalDaggerCategory.dagger_tensor

attribute [instance] MonoidalDaggerCategory.isUnitary_associator
MonoidalDaggerCategory.isUnitary_leftUnitor MonoidalDaggerCategory.isUnitary_rightUnitor

namespace CategoryTheory.MonoidalDaggerCategory

variable [MonoidalDaggerCategory C]

/-- The dagger of a left whiskering is the left whiskering of the dagger. -/
@[simp]
lemma dagger_whiskerLeft {X Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : (X ◁ f)† = X ◁ f† := by
  have h : (X ◁ f : X ⊗ Y₁ ⟶ X ⊗ Y₂) = 𝟙 X ⊗ₘ f := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

/-- The dagger of a right whiskering is the right whiskering of the dagger. -/
@[simp]
lemma dagger_whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : (f ▷ Y)† = f† ▷ Y := by
  have h : (f ▷ Y : X₁ ⊗ Y ⟶ X₂ ⊗ Y) = f ⊗ₘ 𝟙 Y := by simp [tensorHom_def]
  rw [h, MonoidalDaggerCategory.dagger_tensor, dagger_id]
  simp [tensorHom_def]

end CategoryTheory.MonoidalDaggerCategory

end DaggerCategory
