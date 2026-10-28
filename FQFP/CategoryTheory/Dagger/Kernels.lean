/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Dagger kernels

A dagger kernel is a limiting kernel fork with an isometric inclusion.
The witness is independent of the choice of an ordinary kernel.

## Main definitions

* `DaggerCategory.DaggerKernel`: the fork, universal property, and isometry.
* `DaggerCategory.HasDaggerKernel`, `DaggerCategory.HasDaggerKernels`: existence properties.
* `DaggerCategory.daggerKernel`: a chosen witness.

## Main results

* `DaggerCategory.DaggerKernel.isUnitary_iso`: comparison of dagger kernels is unitary.
* `DaggerCategory.kernelLift_eq_dagger_comp`: factorization through an isometric kernel.
* `DaggerCategory.eq_zero_of_comp_dagger_eq_zero`: **Lemma 2.49**, nondegeneracy.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.DaggerCategory

variable {C : Type u} [Category.{v} C] [DaggerCategory C]

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
  rw [isUnitary_hom_iff_dagger_hom_eq_inv]
  have hi_hom : (k.iso l).hom ≫ l.ι = k.ι :=
    IsLimit.conePointUniqueUpToIso_hom_comp k.isLimit l.isLimit WalkingParallelPair.zero
  have hi_inv : (k.iso l).inv ≫ k.ι = l.ι :=
    IsLimit.conePointUniqueUpToIso_inv_comp k.isLimit l.isLimit WalkingParallelPair.zero
  rw [IsIsometry.eq_dagger_comp_of_comp_eq l.ι hi_hom]
  simpa using (IsIsometry.eq_dagger_comp_of_comp_eq k.ι hi_inv).symm

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
