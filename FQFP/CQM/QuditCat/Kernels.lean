/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.QuditCat.Dagger

/-!
# Dagger kernels of qudit morphisms

The kernel of a linear map between finite-dimensional Hilbert spaces is a subspace with the
induced inner product. Its inclusion is an isometry, so it gives the dagger kernel of
Example 2.47. The construction includes zero maps and zero-dimensional state spaces.

## Main definitions

* `kernelObj`, `kernelι`: the kernel subspace and its inclusion.
* `kernelLift`, `kernelIsLimit`: corestriction and the categorical universal property.
* `daggerKernel`: the explicit isometric kernel fork.
* `hasDaggerKernels`: every qudit morphism has a dagger kernel.

## Main results

* `isIsometry_kernelι`: the inclusion preserves the induced inner product.
* `kernelLift_comp`: corestriction followed by inclusion recovers the original map.

The explicit `daggerKernel` is available for computations. The existence instance also enables
the abstract nondegeneracy theorem, without imposing an isometry on an independently chosen
ordinary kernel.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DaggerCategory

namespace QuditCat

noncomputable section

variable {H K L : QuditCat}

/-- The kernel subspace of a linear map, with its induced Hilbert space structure. -/
abbrev kernelObj (f : H ⟶ K) : QuditCat := of (LinearMap.ker f.hom)

/-- The inclusion of the kernel subspace into the domain. -/
def kernelι (f : H ⟶ K) : kernelObj f ⟶ H :=
  ofHom (LinearMap.ker f.hom).subtype

/-- The kernel inclusion sends a subtype element to its underlying vector. -/
@[simp]
lemma kernelι_apply (f : H ⟶ K) (x : (kernelObj f).state) : (kernelι f) x = x.1 := rfl

/-- The kernel inclusion is annihilated by the given map. -/
@[reassoc]
lemma kernelι_comp (f : H ⟶ K) : kernelι f ≫ f = 0 := by
  apply hom_ext
  exact LinearMap.comp_ker_subtype f.hom

/-- The kernel inclusion is an isometry for the induced inner product. -/
instance isIsometry_kernelι (f : H ⟶ K) : IsIsometry (kernelι f) where
  comp_dagger_eq_id := by
    apply hom_ext
    change (LinearMap.ker f.hom).subtype.adjoint ∘ₗ (LinearMap.ker f.hom).subtype =
      LinearMap.id
    apply LinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ y ((LinearMap.ker f.hom).subtype.adjoint x.1) = inner ℂ y x
    rw [LinearMap.adjoint_inner_right]
    rfl

/-- The kernel fork formed from the subspace inclusion. -/
def kernelCone (f : H ⟶ K) : KernelFork f := KernelFork.ofι (kernelι f) (kernelι_comp f)

/-- A map annihilated by `f` corestricts to its kernel subspace. -/
def kernelLift (f : H ⟶ K) (g : L ⟶ H) (hg : g ≫ f = 0) : L ⟶ kernelObj f :=
  ofHom <| LinearMap.codRestrict f.hom.ker g.hom fun x ↦ LinearMap.mem_ker.2 <| by
    have h := congrArg (fun m ↦ m.hom x) hg
    simpa only [hom_comp, LinearMap.comp_apply, hom_zero, LinearMap.zero_apply] using h

/-- Corestriction does not change the underlying vector. -/
@[simp]
lemma coe_kernelLift (f : H ⟶ K) (g : L ⟶ H) (hg : g ≫ f = 0) (x : L.state) :
    ((kernelLift f g hg) x).1 = g x := rfl

/-- Corestriction followed by the kernel inclusion is the original map. -/
@[reassoc (attr := simp)]
lemma kernelLift_comp (f : H ⟶ K) (g : L ⟶ H) (hg : g ≫ f = 0) :
    kernelLift f g hg ≫ kernelι f = g :=
  hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _

/-- The subspace kernel fork is limiting; uniqueness follows from its isometric inclusion. -/
def kernelIsLimit (f : H ⟶ K) : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι' (kernelι f) (kernelι_comp f) fun g hg ↦
    ⟨kernelLift f g hg, kernelLift_comp f g hg⟩

/-- The kernel subspace and its isometric inclusion form a dagger kernel, as in Example 2.47. -/
def daggerKernel (f : H ⟶ K) : DaggerKernel f where
  fork := kernelCone f
  isLimit := kernelIsLimit f
  isIsometry := inferInstanceAs (IsIsometry (kernelι f))

/-- Every morphism between finite-dimensional qudits has a dagger kernel. -/
instance hasDaggerKernels : HasDaggerKernels QuditCat where
  hasDaggerKernel f := ⟨⟨daggerKernel f⟩⟩

end

end QuditCat
