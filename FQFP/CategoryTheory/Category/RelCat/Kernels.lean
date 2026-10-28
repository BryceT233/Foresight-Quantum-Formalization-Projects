/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CategoryTheory.Dagger.Kernels
public import FQFP.CategoryTheory.Category.RelCat.Morphism
public import FQFP.CategoryTheory.Category.RelCat.Semiadditive

/-!
# Dagger kernels of relations

The kernel of a relation consists of the elements of its domain having no successor. The graph
of the subtype inclusion is an isometry and is a categorical kernel, as in Example 2.47.
No finiteness assumption is imposed on the objects, and the kernel may be empty.

## Main definitions

* `kernelObj`, `kernelι`: the subtype of elements with no successor and its inclusion graph.
* `kernelLift`, `kernelIsLimit`: restriction to this subtype and the universal property.
* `daggerKernel`: the explicit isometric kernel fork.
* `hasDaggerKernels`: every relation has a dagger kernel.

## Main results

* `mem_kernelObj_of_comp_eq_zero`: a relation annihilated by `f` lands in its kernel.
* `kernelLift_comp`: restriction followed by inclusion recovers the annihilated relation.

The explicit witness supports relational computations, while the existence instance enables
abstract dagger-kernel results such as nondegeneracy. It does not make an arbitrary chosen
ordinary kernel inclusion isometric.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DaggerCategory

namespace CategoryTheory.RelCat

universe u

variable {X Y Z : RelCat.{u}}

/-- The elements of the domain with no successor under the given relation. -/
def kernelObj (f : X ⟶ Y) : RelCat.{u} := {x : X // ¬ ∃ y : Y, (x, y) ∈ f.rel}

/-- The graph of the inclusion of the relational kernel. -/
def kernelι (f : X ⟶ Y) : kernelObj f ⟶ X := .ofRel {p | p.1.1 = p.2}

/-- The kernel inclusion relates an element to its underlying domain element. -/
@[simp]
lemma mem_kernelι (f : X ⟶ Y) (x : kernelObj f) (y : X) :
    (x, y) ∈ (kernelι f).rel ↔ x.1 = y := Iff.rfl

/-- An inclusion graph is left-total and left-unique, hence an isometry. -/
instance isIsometry_kernelι (f : X ⟶ Y) : IsIsometry (kernelι f) := by
  apply (isIsometry_iff_leftTotal_leftUnique _).2
  constructor
  · intro x
    exact ⟨x.1, rfl⟩
  · intro x x' y h h'
    exact Subtype.ext (h.trans h'.symm)

/-- No element of the relational kernel can be followed by the given relation. -/
@[reassoc]
lemma kernelι_comp (f : X ⟶ Y) : kernelι f ≫ f = 0 := by
  apply Hom.ext
  ext ⟨x, y⟩
  change (∃ a : X, x.1 = a ∧ (a, y) ∈ f.rel) ↔ False
  constructor
  · rintro ⟨a, rfl, h⟩
    exact x.2 ⟨y, h⟩
  · exact False.elim

/-- Every element reached by an annihilated relation has no successor under `f`. -/
lemma mem_kernelObj_of_comp_eq_zero {f : X ⟶ Y} {g : Z ⟶ X} (hg : g ≫ f = 0)
    {z : Z} {x : X} (hx : (z, x) ∈ g.rel) : ¬ ∃ y : Y, (x, y) ∈ f.rel := by
  rintro ⟨y, hy⟩
  have h : (z, y) ∈ (g ≫ f).rel := ⟨x, hx, hy⟩
  rw [hg, rel_zero] at h
  exact h

/-- Restriction of a relation to the kernel subtype; defined even without annihilation. -/
def kernelLift (f : X ⟶ Y) (g : Z ⟶ X) : Z ⟶ kernelObj f :=
  .ofRel {p | (p.1, p.2.1) ∈ g.rel}

/-- The restricted relation has the same membership condition on kernel elements. -/
@[simp]
lemma mem_kernelLift (f : X ⟶ Y) (g : Z ⟶ X) (z : Z) (x : kernelObj f) :
    (z, x) ∈ (kernelLift f g).rel ↔ (z, x.1) ∈ g.rel := Iff.rfl

/-- Restriction followed by inclusion recovers every relation annihilated by `f`. -/
@[reassoc (attr := simp)]
lemma kernelLift_comp (f : X ⟶ Y) (g : Z ⟶ X) (hg : g ≫ f = 0) :
    kernelLift f g ≫ kernelι f = g := by
  apply Hom.ext
  ext ⟨z, x⟩
  change (∃ w : kernelObj f, (z, w.1) ∈ g.rel ∧ w.1 = x) ↔ (z, x) ∈ g.rel
  constructor
  · rintro ⟨w, h, rfl⟩
    exact h
  · intro hx
    exact ⟨⟨x, mem_kernelObj_of_comp_eq_zero hg hx⟩, hx, rfl⟩

/-- The kernel fork formed from the inclusion of the elements with no successor. -/
def kernelCone (f : X ⟶ Y) : KernelFork f := KernelFork.ofι (kernelι f) (kernelι_comp f)

/-- The relational kernel fork is limiting; uniqueness follows from its isometric inclusion. -/
def kernelIsLimit (f : X ⟶ Y) : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι' (kernelι f) (kernelι_comp f) fun g hg ↦
    ⟨kernelLift f g, kernelLift_comp f g hg⟩

/-- The elements with no successor and their inclusion form a dagger kernel, as in Example 2.47. -/
def daggerKernel (f : X ⟶ Y) : DaggerKernel f where
  fork := kernelCone f
  isLimit := kernelIsLimit f
  isIsometry := inferInstanceAs (IsIsometry (kernelι f))

/-- Every relation has a dagger kernel, including relations on infinite sets. -/
instance hasDaggerKernels : HasDaggerKernels RelCat.{u} where
  hasDaggerKernel f := ⟨⟨daggerKernel f⟩⟩

end CategoryTheory.RelCat
