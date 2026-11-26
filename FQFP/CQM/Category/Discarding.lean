/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Dagger.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Discarding and causal processes

The unit and tensor laws for discarding are part of equation (7.19) in Heunen and Vicary's
*Categorical Quantum Mechanics* (2019 lecture notes). A process is causal if it preserves
discarding. When every process is causal, discarding is uniform in the sense of Definition
4.14. Proposition 4.15 identifies this condition with terminality of the tensor unit.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits DaggerCategory

namespace CQM

/-- A choice of discarding effects compatible with the tensor unit and tensor products. -/
structure Discarding (C : Type*) [Category* C] [MonoidalCategory C] where
  /-- Discard a system. -/
  discard (X : C) : X ⟶ 𝟙_ C
  /-- Discarding the unit has no effect. -/
  discard_unit : discard (𝟙_ C) = 𝟙 _
  /-- Discarding two systems independently discards their composite. -/
  discard_tensor (X Y : C) : discard (X ⊗ Y) = (discard X ⊗ₘ discard Y) ≫ (ρ_ (𝟙_ C)).hom

namespace Discarding

variable {C : Type*} [Category* C] [MonoidalCategory C] (D : Discarding C)

/-- A process is causal if discarding after it gives the original discarding effect. -/
def IsCausal {X Y : C} (f : X ⟶ Y) : Prop := f ≫ D.discard Y = D.discard X

lemma isCausal_id (X : C) : D.IsCausal (𝟙 X) := Category.id_comp _

variable {D} {X Y Z X' Y' : C}

/-- Causal postprocessing preserves the effect obtained by discarding the output. -/
lemma IsCausal.comp_discard_eq {g : Y ⟶ Z} (hg : D.IsCausal g) (f : X ⟶ Y) :
    (f ≫ g) ≫ D.discard Z = f ≫ D.discard Y :=
  (Category.assoc ..).trans (congrArg (f ≫ ·) hg)

lemma IsCausal.comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : D.IsCausal f) (hg : D.IsCausal g) :
    D.IsCausal (f ≫ g) := by
  exact (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) hg).trans hf)

lemma IsCausal.tensor {f : X ⟶ Y} {g : X' ⟶ Y'} (hf : D.IsCausal f) (hg : D.IsCausal g) :
    D.IsCausal (f ⊗ₘ g) := by
  rw [IsCausal, D.discard_tensor Y Y', D.discard_tensor X X',
    tensorHom_comp_tensorHom_assoc, hf, hg]

variable (D)

/-- The only causal effect on a system is its discarding effect. -/
lemma isCausal_effect_iff (e : X ⟶ 𝟙_ C) : D.IsCausal e ↔ e = D.discard X := by
  rw [IsCausal, D.discard_unit, Category.comp_id]

/-- A causal state has total weight equal to the unit scalar. -/
lemma isCausal_state_iff (s : 𝟙_ C ⟶ X) : D.IsCausal s ↔ s ≫ D.discard X = 𝟙 _ := by
  rw [IsCausal, D.discard_unit]

/-- Discard the right subsystem of a composite. -/
def discardRight (X Y : C) : X ⊗ Y ⟶ X := (𝟙 X ⊗ₘ D.discard Y) ≫ (ρ_ X).hom

/-- A local causal process on the discarded subsystem leaves the other marginal unchanged.
The process on the retained subsystem is arbitrary. -/
lemma tensor_comp_discardRight (f : X ⟶ Y) {g : X' ⟶ Y'} (hg : D.IsCausal g) :
    (f ⊗ₘ g) ≫ D.discardRight Y Y' = D.discardRight X X' ≫ f := by
  simp only [discardRight, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id]
  rw [hg, ← rightUnitor_naturality, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Category.id_comp, Category.comp_id]

/-- Uniform deleting means that discarding is natural with respect to every process. -/
def IsUniform : Prop := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), D.IsCausal f

/-- Proposition 4.15. Uniform deleting exhibits the tensor unit as terminal. -/
def isTerminalUnit (h : D.IsUniform) : IsTerminal (𝟙_ C) :=
  IsTerminal.ofUniqueHom D.discard fun _ e => (D.isCausal_effect_iff e).mp (h e)

/-- A terminal tensor unit supplies the uniform discarding effects of Proposition 4.15. -/
def ofIsTerminal (t : IsTerminal (𝟙_ C)) : Discarding C where
  discard := t.from
  discard_unit := t.from_self
  discard_tensor _ _ := t.hom_ext _ _

lemma isUniform_iff : D.IsUniform ↔ Nonempty (IsTerminal (𝟙_ C)) :=
  ⟨fun h => ⟨D.isTerminalUnit h⟩, fun ⟨t⟩ _ _ _ => t.hom_ext _ _⟩

/-- The no-deleting theorem (4.20). With left duals, uniform deleting forces parallel
morphisms to coincide, since their conames are effects on the same object. -/
theorem subsingleton_hom_of_isUniform (h : D.IsUniform) (X Y : C) [HasLeftDual Y] :
    Subsingleton (X ⟶ Y) := by
  let e := tensorRightHomEquiv X (ᘁY) Y (𝟙_ C)
  refine ⟨fun f g => (cancel_mono (λ_ Y).inv).mp (e.symm.injective ?_)⟩
  exact (D.isTerminalUnit h).hom_ext _ _

variable {P : Type*} [Category* P] [DaggerCategory P]

/-- The separation axiom (7.20) for a functor interpreting pure processes. -/
def SeparatesPure (F : P ⥤ C) : Prop :=
  ∀ ⦃X Y Z : P⦄ (f : X ⟶ Y) (g : X ⟶ Z),
    F.map f ≫ D.discard (F.obj Y) = F.map g ≫ D.discard (F.obj Z) ↔ f ≫ f† = g ≫ g†

/-- Under environment separation, the causal pure processes are precisely the isometries. -/
theorem SeparatesPure.isCausal_map_iff {D : Discarding C} {F : P ⥤ C} (h : D.SeparatesPure F)
    {X Y : P} (f : X ⟶ Y) : D.IsCausal (F.map f) ↔ IsIsometry f := by
  simpa only [IsCausal, F.map_id, Category.id_comp, dagger_id, isIsometry_iff] using h f (𝟙 X)

end Discarding

end CQM
