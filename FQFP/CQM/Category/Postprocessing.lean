/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.SemiCartesian

/-!
# Postprocessing and joint processes

A process simulates another if a second process on its output realizes the target.
In a semicartesian category joint processes have two marginals. Postprocessing these
marginals independently preserves compatibility. Taking two identical marginals gives
the channel version of the broadcasting equations in §7.3.2 of *Categorical Quantum Mechanics*.
-/

@[expose] public section

open CategoryTheory MonoidalCategory SemiCartesianMonoidalCategory

namespace CQM

variable {C : Type*} [Category* C] {S X Y Z : C}

/-- The second process can be obtained by processing the output of the first. -/
def IsDegradableTo (f : S ⟶ X) (g : S ⟶ Y) : Prop := ∃ d : X ⟶ Y, f ≫ d = g

namespace IsDegradableTo

lemma refl (f : S ⟶ X) : IsDegradableTo f f := ⟨𝟙 X, Category.comp_id _⟩

lemma trans {f : S ⟶ X} {g : S ⟶ Y} {k : S ⟶ Z}
    (h : IsDegradableTo f g) (h' : IsDegradableTo g k) : IsDegradableTo f k := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨e, rfl⟩ := h'
  exact ⟨d ≫ e, (Category.assoc ..).symm⟩

/-- Apply a common preparation before the processes being compared. -/
lemma precomp {f : S ⟶ X} {g : S ⟶ Y} (h : IsDegradableTo f g) (a : Z ⟶ S) :
    IsDegradableTo (a ≫ f) (a ≫ g) := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨d, Category.assoc ..⟩

lemma tensor [MonoidalCategory C] {T X' Y' : C} {f : S ⟶ X} {g : S ⟶ Y}
    {f' : T ⟶ X'} {g' : T ⟶ Y'} (h : IsDegradableTo f g) (h' : IsDegradableTo f' g') :
    IsDegradableTo (f ⊗ₘ f') (g ⊗ₘ g') := by
  obtain ⟨d, rfl⟩ := h
  obtain ⟨e, rfl⟩ := h'
  exact ⟨d ⊗ₘ e, tensorHom_comp_tensorHom ..⟩

end IsDegradableTo

lemma isDegradableTo_of_id (f : S ⟶ X) : IsDegradableTo (𝟙 S) f := ⟨f, Category.id_comp _⟩

variable [SemiCartesianMonoidalCategory C]

/-- The two processes are marginals of one joint process on the same input. -/
def Compatible (f : S ⟶ X) (g : S ⟶ Y) : Prop :=
  ∃ j : S ⟶ X ⊗ Y, j ≫ fst X Y = f ∧ j ≫ snd X Y = g

/-- Any process into a tensor realizes its two marginals jointly. -/
lemma compatible_marginals (j : S ⟶ X ⊗ Y) : Compatible (j ≫ fst X Y) (j ≫ snd X Y) :=
  ⟨j, rfl, rfl⟩

/-- Exchanging the outputs of a joint process exchanges its marginals. -/
lemma Compatible.symm [BraidedCategory C] {f : S ⟶ X} {g : S ⟶ Y} (h : Compatible f g) :
    Compatible g f := by
  obtain ⟨j, rfl, rfl⟩ := h
  exact ⟨j ≫ (β_ X Y).hom, by rw [Category.assoc, braiding_hom_fst],
    by rw [Category.assoc, braiding_hom_snd]⟩

/-- Independent postprocessing of two compatible outputs preserves compatibility. -/
lemma Compatible.postprocess {X' Y' : C} {f : S ⟶ X} {g : S ⟶ Y}
    {f' : S ⟶ X'} {g' : S ⟶ Y'} (h : Compatible f g)
    (hf : IsDegradableTo f f') (hg : IsDegradableTo g g') : Compatible f' g' := by
  obtain ⟨j, rfl, rfl⟩ := h
  obtain ⟨d, rfl⟩ := hf
  obtain ⟨e, rfl⟩ := hg
  exact ⟨j ≫ (d ⊗ₘ e), by rw [Category.assoc, tensorHom_fst, Category.assoc],
    by rw [Category.assoc, tensorHom_snd, Category.assoc]⟩

/-- Discarding the output and preparing a fixed state is always a postprocessing. -/
lemma isDegradableTo_toUnit_comp (f : S ⟶ X) (s : 𝟙_ C ⟶ Y) :
    IsDegradableTo f (toUnit S ≫ s) :=
  ⟨toUnit X ≫ s, by rw [← Category.assoc, comp_toUnit]⟩

end CQM
