/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Monoidal.SemiCartesian
public import FQFP.CategoryTheory.Monoidal.State
public import Mathlib.CategoryTheory.Generator.Basic

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

/-- A specified joint process realizes the two given marginals. -/
def HasMarginals (j : S ⟶ X ⊗ Y) (f : S ⟶ X) (g : S ⟶ Y) : Prop :=
  j ≫ fst X Y = f ∧ j ≫ snd X Y = g

/-- Running an independent process alongside a joint realization carries its output
with the second marginal. Taking the independent process to be an identity gives
the reference extension used in §7.2.2 of *Categorical Quantum Mechanics*. -/
lemma HasMarginals.tensorRight {j : S ⟶ X ⊗ Y} {f : S ⟶ X} {g : S ⟶ Y}
    (h : HasMarginals j f g) {R R' : C} (k : R ⟶ R') :
    HasMarginals ((j ⊗ₘ k) ≫ (α_ X Y R').hom) (fst S R ≫ f) (g ⊗ₘ k) :=
  ⟨(tensorHom_associator_hom_fst j k).trans (congrArg (fst S R ≫ ·) h.1),
    (tensorHom_associator_hom_snd j k).trans (congrArg (· ⊗ₘ k) h.2)⟩

/-- Exchanging the outputs of a specified joint realization exchanges its marginals. -/
lemma HasMarginals.swap [BraidedCategory C] {j : S ⟶ X ⊗ Y} {f : S ⟶ X} {g : S ⟶ Y}
    (h : HasMarginals j f g) : HasMarginals (j ≫ (β_ X Y).hom) g f :=
  ⟨by rw [Category.assoc, braiding_hom_fst, h.2],
    by rw [Category.assoc, braiding_hom_snd, h.1]⟩

/-- The two processes are marginals of one joint process on the same input. -/
def Compatible (f : S ⟶ X) (g : S ⟶ Y) : Prop :=
  ∃ j : S ⟶ X ⊗ Y, HasMarginals j f g

/-- Any process into a tensor realizes its two marginals jointly. -/
lemma compatible_marginals (j : S ⟶ X ⊗ Y) : Compatible (j ≫ fst X Y) (j ≫ snd X Y) :=
  ⟨j, rfl, rfl⟩

/-- A specified process broadcasts an input preparation when either marginal recovers it.
For the identity input these are the broadcasting equations of Definition 7.31. -/
def Broadcasts (d : X ⟶ X ⊗ X) (f : S ⟶ X) : Prop :=
  f ≫ d ≫ fst X X = f ∧ f ≫ d ≫ snd X X = f

/-- A copier for the outputs of a process also works after any input preparation. -/
lemma Broadcasts.precomp {d : X ⟶ X ⊗ X} {f : S ⟶ X} (h : Broadcasts d f) (a : Z ⟶ S) :
    Broadcasts d (a ≫ f) := by
  simp [Broadcasts, Category.assoc, h.1, h.2]

/-- Broadcasting a preparation supplies a joint realization of two copies of its marginal. -/
lemma Broadcasts.compatible {d : X ⟶ X ⊗ X} {f : S ⟶ X} (h : Broadcasts d f) :
    Compatible f f :=
  ⟨f ≫ d, (Category.assoc ..).trans h.1, (Category.assoc ..).trans h.2⟩

/-- An object admits a single process broadcasting its identity (Definition 7.31). -/
def IsBroadcastable (X : C) : Prop := ∃ d, Broadcasts d (𝟙 X)

/-- A joint extension of two identity processes is precisely a universal broadcaster. -/
lemma isBroadcastable_iff_compatible_id (X : C) :
    IsBroadcastable X ↔ Compatible (𝟙 X) (𝟙 X) := by
  simp only [IsBroadcastable, Broadcasts, Compatible, HasMarginals, Category.id_comp]

/-- In a well-pointed category (Definition 1.12), broadcasting can be tested on states. -/
lemma broadcasts_id_iff_forall_state (h : IsSeparator (𝟙_ C)) (d : X ⟶ X ⊗ X) :
    Broadcasts d (𝟙 X) ↔ ∀ s : State X, Broadcasts d s := by
  constructor
  · intro hd s
    simpa only [Category.comp_id] using hd.precomp s
  · intro hs
    simp only [Broadcasts, Category.id_comp]
    exact ⟨h.def _ _ (fun s => ((hs s).1).trans (Category.comp_id s).symm),
      h.def _ _ (fun s => ((hs s).2).trans (Category.comp_id s).symm)⟩

/-- A symmetric splitting broadcasts precisely the inputs fixed by its first marginal. -/
lemma broadcasts_iff_of_swap [BraidedCategory C] (d : X ⟶ X ⊗ X)
    (hd : d ≫ (β_ X X).hom = d) (f : S ⟶ X) :
    Broadcasts d f ↔ f ≫ d ≫ fst X X = f := by
  rw [Broadcasts, ← comp_fst_eq_comp_snd_of_swap d hd, and_self]

/-- Exchanging the outputs of a joint process exchanges its marginals. -/
lemma Compatible.symm [BraidedCategory C] {f : S ⟶ X} {g : S ⟶ Y} (h : Compatible f g) :
    Compatible g f := by
  obtain ⟨j, hj⟩ := h
  exact ⟨_, hj.swap⟩

/-- Independent postprocessing of two compatible outputs preserves compatibility. -/
lemma Compatible.postprocess {X' Y' : C} {f : S ⟶ X} {g : S ⟶ Y}
    {f' : S ⟶ X'} {g' : S ⟶ Y'} (h : Compatible f g)
    (hf : IsDegradableTo f f') (hg : IsDegradableTo g g') : Compatible f' g' := by
  obtain ⟨j, rfl, rfl⟩ := h
  obtain ⟨d, rfl⟩ := hf
  obtain ⟨e, rfl⟩ := hg
  exact ⟨j ≫ (d ⊗ₘ e), by rw [Category.assoc, tensorHom_fst, Category.assoc],
    by rw [Category.assoc, tensorHom_snd, Category.assoc]⟩

/-- Any two processes on a broadcastable input have a joint realization. -/
lemma IsBroadcastable.compatible {S : C} (h : IsBroadcastable S) (f : S ⟶ X) (g : S ⟶ Y) :
    Compatible f g :=
  ((isBroadcastable_iff_compatible_id S).mp h).postprocess
    (isDegradableTo_of_id f) (isDegradableTo_of_id g)

/-- A fixed state can be prepared alongside any process. -/
lemma compatible_toUnit_comp (f : S ⟶ X) (s : 𝟙_ C ⟶ Y) :
    Compatible f (toUnit S ≫ s) := by
  have h : Compatible f (toUnit S) :=
    ⟨f ≫ (ρ_ X).inv, by simp [fst_def], toUnit_unique _ _⟩
  exact h.postprocess (.refl f) ⟨s, rfl⟩

/-- Discarding the output and preparing a fixed state is always a postprocessing. -/
lemma isDegradableTo_toUnit_comp (f : S ⟶ X) (s : 𝟙_ C ⟶ Y) :
    IsDegradableTo f (toUnit S ≫ s) :=
  ⟨toUnit X ≫ s, by rw [← Category.assoc, comp_toUnit]⟩

end CQM
