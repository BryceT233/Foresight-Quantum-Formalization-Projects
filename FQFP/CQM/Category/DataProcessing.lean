/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.Postprocessing
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Data processing on states

For a functor describing the action of processes on states, a distinguishability
measure satisfies data processing when a common process cannot increase it.
The postprocessing order then compares two experiments on the same pair of inputs.
-/

@[expose] public section

open CategoryTheory

namespace CQM

variable {C : Type*} [Category* C] {R : Type*} [Preorder R]

/-- A two-state quantity which decreases under common processing. Use the dual order
for a similarity such as fidelity. -/
def SatisfiesDataProcessing (F : C ⥤ Type*) (q : ∀ X, F.obj X → F.obj X → R) : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y) (s t : F.obj X), q Y (F.map f s) (F.map f t) ≤ q X s t

variable {F : C ⥤ Type*} {q : ∀ X, F.obj X → F.obj X → R}

/-- Postprocessing can only decrease output distinguishability, even when the two
experiments have different output objects. -/
lemma SatisfiesDataProcessing.le_of_isDegradableTo (hq : SatisfiesDataProcessing F q)
    {S X Y : C} {f : S ⟶ X} {g : S ⟶ Y} (h : IsDegradableTo f g) (s t : F.obj S) :
    q Y (F.map g s) (F.map g t) ≤ q X (F.map f s) (F.map f t) := by
  obtain ⟨d, rfl⟩ := h
  simpa only [F.map_comp, types_comp_apply] using hq d (F.map f s) (F.map f t)

/-- A common recovery for these two states forces equality in data processing. -/
lemma SatisfiesDataProcessing.eq_of_recovery {T : Type*} [PartialOrder T]
    {q : ∀ X, F.obj X → F.obj X → T} (hq : SatisfiesDataProcessing F q)
    {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) {s t : F.obj X}
    (hs : F.map g (F.map f s) = s) (ht : F.map g (F.map f t) = t) :
    q Y (F.map f s) (F.map f t) = q X s t := by
  refine le_antisymm (hq f s t) ?_
  simpa only [hs, ht] using hq g (F.map f s) (F.map f t)

end CQM
