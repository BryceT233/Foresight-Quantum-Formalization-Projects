/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.Discarding
public import FQFP.CategoryTheory.Semiadditive.Basic

/-!
# Finite instruments and outcome effects

In a semiadditive process category, summing branches forgets the observed outcome.
A family is an instrument when this sum preserves discarding. For effects this gives
the normalization of a POVM (Heunen and Vicary, Definitions 0.69–0.70 and Example 7.8).
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace CQM.Discarding

variable {C : Type*} [Category* C] [MonoidalCategory C] [Semiadditive C]
variable (D : Discarding C) {X Y Z : C} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A finite instrument has causal total process after forgetting its outcome. -/
def IsInstrument (f : ι → (X ⟶ Y)) : Prop := D.IsCausal (∑ i, f i)

/-- Normalization can be checked on the effects obtained by discarding each output. -/
lemma isInstrument_iff_sum_effect (f : ι → (X ⟶ Y)) :
    D.IsInstrument f ↔ ∑ i, f i ≫ D.discard Y = D.discard X := by
  rw [IsInstrument, IsCausal, Semiadditive.sum_comp]

/-- A family of effects is a measurement exactly when the effects sum to discarding. -/
lemma isInstrument_effect_iff (e : ι → (X ⟶ 𝟙_ C)) :
    D.IsInstrument e ↔ ∑ i, e i = D.discard X :=
  D.isCausal_effect_iff _

variable {D}

/-- Running a causal process before a finite instrument preserves normalization. -/
lemma IsInstrument.precomp {g : ι → (Y ⟶ Z)} (hg : D.IsInstrument g)
    {f : X ⟶ Y} (hf : D.IsCausal f) : D.IsInstrument (fun i => f ≫ g i) := by
  rw [IsInstrument, ← Semiadditive.comp_sum]
  exact hf.comp hg

/-- Postprocessing may depend on the outcome, including preparation after a measurement. -/
lemma IsInstrument.postprocess {f : ι → (X ⟶ Y)} (hf : D.IsInstrument f)
    {g : ι → (Y ⟶ Z)} (hg : ∀ i, D.IsCausal (g i)) :
    D.IsInstrument (fun i => f i ≫ g i) := by
  rw [D.isInstrument_iff_sum_effect] at hf ⊢
  simpa only [fun i => (hg i).comp_discard_eq (f i)] using hf

/-- Sequential instruments may choose the second experiment from the first outcome. -/
lemma IsInstrument.bind {f : ι → (X ⟶ Y)} (hf : D.IsInstrument f)
    {g : ι → κ → (Y ⟶ Z)} (hg : ∀ i, D.IsInstrument (g i)) :
    D.IsInstrument (fun p : ι × κ => f p.1 ≫ g p.1 p.2) := by
  unfold IsInstrument
  rw [Semiadditive.sum_prod_comp]
  exact hf.postprocess hg

end CQM.Discarding
