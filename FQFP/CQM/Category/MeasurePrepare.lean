/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Monoidal.State
public import FQFP.CategoryTheory.Semiadditive.Basic

/-!
# Measurement followed by preparation

In §0.3.5 of *Categorical Quantum Mechanics*, preparing and reading a basis label
gives the Kronecker delta (0.41). Consequently a register of distinguishable
preparations lets one recover each effect of the measurement that wrote it.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CQM

variable {C : Type*} [Category* C] [MonoidalCategory C] [Semiadditive C]
  {X Y Z : C} {ι : Type*} [Fintype ι]

/-- Measure an effect family, prepare its associated states, and forget the outcome. -/
def measurePrepare (e : ι → Effect X) (s : ι → State Y) : X ⟶ Y :=
  ∑ i, e i ≫ s i

/-- Further processing acts on each prepared state. -/
lemma measurePrepare_comp (e : ι → Effect X) (s : ι → State Y) (g : Y ⟶ Z) :
    measurePrepare e s ≫ g = measurePrepare e (fun i => s i ≫ g) := by
  simp only [measurePrepare, Semiadditive.sum_comp, Category.assoc]

/-- Processing before the measurement pulls back each outcome effect. -/
lemma comp_measurePrepare (g : Z ⟶ X) (e : ι → Effect X) (s : ι → State Y) :
    g ≫ measurePrepare e s = measurePrepare (fun i => g ≫ e i) s := by
  simp only [measurePrepare, Semiadditive.comp_sum, Category.assoc]

/-- Reading one perfectly distinguishable label of a prepared register recovers
its original measurement effect. Only the response to this label is required. -/
lemma measurePrepare_comp_readout [DecidableEq ι] (e : ι → Effect X) (s : ι → State Y)
    (j : ι) (r : Effect Y) (hr : ∀ i, s i ≫ r = if i = j then 𝟙 _ else 0) :
    measurePrepare e s ≫ r = e j := by
  apply Semiadditive.sum_comp_retraction (Y := fun _ => 𝟙_ C) e s j r
  · exact (hr j).trans (ite_eq_left rfl)
  · intro i hij
    exact (hr i).trans (ite_eq_right hij)

end CQM
