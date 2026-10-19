/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.RelCat.Biproducts
public import FQFP.CQM.Category.Measurement

/-!
# Relational measurement semantics

States and effects in `RelCat` are subsets, and a Born scalar is true exactly when
the state and effect subsets intersect. Complete effect families cover the object;
disjoint effect families have nonempty, pairwise disjoint blocks.

## Main definitions

* `stateEquivSet`, `effectEquivSet`: states and effects as subsets.
* `EffectSetsFormPartition`: coverage by nonempty pairwise disjoint effect subsets.

## Main results

* `isIsometry_state_iff_nonempty`: relational unit states are nonempty subsets.
* `complete_disjoint_iff_partition`: **Example 2.54**.
* `isIsometry_dagger_sum_lift_of_partition`: the disjointness theorem applied to a partition.
* `sum_probability_eq_one_of_cover`: Boolean normalization from coverage, without inverses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DaggerCategory

namespace CategoryTheory.RelCat

universe u

variable {X : RelCat.{u}}

/-- The subset denoted by a relational state. -/
def stateSet (a : State X) : Set X := {x | (PUnit.unit, x) ∈ a.rel}

/-- The subset denoted by a relational effect. -/
def effectSet (x : Effect X) : Set X := {a | (a, PUnit.unit) ∈ x.rel}

/-- Relational states are precisely subsets of the object. -/
def stateEquivSet : State X ≃ Set X where
  toFun := stateSet
  invFun s := .ofRel {p | s p.2}
  left_inv a := by
    apply Hom.ext
    ext ⟨p, x⟩
    cases p
    rfl
  right_inv _ := rfl

/-- Relational effects are precisely subsets of the object. -/
def effectEquivSet : Effect X ≃ Set X where
  toFun := effectSet
  invFun s := .ofRel {p | s p.1}
  left_inv x := by
    apply Hom.ext
    ext ⟨a, p⟩
    cases p
    rfl
  right_inv _ := rfl

/-- An isometric relational state is exactly a nonempty subset. -/
theorem isIsometry_state_iff_nonempty (a : State X) :
    IsIsometry a ↔ ∃ z : X, stateSet a z := by
  constructor
  · intro ha
    have hmem : (PUnit.unit, PUnit.unit) ∈ (a ≫ a†).rel := by
      rw [ha.comp_dagger_eq_id]
      rfl
    change (∃ z : X, stateSet a z ∧ stateSet a z) at hmem
    obtain ⟨z, hz, _⟩ := hmem
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨?_⟩
    apply Hom.ext
    ext ⟨p, q⟩
    cases p
    cases q
    change (∃ w : X, stateSet a w ∧ stateSet a w) ↔ PUnit.unit = PUnit.unit
    exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨z, hz, hz⟩⟩

/-- A relational Born scalar holds exactly when the state meets the effect. -/
theorem probability_nonempty_intersection (a : State X) (x : Effect X) :
    (PUnit.unit, PUnit.unit) ∈ (probability a x).asHom.rel ↔
      ∃ z : X, stateSet a z ∧ effectSet x z := by
  change (∃ z : X, (PUnit.unit, z) ∈ a.rel ∧
    ∃ p : PUnit, (z, p) ∈ x.rel ∧
      ∃ w : X, (w, p) ∈ x.rel ∧ (PUnit.unit, w) ∈ a.rel) ↔
      ∃ z : X, (PUnit.unit, z) ∈ a.rel ∧ (z, PUnit.unit) ∈ x.rel
  grind

/-- A family of relational effects is complete exactly when its subsets cover the object. -/
theorem complete_iff_cover {ι : Type*} (x : ι → Effect X) :
    Effect.Complete x ↔ ∀ z : X, ∃ i : ι, effectSet (x i) z := by
  constructor
  · intro hc z
    by_contra hn
    have hnone : ∀ i : ι, ¬ effectSet (x i) z := by
      simpa using hn
    let f : State X := .ofRel {p | p.2 = z}
    have hf : ∀ i, f ≫ x i = 0 := by
      intro i
      apply Hom.ext
      ext ⟨p, q⟩
      cases p
      cases q
      change (∃ w : (X : Type u), w = z ∧ effectSet (x i) w) ↔ False
      constructor
      · rintro ⟨w, rfl, hw⟩
        exact hnone i hw
      · exact False.elim
    have hzero := hc f hf
    have hz := congrArg (fun r : SetRel PUnit X ↦ (PUnit.unit, z) ∈ r)
      (congrArg Hom.rel hzero)
    rw [rel_zero] at hz; revert hz
    simpa [f] using Eq.refl z
  · intro hcover Y f hf
    apply Hom.ext
    ext ⟨y, z⟩
    have hzero : ∀ i, (y, PUnit.unit) ∉ (f ≫ x i).rel := by
      intro i
      have hi := congrArg (fun r : SetRel Y (𝟙_ RelCat) ↦ (y, PUnit.unit) ∈ r)
        (congrArg Hom.rel (hf i))
      rw [rel_zero] at hi
      change _ = False at hi
      exact fun h ↦ Eq.mp hi h
    change (y, z) ∈ f.rel ↔ False
    constructor
    · intro hyz
      obtain ⟨i, hi⟩ := hcover z
      apply hzero i
      exact ⟨z, hyz, hi⟩
    · intro h
      exact False.elim h

/-- A dagger-effect composite is true exactly when the two effect subsets meet. -/
theorem effect_dagger_comp_effect_iff (x y : Effect X) :
    (PUnit.unit, PUnit.unit) ∈ (x† ≫ y).rel ↔
      ∃ z : X, effectSet x z ∧ effectSet y z := by
  change (∃ z : X, (z, PUnit.unit) ∈ x.rel ∧
    (z, PUnit.unit) ∈ y.rel) ↔ _
  rfl

/-- The relational dagger composite is identity exactly for a nonempty effect subset. -/
theorem effect_dagger_comp_self_eq_id_iff (x : Effect X) :
    x† ≫ x = 𝟙 (𝟙_ RelCat.{u}) ↔ ∃ z : X, effectSet x z := by
  constructor
  · intro h
    have : (PUnit.unit, PUnit.unit) ∈ (x† ≫ x).rel := by
      rw [h]
      rfl
    obtain ⟨z, hz, _⟩ := (effect_dagger_comp_effect_iff x x).1 this
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    apply Hom.ext
    ext ⟨p, q⟩
    cases p
    cases q
    change (∃ w : X, effectSet x w ∧ effectSet x w) ↔
      PUnit.unit = PUnit.unit
    exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨z, hz, hz⟩⟩

/-- The relational dagger composite is zero exactly for disjoint effect subsets. -/
theorem effect_dagger_comp_effect_eq_zero_iff (x y : Effect X) :
    x† ≫ y = 0 ↔ ∀ z : X, ¬ (effectSet x z ∧ effectSet y z) := by
  constructor
  · intro h z hz
    have hh := (effect_dagger_comp_effect_iff x y).2 ⟨z, hz⟩
    rw [h] at hh
    exact hh
  · intro h
    ext ⟨p, q⟩
    cases p
    cases q
    change (∃ z : X, effectSet x z ∧ effectSet y z) ↔ False
    exact ⟨fun ⟨z, hz⟩ ↦ h z hz, False.elim⟩

/-- Relational disjointness means nonempty, pairwise disjoint effect subsets. -/
theorem disjoint_iff_nonempty_pairwise {ι : Type*} (x : ι → Effect X) :
    Effect.Disjoint x ↔
      (∀ i, ∃ z : X, effectSet (x i) z) ∧
      _root_.Pairwise (fun i j ↦ ∀ z : X,
        ¬ (effectSet (x i) z ∧ effectSet (x j) z)) := by
  constructor
  · rintro ⟨hself, hother⟩
    refine ⟨fun i ↦ (effect_dagger_comp_self_eq_id_iff (x i)).1 (hself i), ?_⟩
    intro i j hij z hz
    exact (effect_dagger_comp_effect_eq_zero_iff (x j) (x i)).1
      (hother hij) z ⟨hz.2, hz.1⟩
  · rintro ⟨hself, hother⟩
    refine ⟨fun i ↦ (effect_dagger_comp_self_eq_id_iff (x i)).2 (hself i), ?_⟩
    intro i j hij
    apply (effect_dagger_comp_effect_eq_zero_iff (x j) (x i)).2
    intro z hz
    exact hother hij z ⟨hz.2, hz.1⟩

/-- The three set-theoretic conditions defining a partition of the effect subsets. -/
def EffectSetsFormPartition {ι : Type*} (x : ι → Effect X) : Prop :=
  (∀ z : X, ∃ i : ι, effectSet (x i) z) ∧
  (∀ i, ∃ z : X, effectSet (x i) z) ∧
  _root_.Pairwise (fun i j ↦ ∀ z : X,
    ¬ (effectSet (x i) z ∧ effectSet (x j) z))

/-- Example 2.54: complete, disjoint effects are exactly relational partitions. -/
theorem complete_disjoint_iff_partition {ι : Type*} (x : ι → Effect X) :
    Effect.Complete x ∧ Effect.Disjoint x ↔ EffectSetsFormPartition x := by
  rw [complete_iff_cover, disjoint_iff_nonempty_pairwise]
  rfl

/-- A partition's relational measurement lift has an isometric dagger.
This uses the explicit disjoint-union witness and needs no additive inverses. -/
theorem isIsometry_dagger_sum_lift_of_partition {ι : Type*} [Small.{u} ι]
    (x : ι → Effect X) (hx : EffectSetsFormPartition x) :
    IsIsometry ((sumBicone (fun _ : ι ↦ 𝟙_ RelCat.{u})).lift
      (sumBiconeIsBilimit _) x)† :=
  (Effect.disjoint_iff_isIsometry_dagger_lift
    (sumBicone (fun _ : ι ↦ 𝟙_ RelCat.{u})) (sumBiconeIsBilimit _) x).1
      ((complete_disjoint_iff_partition x).2 hx).2

/-- Membership in a finite union of relational morphisms. -/
private theorem mem_rel_sum {ι : Type*} {Y Z : RelCat.{u}}
    (s : Finset ι) (f : ι → (Y ⟶ Z)) (y : Y) (z : Z) :
    (y, z) ∈ (∑ i ∈ s, f i).rel ↔ ∃ i ∈ s, (y, z) ∈ (f i).rel := by
  classical
  induction s using Finset.induction with
  | empty => simp [rel_zero]
  | @insert i s hi ih =>
      simp [Finset.sum_insert hi, rel_add, ih, Finset.mem_insert]

/-- Boolean normalization for finite relational measurements, using coverage directly. -/
theorem sum_probability_eq_one_of_cover {ι : Type*} [Fintype ι]
    (x : ι → Effect X) (hx : Effect.Complete x)
    (a : State X) [IsIsometry a] : ∑ i, probability a (x i) = 1 := by
  apply End.ext
  rw [Semiadditive.end_sum_asHom]
  apply Hom.ext
  ext ⟨p, q⟩
  cases p
  cases q
  rw [mem_rel_sum]
  change (∃ i ∈ Finset.univ,
    (PUnit.unit, PUnit.unit) ∈ (probability a (x i)).asHom.rel) ↔
    PUnit.unit = PUnit.unit
  constructor; · tauto
  · intro _
    obtain ⟨z, hz⟩ := (isIsometry_state_iff_nonempty a).1 inferInstance
    obtain ⟨i, hi⟩ := (complete_iff_cover x).1 hx z
    exact ⟨i, Finset.mem_univ i,
      (probability_nonempty_intersection a (x i)).2 ⟨z, hz, hi⟩⟩

end CategoryTheory.RelCat
