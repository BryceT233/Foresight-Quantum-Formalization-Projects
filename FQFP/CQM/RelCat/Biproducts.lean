/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.RelCat.Semiadditive
public import FQFP.CQM.RelCat.Dagger
public import FQFP.CQM.Category.DaggerBiproduct
public import Mathlib.Basic.UnivLE

/-!
# Disjoint-union dagger biproducts of relations

A small tagged disjoint union is both a product and a coproduct in `RelCat`.
Its injections are converse to its projections. The index universe is independent of
the object universe; a `Small` index ensures that the union fits in the latter.

## Main definitions

* `sumBicone`, `sumBiconeIsBilimit`: the explicit disjoint-union bilimit.
* `sumBinaryBicone`: its binary specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DaggerCategory

namespace CategoryTheory.RelCat

noncomputable section

universe u v

variable {ι : Type v} [Small.{u} ι] (F : ι → RelCat.{u})

/-- A small index and small fibers give a small tagged union. -/
local instance : Small.{u} (Σ i, F i) := by
  let : ∀ i, Small.{u} (F i) := fun i ↦ small_self (F i)
  exact small_sigma (fun i ↦ (F i : Type u))

/-- A small representative of the tagged disjoint union. -/
def sumSpace : Type u := Shrink.{u} (Σ i, F i)

/-- Tags and elements identify the small representative with the full disjoint union. -/
def sumEquiv : (Σ i, F i) ≃ sumSpace F := equivShrink _

/-- The tagged disjoint-union bicone in the category of relations. -/
def sumBicone : Bicone (C := RelCat.{u}) F where
  pt := sumSpace F
  π i := .ofRel {p | p.1 = sumEquiv F ⟨i, p.2⟩}
  ι i := .ofRel {p | p.2 = sumEquiv F ⟨i, p.1⟩}
  ι_π i j := by
    classical
    split_ifs with hij
    · subst j
      apply Hom.ext
      ext ⟨x, y⟩
      change (∃ s, s = sumEquiv F ⟨i, x⟩ ∧ s = sumEquiv F ⟨i, y⟩) ↔ x = y
      simp only [exists_eq_left, Equiv.apply_eq_iff_eq]
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl
    · apply Hom.ext
      ext ⟨x, y⟩
      rw [rel_zero]
      change (∃ s, s = sumEquiv F ⟨i, x⟩ ∧ s = sumEquiv F ⟨j, y⟩) ↔ False
      simp only [exists_eq_left, Equiv.apply_eq_iff_eq, iff_false]
      exact fun h ↦ hij (congrArg Sigma.fst h)

/-- Injections and projections of the relational sum are converse. -/
instance sumBicone_isDagger : (sumBicone F).IsDagger where
  dagger_ι i := by
    apply Hom.ext
    ext ⟨s, x⟩
    rfl

/-- The disjoint-union bicone has both relational universal properties. -/
def sumBiconeIsBilimit : (sumBicone F).IsBilimit where
  isLimit := Fan.IsLimit.mk (sumBicone F).toCone
    (fun s ↦ .ofRel {p | (p.1, ((sumEquiv F).symm p.2).2) ∈
      (s.proj ((sumEquiv F).symm p.2).1).rel})
    (by
      intro s i
      apply Hom.ext
      ext ⟨x, y⟩
      change (∃ t, (x, ((sumEquiv F).symm t).2) ∈
        (s.proj ((sumEquiv F).symm t).1).rel ∧ t = sumEquiv F ⟨i, y⟩) ↔ _
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [(sumEquiv F).symm_apply_apply] at ht
        exact ht
      · intro h
        refine ⟨sumEquiv F ⟨i, y⟩, ?_, rfl⟩
        rw [(sumEquiv F).symm_apply_apply]
        exact h)
    (by
      intro s m hm
      apply Hom.ext
      ext ⟨x, t⟩
      obtain ⟨⟨i, y⟩, rfl⟩ := (sumEquiv F).surjective t
      have hi := congrArg Hom.rel (hm i)
      have hii := congrArg (fun r : SetRel s.pt (F i) ↦ (x, y) ∈ r) hi
      change ((∃ t, (x, t) ∈ m.rel ∧ t = sumEquiv F ⟨i, y⟩) =
        ((x, y) ∈ (s.proj i).rel)) at hii
      change ((x, sumEquiv F ⟨i, y⟩) ∈ m.rel ↔
        (x, ((sumEquiv F).symm (sumEquiv F ⟨i, y⟩)).2) ∈
          (s.proj ((sumEquiv F).symm (sumEquiv F ⟨i, y⟩)).1).rel)
      rw [(sumEquiv F).symm_apply_apply]
      constructor
      · intro h
        exact Eq.mp hii ⟨_, h, rfl⟩
      · intro h
        obtain ⟨t, ht, rfl⟩ := Eq.mpr hii h
        exact ht)
  isColimit := Cofan.IsColimit.mk (sumBicone F).toCocone
    (fun s ↦ .ofRel {p | (((sumEquiv F).symm p.1).2, p.2) ∈
      (s.inj ((sumEquiv F).symm p.1).1).rel})
    (by
      intro s i
      apply Hom.ext
      ext ⟨x, y⟩
      change (∃ t, t = sumEquiv F ⟨i, x⟩ ∧ (((sumEquiv F).symm t).2, y) ∈
        (s.inj ((sumEquiv F).symm t).1).rel) ↔ _
      constructor
      · rintro ⟨t, rfl, ht⟩
        rw [(sumEquiv F).symm_apply_apply] at ht
        exact ht
      · intro h
        refine ⟨sumEquiv F ⟨i, x⟩, rfl, ?_⟩
        rw [(sumEquiv F).symm_apply_apply]
        exact h)
    (by
      intro s m hm
      apply Hom.ext
      ext ⟨t, y⟩
      obtain ⟨⟨i, x⟩, rfl⟩ := (sumEquiv F).surjective t
      have hi := congrArg Hom.rel (hm i)
      have hii := congrArg (fun r : SetRel (F i) s.pt ↦ (x, y) ∈ r) hi
      change ((∃ t, t = sumEquiv F ⟨i, x⟩ ∧ (t, y) ∈ m.rel) =
        ((x, y) ∈ (s.inj i).rel)) at hii
      change ((sumEquiv F ⟨i, x⟩, y) ∈ m.rel ↔
        (((sumEquiv F).symm (sumEquiv F ⟨i, x⟩)).2, y) ∈
          (s.inj ((sumEquiv F).symm (sumEquiv F ⟨i, x⟩)).1).rel)
      rw [(sumEquiv F).symm_apply_apply]
      constructor
      · intro h
        exact Eq.mp hii ⟨_, rfl, h⟩
      · intro h
        obtain ⟨t, rfl, ht⟩ := Eq.mpr hii h
        exact ht)

/-- Every small family of relations has a normalized dagger biproduct. -/
instance hasDaggerBiproduct : HasDaggerBiproduct (C := RelCat.{u}) F where
  exists_daggerBiproduct := ⟨sumBicone F, sumBiconeIsBilimit F, inferInstance⟩

/-- Small disjoint unions supply Mathlib's finite-biproduct existence interface. -/
instance : HasFiniteBiproducts RelCat.{u} where
  out _ := ⟨fun F ↦ HasBiproduct.mk ⟨sumBicone F, sumBiconeIsBilimit F⟩⟩

/-- The binary disjoint-union bicone of two relations. -/
def sumBinaryBicone (X Y : RelCat.{u}) : BinaryBicone X Y :=
  (sumBicone (pairFunction X Y)).toBinaryBicone

/-- The binary disjoint union has both universal properties. -/
def sumBinaryBiconeIsBilimit (X Y : RelCat.{u}) : (sumBinaryBicone X Y).IsBilimit :=
  (Bicone.toBinaryBiconeIsBilimit _).symm (sumBiconeIsBilimit (pairFunction X Y))

/-- The binary injections and projections are converse. -/
instance sumBinaryBicone_isDagger (X Y : RelCat.{u}) : (sumBinaryBicone X Y).IsDagger where
  dagger_inl := Bicone.IsDagger.dagger_ι (b := sumBicone (pairFunction X Y)) WalkingPair.left
  dagger_inr := Bicone.IsDagger.dagger_ι (b := sumBicone (pairFunction X Y)) WalkingPair.right

/-- Every pair of relations has a normalized binary dagger biproduct. -/
instance hasDaggerBinaryBiproduct (X Y : RelCat.{u}) : HasDaggerBinaryBiproduct X Y where
  exists_daggerBinaryBiproduct :=
    ⟨sumBinaryBicone X Y, sumBinaryBiconeIsBilimit X Y, inferInstance⟩

/-- The binary disjoint unions supply Mathlib's binary-biproduct interface. -/
instance : HasBinaryBiproducts RelCat.{u} where
  has_binary_biproduct X Y :=
    HasBinaryBiproduct.mk ⟨sumBinaryBicone X Y, sumBinaryBiconeIsBilimit X Y⟩

/-- The empty disjoint union is a zero object. -/
theorem isZero_sumSpace [IsEmpty ι] : IsZero (C := RelCat.{u}) (sumSpace F) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply Hom.ext
  ext ⟨x, y⟩
  exact isEmptyElim ((sumEquiv F).symm x).1

/-- Empty disjoint union supplies the zero object of `RelCat`. -/
instance : HasZeroObject RelCat.{u} :=
  (isZero_sumSpace (fun i : Empty ↦ (isEmptyElim i : RelCat.{u}))).hasZeroObject

end

end CategoryTheory.RelCat
