/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.QuditCat.Dagger
public import FQFP.CategoryTheory.Dagger.Biproducts
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi

/-!
# Orthogonal direct sums of qudits

The orthogonal direct sum of a finite family of finite-dimensional Hilbert spaces is their
`L²` product `PiLp 2`. Its coordinate maps are adjoint, so it is a concrete normalized dagger
biproduct in `QuditCat`: the dagger-biproduct calculus of
`FQFP.CategoryTheory.Dagger.Biproducts` then applies to it without assuming anything about
Mathlib's independently chosen ordinary biproduct.

The empty family is included: `PiLp 2` over an empty index type is the zero space, so the
zero object of `QuditCat` is a biproduct of no objects.

## Main definitions

* `QuditCat.sumSpace`: the orthogonal direct sum of a finite family of state spaces.
* `QuditCat.sumProjection`, `QuditCat.sumInjection`: its coordinate maps.
* `QuditCat.sumBicone`, `QuditCat.sumBinaryBicone`: explicit family and binary witnesses.

## Main results

* `QuditCat.sumInjection_dagger_eq_sumProjection`: the coordinate maps are adjoint, which is
  Definition 2.39 for the direct sum.
* `QuditCat.sumBiconeIsBilimit`: the orthogonal sum has both universal properties.
* `QuditCat.isZero_sumSpace`: an empty orthogonal sum is a zero object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DaggerCategory

namespace QuditCat

noncomputable section

/-- The orthogonal direct sum of a finite family of qudit state spaces: the `L²` product of
the state spaces, whose inner product is the sum of the inner products of the components. -/
abbrev sumSpace {ι : Type} [Fintype ι] (F : ι → QuditCat) : QuditCat :=
  .of (PiLp 2 fun i ↦ (F i).state)

/-- The canonical linear map from the product of state spaces into the orthogonal direct sum,
the inverse of the coordinate-reading linear equivalence. -/
def sumOfPi {ι : Type} [Fintype ι] (F : ι → QuditCat) :
    (∀ i, (F i).state) →ₗ[ℂ] (sumSpace F).state :=
  (WithLp.linearEquiv 2 ℂ (∀ i, (F i).state)).symm.toLinearMap

@[simp]
lemma sumOfPi_apply {ι : Type} [Fintype ι] (F : ι → QuditCat)
    (x : ∀ i, (F i).state) (i : ι) : sumOfPi F x i = x i := rfl

/-- The `i`-th coordinate projection out of an orthogonal direct sum. -/
def sumProjection {ι : Type} [Fintype ι] (F : ι → QuditCat) (i : ι) : sumSpace F ⟶ F i :=
  ofHom (PiLp.projₗ 2 (𝕜 := ℂ) (fun i ↦ (F i).state) i)

/-- The `i`-th coordinate injection into an orthogonal direct sum. -/
def sumInjection {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → QuditCat) (i : ι) : F i ⟶ sumSpace F :=
  ofHom (sumOfPi F ∘ₗ LinearMap.single ℂ (fun i ↦ (F i).state) i)

lemma sumProjection_apply {ι : Type} [Fintype ι] (F : ι → QuditCat) (i : ι)
    (x : (sumSpace F).state) : (sumProjection F i).hom x = x.ofLp i := rfl

lemma sumInjection_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → QuditCat) (i : ι) (y : (F i).state) :
    (sumInjection F i).hom y = PiLp.single 2 i y := rfl

/-- The coordinate maps of an orthogonal direct sum are adjoint: the injection at an index is
the dagger of the projection at that index. This is Definition 2.39 for the direct sum, and it
is what the dagger-biproduct calculus is applied to downstream. -/
theorem sumInjection_dagger_eq_sumProjection {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : ι → QuditCat) (i : ι) :
    (sumInjection F i)† = sumProjection F i := by
  apply hom_ext
  rw [hom_dagger]
  refine LinearMap.ext fun x ↦ ext_inner_left ℂ fun y ↦ ?_
  rw [LinearMap.adjoint_inner_right, sumProjection_apply, PiLp.inner_apply, sumInjection_apply,
    Finset.sum_eq_single i]
  · rw [PiLp.single_eq_same]
  · intro j _ hj
    rw [PiLp.single_eq_of_ne (p := 2) hj, inner_zero_left]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The bicone of the orthogonal direct sum, including the empty family. -/
def sumBicone {ι : Type} [Fintype ι] (F : ι → QuditCat) : Bicone F := by
  classical
  exact
    { pt := sumSpace F
      π := sumProjection F
      ι := sumInjection F
      ι_π := fun i j ↦ by
        split_ifs with h
        · subst j
          apply hom_ext
          ext x
          simp [sumInjection, sumProjection, sumOfPi, PiLp.projₗ]
        · apply hom_ext
          ext x
          simp [sumInjection, sumProjection, sumOfPi, PiLp.projₗ, h] }

/-- Coordinatewise assembly gives the product universal property of the orthogonal sum. -/
def sumBiconeIsLimit {ι : Type} [Fintype ι] (F : ι → QuditCat) :
    IsLimit (sumBicone F).toCone :=
  Fan.IsLimit.mk _
    (fun s ↦ ofHom (sumOfPi F ∘ₗ LinearMap.pi (fun i ↦ (s.proj i).hom)))
    (by
      intro s i
      apply hom_ext
      ext x
      rfl)
    (by
      intro s m hm
      apply hom_ext
      apply LinearMap.ext
      intro x
      apply PiLp.ext
      intro i
      exact congrArg (fun f ↦ f.hom x) (hm i))

/-- The finite orthogonal sum is both a product and a coproduct. -/
def sumBiconeIsBilimit {ι : Type} [Fintype ι] (F : ι → QuditCat) :
    (sumBicone F).IsBilimit :=
  isBilimitOfIsLimit _ (sumBiconeIsLimit F)

/-- Coordinate injections and projections of the sum bicone are adjoint. -/
instance sumBicone_isDagger {ι : Type} [Fintype ι] (F : ι → QuditCat) :
    (sumBicone F).IsDagger where
  dagger_ι i := by
    classical
    exact sumInjection_dagger_eq_sumProjection F i

/-- Every finite family of qudits has a normalized dagger biproduct. -/
instance {ι : Type} [Finite ι] (F : ι → QuditCat) : HasDaggerBiproduct F := by
  let := Fintype.ofFinite ι
  exact ⟨⟨sumBicone F, sumBiconeIsBilimit F, inferInstance⟩⟩

/-- The normalized witnesses supply Mathlib's finite-biproduct existence interface. -/
instance : HasFiniteBiproducts QuditCat where
  out _ := ⟨fun F ↦ HasBiproduct.mk ⟨sumBicone F, sumBiconeIsBilimit F⟩⟩

/-- The binary orthogonal sum is the two-index instance of the family construction. -/
def sumBinaryBicone (X Y : QuditCat) : BinaryBicone X Y :=
  (sumBicone (pairFunction X Y)).toBinaryBicone

/-- The binary orthogonal sum has both universal properties. -/
def sumBinaryBiconeIsBilimit (X Y : QuditCat) : (sumBinaryBicone X Y).IsBilimit :=
  (Bicone.toBinaryBiconeIsBilimit _).symm (sumBiconeIsBilimit (pairFunction X Y))

/-- The binary coordinate injections are adjoint to the projections. -/
instance sumBinaryBicone_isDagger (X Y : QuditCat) : (sumBinaryBicone X Y).IsDagger where
  dagger_inl := Bicone.IsDagger.dagger_ι (b := sumBicone (pairFunction X Y)) WalkingPair.left
  dagger_inr := Bicone.IsDagger.dagger_ι (b := sumBicone (pairFunction X Y)) WalkingPair.right

/-- Every pair of qudits has a normalized binary dagger biproduct. -/
instance (X Y : QuditCat) : HasDaggerBinaryBiproduct X Y where
  exists_daggerBinaryBiproduct :=
    ⟨sumBinaryBicone X Y, sumBinaryBiconeIsBilimit X Y, inferInstance⟩

/-- The binary witnesses also supply Mathlib's binary-biproduct interface. -/
instance : HasBinaryBiproducts QuditCat where
  has_binary_biproduct X Y :=
    HasBinaryBiproduct.mk ⟨sumBinaryBicone X Y, sumBinaryBiconeIsBilimit X Y⟩

/-- The orthogonal sum over an empty index type is a zero object. -/
theorem isZero_sumSpace {ι : Type} [Fintype ι] [IsEmpty ι] (F : ι → QuditCat) :
    IsZero (sumSpace F) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply hom_ext
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  exact isEmptyElim i

/-- The empty orthogonal sum supplies the zero object of `QuditCat`. -/
instance : HasZeroObject QuditCat :=
  (isZero_sumSpace (fun i : Empty ↦ isEmptyElim i)).hasZeroObject

end

end QuditCat
