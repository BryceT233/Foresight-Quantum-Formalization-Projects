/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.QuditCat.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Additive and dagger structure on `QuditCat`

This file completes the categorical structure of the category `QuditCat` of finite-dimensional
complex inner product spaces that `FQFP.CQM.QuditCat.Basic` sets up: the additive structure on
its hom-sets, the resulting `Preadditive` instance, and the interaction of the dagger with the
bra and ket morphisms.

`QuditCat` is the running example of a monoidal dagger category in the source notes, and both
of the structures developed here are needed before its dual structure can be discussed. The
additive structure is what makes the Born-rule sum `∑ i, probability a (x i)` an element of
`End (𝟙_ QuditCat)`, and it is the superposition rule of Chapter 2 in this model. The dagger
lemmas record that the adjoint of a bra is the corresponding ket and conversely, which is the
form in which the dagger is used when duals are described concretely.

## Main definitions

* The pointwise `Add`, `Zero`, `SMul ℕ`, `Neg`, `Sub`, `SMul ℤ` and `AddCommGroup` structures
  on the hom-sets of `QuditCat`, transported from the corresponding structures on linear maps
  along the injective forgetful map.
* `QuditCat.preadditive`: `QuditCat` is preadditive.

## Main results

* `QuditCat.hom_add`, `QuditCat.hom_zero`, `QuditCat.hom_neg`, `QuditCat.hom_sub`,
  `QuditCat.hom_nsmul`, `QuditCat.hom_zsmul`, `QuditCat.hom_sum`: the underlying linear map of
  each of these operations.
* `QuditCat.braArrow_dagger`, `QuditCat.ketArrow_dagger`: the dagger of a bra is the
  corresponding ket, and conversely.
* `QuditCat.ofHom_lsmul_one`: the scalar `1` acts as the identity on the monoidal unit.

## Implementation notes

The additive structure is installed by hand rather than derived, because `QuditCat` is a
`LargeCategory` whose hom-sets are *bundled* linear maps: `Function.Injective.addCommGroup`
transports the group structure along `Hom.hom`, which is injective by `hom_injective`. The
plain `Add`/`Zero`/`SMul ℕ`/`Neg`/`Sub`/`SMul ℤ` instances are given first so that the
`addCommGroup` instance's proof obligations are `rfl`, exactly as Mathlib's `ModuleCat` does.
`Preadditive` then follows from additivity of composition of linear maps, and every
`hom_*` lemma is `rfl`, so `simp` can push the forgetful functor through these operations.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace QuditCat

noncomputable section

variable {H₁ H₂ : QuditCat}

/-- Morphisms of `QuditCat` are added pointwise on their underlying linear maps. -/
instance : Add (H₁ ⟶ H₂) where
  add f g := ofHom (f.hom + g.hom)

/-- The underlying linear map of a sum of morphisms of `QuditCat` is the sum of the underlying
linear maps. -/
@[simp]
lemma hom_add (f g : H₁ ⟶ H₂) : (f + g).hom = f.hom + g.hom := rfl

/-- The zero morphism of `QuditCat` is the zero linear map. -/
instance : Zero (H₁ ⟶ H₂) where
  zero := ofHom 0

/-- The underlying linear map of the zero morphism of `QuditCat` is zero. -/
@[simp]
lemma hom_zero : (0 : H₁ ⟶ H₂).hom = 0 := rfl

/-- Natural number multiples of a morphism of `QuditCat` are pointwise. -/
instance : SMul ℕ (H₁ ⟶ H₂) where
  smul n f := ofHom (n • f.hom)

/-- The underlying linear map of a natural number multiple of a morphism of `QuditCat`. -/
@[simp]
lemma hom_nsmul (n : ℕ) (f : H₁ ⟶ H₂) : (n • f).hom = n • f.hom := rfl

/-- Negation of a morphism of `QuditCat` is pointwise. -/
instance : Neg (H₁ ⟶ H₂) where
  neg f := ofHom (-f.hom)

/-- The underlying linear map of the negation of a morphism of `QuditCat`. -/
@[simp]
lemma hom_neg (f : H₁ ⟶ H₂) : (-f).hom = -f.hom := rfl

/-- Subtraction of morphisms of `QuditCat` is pointwise. -/
instance : Sub (H₁ ⟶ H₂) where
  sub f g := ofHom (f.hom - g.hom)

/-- The underlying linear map of a difference of morphisms of `QuditCat`. -/
@[simp]
lemma hom_sub (f g : H₁ ⟶ H₂) : (f - g).hom = f.hom - g.hom := rfl

/-- Integer multiples of a morphism of `QuditCat` are pointwise. -/
instance : SMul ℤ (H₁ ⟶ H₂) where
  smul n f := ofHom (n • f.hom)

/-- The underlying linear map of an integer multiple of a morphism of `QuditCat`. -/
@[simp]
lemma hom_zsmul (n : ℤ) (f : H₁ ⟶ H₂) : (n • f).hom = n • f.hom := rfl

/-- The hom-set of `QuditCat` is an additive commutative group, transported from the additive
commutative group of linear maps along the injective forgetful map. -/
instance : AddCommGroup (H₁ ⟶ H₂) :=
  Function.Injective.addCommGroup Hom.hom hom_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying linear map of a finite sum of morphisms of `QuditCat` is the sum of the
underlying linear maps. -/
@[simp]
lemma hom_sum {ι : Type*} (s : Finset ι) (f : ι → (H₁ ⟶ H₂)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ({ toFun := Hom.hom, map_zero' := hom_zero, map_add' := hom_add } :
    (H₁ ⟶ H₂) →+ (H₁.state →ₗ[ℂ] H₂.state)) f s

/-- `QuditCat` is preadditive: composition is additive in both variables, by additivity of
composition of linear maps. -/
instance : Preadditive QuditCat where
  add_comp _ _ _ _ _ _ := by
    apply hom_ext
    simp only [hom_comp, hom_add]
    exact LinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _ := by
    apply hom_ext
    simp only [hom_comp, hom_add]
    exact LinearMap.add_comp _ _ _

/-- The dagger of the bra of a vector is the ket of that vector. -/
@[simp]
lemma braArrow_dagger {H : QuditCat} (v : H.state) : (braArrow v)† = ketArrow v := by
  apply hom_ext
  simp only [hom_dagger, braArrow, ketArrow, bra, ket, hom_ofHom]
  exact LinearMap.adjoint_innerₛₗ_apply (𝕜 := ℂ) (E := H.state) v

/-- The dagger of the ket of a vector is the bra of that vector. -/
@[simp]
lemma ketArrow_dagger {H : QuditCat} (v : H.state) : (ketArrow v)† = braArrow v := by
  apply hom_ext
  simp only [hom_dagger, braArrow, ketArrow, bra, ket, hom_ofHom]
  exact LinearMap.adjoint_toSpanSingleton (𝕜 := ℂ) (E := H.state) v

/-- A scalar of `QuditCat` treated as an endomorphism of `ℂ` is the identity when the scalar
is `1`. -/
lemma ofHom_lsmul_one : ofHom (LinearMap.lsmul ℂ ℂ (1 : ℂ)) = 𝟙 (of ℂ) := by
  rw [show LinearMap.lsmul ℂ ℂ (1 : ℂ) = LinearMap.id from by
    ext
    simp [LinearMap.lsmul_apply]]
  exact ofHom_id

end

end QuditCat
