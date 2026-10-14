/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerBiproduct
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Logic.Pairwise

/-!
# Scalars, states, effects and the Born rule

This file develops the basic ingredients of categorical quantum mechanics in an arbitrary
monoidal category `C` — the scalars of `C`, states and joint states, effects — together with
the measurement theory that §2.4.3 of the source notes builds on them.

The scalars of `C` are the endomorphisms of its monoidal unit `𝟙_ C`; they form a commutative
monoid (by the Eckmann-Hilton argument) and act on every hom-set by scalar multiplication. We
also define states, joint states and entanglement, effects, and the Born-rule probability of an
effect in a state (for a monoidal dagger category).

A family of effects `A --xᵢ--> I` is *complete* when every nonzero process yields a nonzero
effect, and *disjoint* when `xᵢ ∘ xᵢ† = id` and `xᵢ ∘ xⱼ† = 0` for `i ≠ j`. The notes
characterize complete disjoint families by their associated biproduct map `biproduct.lift x`
(Lemma 2.52) and show that map is unitary under an invertible superposition rule (Lemma 2.53).
The Born rule is proved first for effects resolving the identity, and then for a complete
disjoint family under an invertible superposition rule as a corrected form of Proposition 2.55.

## Main definitions

* `Scalar`: the scalars of a monoidal category, i.e. `End (𝟙_ C)`.
* `State` and `JointState`: morphisms from the monoidal unit into an object, resp. a tensor
  product of two objects.
* `JointState.Entangled`: the property that a joint state is not a product state.
* `Effect`: morphisms into the monoidal unit.
* `Effect.Complete` and `Effect.Disjoint`: complete, resp. disjoint, families of effects.
* `probability`: the Born-rule probability of an effect in a state.

## Main results

* `Scalar.commMonoid`: the scalars of a monoidal category form a commutative monoid.
* `comp_comm`: endomorphisms of the monoidal unit commute under composition.
* `smul_assoc` and `smul_comp_smul`: the scalar action is associative and satisfies the
  interchange law with composition.
* `JointState.not_entangled_iff`: a joint state is not entangled iff it is a product state.
* `Effect.disjoint_iff_isIsometry_dagger`: **Lemma 2.52**, disjointness half — a family is
  disjoint iff the dagger of its biproduct map is an isometry.
* `Effect.complete_iff_kernel_iota_eq_zero`: **Lemma 2.52**, completeness half — a family is
  complete iff its biproduct map has zero kernel.
* `Effect.isUnitary_lift_of_complete_disjoint`: **Lemma 2.53**.
* `Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id`: the Born rule for effects resolving
  the identity, without an additive-inverse or biproduct assumption.
* `Effect.sum_probability_eq_one`: a corrected form of **Proposition 2.55** under an invertible
  superposition rule.

## Implementation notes

The effects sections preserve the established order of the `MonoidalCategory` and
`DaggerCategory` instance parameters in the public declarations.

Two points where this formalization deliberately departs from the printed source, both
recorded here because they are corrections rather than choices:

* Lemma 2.53 is stated **without** the notes' `HasEqualizers` hypothesis. The notes use the
  equalizer of `x` and `0` to conclude `y = 0` from `x ∘ y = 0`, but completeness alone
  already gives that, so the hypothesis is unused and dropping it strengthens the result.
* The printed Proposition 2.55 is false for general complete families: with `A = ℂ²`,
  `x₁ = ⟨e₁|` and `x₂ = ⟨e₁| + ⟨e₂|`, the family is complete but not disjoint, and
  `Σᵢ Prob(xᵢ, |e₁⟩) = 2`. The corrected complete/disjoint theorem also assumes an
  invertible superposition rule (`Preadditive C`), used through Lemma 2.53. Lemma 2.52 alone
  gives the identity on `⨁ᵢ I`, whereas the Born-rule computation needs the identity on `A`.
  These added hypotheses are sufficient; they are not asserted to be the unique intended
  correction. The identity-resolution theorem below gives a separate sufficient condition.

The kernel in Lemma 2.52 is rendered as `kernel.ι X = 0` (the kernel map is the zero
morphism). This is the `Prop`-valued form that follows directly from `Effect.Complete`;
`IsZero (kernel X)` says the same thing but additionally demands
`Nonempty (Unique (kernel X ⟶ Y))` and so needs a detour through `𝟙 (kernel X) = 0`.
-/

@[expose] public section

open CategoryTheory Limits
open scoped BigOperators

namespace CategoryTheory.MonoidalCategory

open CategoryTheory.DaggerCategory

universe u v

section Scalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- The scalars of a monoidal category `C`, i.e. the endomorphisms of its monoidal unit
`𝟙_ C`. They form a commutative monoid (see `Scalar.commMonoid`) and act on every hom-set by
scalar multiplication (see the `SMul` instance below). -/
abbrev Scalar (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] : Type _ := End (𝟙_ C)

@[reassoc]
private lemma whiskerRight_leftUnitor (s : Scalar C) :
    (s ▷ 𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ s :=
  unitors_equal (C := C) ▸ rightUnitor_naturality s

private lemma scalar_tensor_eq_comp (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = s ≫ t := by
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality, whiskerRight_leftUnitor_assoc]
  simp

private lemma scalar_tensor_eq_comp_rev (s t : Scalar C) :
    (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (λ_ (𝟙_ C)).hom = t ≫ s := by
  have : s ⊗ₘ t = (𝟙_ C ◁ t) ≫ (s ▷ 𝟙_ C) := by
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
  rw [this, Category.assoc, whiskerRight_leftUnitor, leftUnitor_naturality_assoc]
  simp

/-- Endomorphisms of the monoidal unit commute under composition. -/
@[reassoc]
lemma comp_comm {s t : End (𝟙_ C)} : s ≫ t = t ≫ s := by
  rw [← scalar_tensor_eq_comp, scalar_tensor_eq_comp_rev]

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance Scalar.commMonoid : CommMonoid (Scalar C) where
  mul_comm _ _ := by rw [End.mul_def, End.mul_def, comp_comm]

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom

/-- The scalar action of `s : Scalar C` on a morphism `f : c₁ ⟶ c₂` is given by tensoring
with `s` and transporting across the left unitors. -/
lemma smul_def {c₁ c₂ : C} {s : Scalar C} {f : c₁ ⟶ c₂} :
    s • f = (λ_ c₁).inv ≫ (s ⊗ₘ f) ≫ (λ_ c₂).hom := rfl

/-- Scalar multiplication is associative: acting on a morphism by `s` then `t` agrees with
acting by the scalar product `t * s`. -/
lemma smul_assoc {c₁ c₂ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} : s • t • f = (t * s) • f := by
  rw [smul_def, smul_def, smul_def, End.mul_def, ← scalar_tensor_eq_comp]
  simp [tensorHom_def]

/-- Scalar multiplication satisfies the interchange law with composition:
`(s • f) ≫ (t • g) = (s * t) • (f ≫ g)`. -/
lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  simp [comp_comm, smul_def]

end Scalars

section States

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- A state of an object `c` is a morphism from the monoidal unit `𝟙_ C` into `c`. -/
abbrev State (c : C) : Type _ := 𝟙_ C ⟶ c

/-- A joint state of two objects `c₁` and `c₂` is a morphism from the monoidal unit `𝟙_ C`
into their tensor product `c₁ ⊗ c₂`. -/
abbrev JointState (c₁ c₂ : C) : Type _ := 𝟙_ C ⟶ c₁ ⊗ c₂

/-- A joint state `f : JointState c₁ c₂` is entangled if it is not a product state, i.e. if
it cannot be written as `(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g : State c₁` and
`h : State c₂`. -/
def JointState.Entangled {c₁ c₂ : C} (f : JointState c₁ c₂) : Prop :=
  ∀ (g : State c₁) (h : State c₂), f ≠ (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)

/-- A joint state is not entangled iff it is a product state, i.e. of the form
`(λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h)` for states `g` and `h`. -/
lemma JointState.not_entangled_iff {c₁ c₂ : C} (f : JointState c₁ c₂) :
    ¬ f.Entangled ↔ ∃ (g : State c₁) (h : State c₂), f = (λ_ (𝟙_ C)).inv ≫ (g ⊗ₘ h) := by
  simp [JointState.Entangled]

end States

section Effects

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- An effect on an object `c` is a morphism from `c` into the monoidal unit `𝟙_ C`. -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

/-- A set of effects `xᵢ : c ⟶ 𝟙_ C` is complete if every nonzero process yields a nonzero
effect, i.e. if a morphism `f : c' ⟶ c` vanishes after postcomposition with every `xᵢ`, then
`f = 0`. -/
def Effect.Complete [HasZeroMorphisms C] {ι : Type*} {c : C} (x : ι → Effect c) : Prop :=
  ∀ {c' : C} (f : c' ⟶ c), (∀ (i : ι), f ≫ x i = 0) → f = 0

variable [DaggerCategory C]

/-- A family of effects is disjoint if each dagger effect is an isometry and distinct effects
are orthogonal: `(x j)† ≫ x i = 0` whenever `i ≠ j`. -/
def Effect.Disjoint [HasZeroMorphisms C] {ι : Type*} {c : C} (x : ι → Effect c) : Prop :=
  (∀ (i : ι), (x i)† ≫ x i = 𝟙 (𝟙_ C)) ∧ _root_.Pairwise (fun i j ↦ (x j)† ≫ x i = 0)

lemma Effect.Disjoint.isIsometry_dagger [HasZeroMorphisms C] {ι : Type*} {c : C}
    (x : ι → Effect c) (hx : Effect.Disjoint x) (i : ι) : DaggerCategory.IsIsometry (x i)† :=
  ⟨by simpa using hx.1 i⟩

lemma Effect.Disjoint.dagger_comp_eq_zero [HasZeroMorphisms C] {ι : Type*} {c : C}
    (x : ι → Effect c) (hx : Effect.Disjoint x) {i j : ι} (h : i ≠ j) : (x j)† ≫ (x i) = 0 :=
  hx.2 h

-- The two characterizations of `Effect.Complete` and `Effect.Disjoint` by the associated
-- biproduct map `biproduct.lift x` are proved in the `EffectsBiproduct` section below:
-- `Effect.complete_iff_kernel_iota_eq_zero` and `Effect.disjoint_iff_isIsometry_dagger`.

end Effects

section EffectsBiproduct

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [MonoidalCategory.{v} C]
  [HasZeroMorphisms C]
variable {ι : Type} [Fintype ι] {c : C}
variable (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
  [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)]

omit [Fintype ι] in
/-- The `i`-th component of the dagged biproduct map is `(x i)†`. This is where
Definition 2.39 is used. -/
lemma Effect.iota_lift_dagger (i : ι) :
    biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ (biproduct.lift x)† = (x i)† := by simp

omit [Fintype ι] in
/-- **Lemma 2.52**, disjointness half: a family of effects is disjoint precisely when the
dagger of its associated biproduct map is an isometry. -/
theorem Effect.disjoint_iff_isIsometry_dagger :
    Effect.Disjoint x ↔ IsIsometry (biproduct.lift x)† := by
  constructor
  · intro h
    refine ⟨?_⟩
    simp only [involutive_dagger]
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, Category.id_comp, biproduct.lift_π]
    apply biproduct.hom_ext'
    intro i
    rw [← Category.assoc, Effect.iota_lift_dagger x i]
    by_cases hij : i = j
    · subst hij
      rw [biproduct.ι_π_self, h.1 i]
    · rw [biproduct.ι_π_ne _ hij]
      exact h.2 (fun h ↦ hij h.symm)
  · intro h
    have hh : (biproduct.lift x)† ≫ biproduct.lift x = 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C) := by
      simpa only [involutive_dagger] using h.comp_dagger_eq_id
    have key : ∀ i j : ι, (x i)† ≫ x j
        = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
      intro i j
      calc (x i)† ≫ x j
          = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ (biproduct.lift x)†
              ≫ biproduct.lift x ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [← Category.assoc, Effect.iota_lift_dagger x i, biproduct.lift_π]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i
              ≫ ((biproduct.lift x)† ≫ biproduct.lift x)
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            simp only [Category.assoc]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i ≫ 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C)
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [hh]
        _ = biproduct.ι (fun _ : ι ↦ 𝟙_ C) i
              ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) j := by
            rw [Category.id_comp]
    constructor
    · intro i
      rw [key i i, biproduct.ι_π_self]
    · intro i j hij
      rw [key j i, biproduct.ι_π_ne _ (fun h ↦ hij h.symm)]

omit [DaggerCategory C] [Fintype ι] [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)] in
/-- **Lemma 2.52**, completeness half: a family of effects is complete precisely when its
associated biproduct map has zero kernel. -/
theorem Effect.complete_iff_kernel_iota_eq_zero [HasKernel (biproduct.lift x)] :
    Effect.Complete x ↔ kernel.ι (biproduct.lift x) = 0 := by
  constructor
  · intro h
    exact h (kernel.ι (biproduct.lift x)) fun i ↦ by
      rw [← biproduct.lift_π x i, ← Category.assoc, kernel.condition, zero_comp]
  · intro h c' f hf
    have hX : f ≫ biproduct.lift x = 0 := by
      apply biproduct.hom_ext
      intro i
      rw [Category.assoc, biproduct.lift_π, zero_comp]
      exact hf i
    calc f = kernel.lift (biproduct.lift x) f hX ≫ kernel.ι (biproduct.lift x) :=
          (kernel.lift_ι (biproduct.lift x) f hX).symm
      _ = kernel.lift (biproduct.lift x) f hX ≫ 0 := by rw [h]
      _ = 0 := comp_zero

end EffectsBiproduct

section EffectsUnitary

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [MonoidalCategory.{v} C]
  [Preadditive C]
variable {ι : Type} [Fintype ι] {c : C}
variable (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
  [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)]

omit [Fintype ι] in
/-- **Lemma 2.53**: a finite complete disjoint set of effects has a unitary associated
biproduct map.

The notes assume `HasEqualizers` here; the proof below does not use it. With
`y := x ≫ x† − 𝟙`, disjointness gives `y ≫ x = 0`, and completeness alone (`y ≫ xᵢ = 0` for
all `i` implies `y = 0`) already concludes `y = 0`, so the statement is strictly stronger
than the printed one. The notes' "invertible superposition rule" is `Preadditive C`. -/
theorem Effect.isUnitary_lift_of_complete_disjoint
    (hx : Effect.Complete x) (hxd : Effect.Disjoint x) :
    IsUnitary (biproduct.lift x) := by
  have hXX : (biproduct.lift x)† ≫ biproduct.lift x = 𝟙 (⨁ fun _ : ι ↦ 𝟙_ C) := by
    have h := (Effect.disjoint_iff_isIsometry_dagger x).mp hxd
    simpa only [involutive_dagger] using h.comp_dagger_eq_id
  have hy : biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c = 0 := by
    refine hx (biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c) ?_
    have hyX : (biproduct.lift x ≫ (biproduct.lift x)† - 𝟙 c) ≫ biproduct.lift x = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hXX, Category.comp_id,
        sub_self]
    intro i
    have := congrArg (fun m ↦ m ≫ biproduct.π (fun _ : ι ↦ 𝟙_ C) i) hyX
    simpa [Category.assoc, biproduct.lift_π] using this
  let : IsIsometry (biproduct.lift x) := ⟨sub_eq_zero.mp hy⟩
  exact ⟨hXX⟩

end EffectsUnitary

section Probability

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [DaggerCategory C]

/-- The probability associated to a state and an effect of an object in a monoidal dagger category,
given by the scalar `a ≫ x ≫ x† ≫ a†`. -/
abbrev probability {c : C} (a : State c) (x : Effect c) : Scalar C := a ≫ x ≫ x† ≫ a†

end Probability

section ProbabilityAdditive

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [MonoidalCategory.{v} C]
  [Semiadditive C]

/-- The **Born rule** for a finite family of effects resolving the identity and an isometric
state. This only needs commutative-monoid superposition, not additive inverses or biproducts. -/
theorem Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id
    {ι : Type*} [Fintype ι] {c : C} (x : ι → Effect c)
    (hx : ∑ i, x i ≫ (x i)† = 𝟙 c) (a : State c) (ha : IsIsometry a) :
    ∑ i, probability a (x i) = 𝟙 (𝟙_ C) := by
  calc ∑ i, probability a (x i)
      = a ≫ (∑ i, x i ≫ (x i)†) ≫ a† := by
        simp only [probability, Semiadditive.comp_sum, Semiadditive.sum_comp, Category.assoc]
    _ = a ≫ a† := by rw [hx, Category.id_comp]
    _ = 𝟙 (𝟙_ C) := ha.comp_dagger_eq_id

end ProbabilityAdditive

section BornRule

variable {C : Type u} [Category.{v} C] [DaggerCategory C] [MonoidalCategory.{v} C]
  [Preadditive C]
variable {ι : Type} [Fintype ι] {c : C}
variable (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
  [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)]

/-- `x ≫ x†` is the sum of the rank-one pieces `xᵢ ≫ xᵢ†` — the diagonal part of the
matrix computation in Lemma 2.52. Uses `biproduct.total` and Definition 2.39. -/
theorem Effect.lift_comp_dagger_eq_sum :
    biproduct.lift x ≫ (biproduct.lift x)† = ∑ i, x i ≫ (x i)† := by
  calc biproduct.lift x ≫ (biproduct.lift x)†
      = biproduct.lift x ≫ (∑ i, biproduct.π (fun _ : ι ↦ 𝟙_ C) i
            ≫ biproduct.ι (fun _ : ι ↦ 𝟙_ C) i) ≫ (biproduct.lift x)† := by
        rw [biproduct.total, Category.id_comp]
    _ = ∑ i, x i ≫ (x i)† := by
        rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Category.assoc, biproduct.lift_π, Category.assoc, Effect.iota_lift_dagger]

/-- A corrected form of **Proposition 2.55 (the Born rule)**: for a finite complete disjoint
family of effects with an invertible superposition rule and an isometric state, probabilities
sum to `1`.

The printed statement omits both `Disjoint` and the invertible superposition assumption.
The latter is used by Lemma 2.53; see the file header for the scope of this correction. -/
theorem Effect.sum_probability_eq_one (hx : Effect.Complete x) (hxd : Effect.Disjoint x)
    (a : State c) (ha : IsIsometry a) :
    (∑ i, probability a (x i)) = 𝟙 (𝟙_ C) := by
  have hunit : IsUnitary (biproduct.lift x) :=
    Effect.isUnitary_lift_of_complete_disjoint x hx hxd
  exact Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id x (by
    rw [← Effect.lift_comp_dagger_eq_sum x]
    exact IsIsometry.comp_dagger_eq_id (biproduct.lift x)) a ha

end BornRule

end CategoryTheory.MonoidalCategory
