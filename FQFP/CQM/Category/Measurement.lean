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
* `Effect.disjoint_iff_isIsometry_dagger_lift`,
  `Effect.complete_iff_bicone_kernel_iota_eq_zero`,
  `Effect.isUnitary_bicone_lift_of_complete_disjoint`: the explicit-witness versions of
  **Lemmas 2.52 and 2.53**. The chosen-biproduct declarations are their specializations.
* `Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id`: the Born rule for effects resolving
  the identity, without an additive-inverse or biproduct assumption.
* `Effect.sum_probability_eq_one`: a corrected form of **Proposition 2.55** under an invertible
  superposition rule.
* `Effect.sum_probability_eq_one_of_complete_disjoint_bicone`: the same corrected Born rule
  for an explicitly supplied dagger-biproduct witness.

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

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

section Scalars

/-- The scalars of a monoidal category `C`, i.e. the endomorphisms of its monoidal unit
`𝟙_ C`. They form a commutative monoid (see `Scalar.commMonoid`) and act on every hom-set by
scalar multiplication (see the `SMul` instance below). -/
abbrev Scalar (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] : Type _ := End (𝟙_ C)

/-- Scalar endomorphisms of the monoidal unit commute. -/
instance : CommMonoid (Scalar C) where
  mul_comm s t := by
    ext
    simpa [unitors_equal, unitors_inv_equal] using
      congrArg (fun f => (ρ_ (𝟙_ C)).inv ≫ f ≫ (ρ_ (𝟙_ C)).hom)
        (whisker_exchange s.asHom t.asHom)

instance {c₁ c₂ : C} : SMul (Scalar C) (c₁ ⟶ c₂) where
  smul s f := (λ_ c₁).inv ≫ (s.asHom ⊗ₘ f) ≫ (λ_ c₂).hom

/-- The scalar action of `s : Scalar C` on a morphism `f : c₁ ⟶ c₂` is given by tensoring
with `s` and transporting across the left unitors. -/
lemma smul_def {c₁ c₂ : C} {s : Scalar C} {f : c₁ ⟶ c₂} :
    s • f = (λ_ c₁).inv ≫ (s.asHom ⊗ₘ f) ≫ (λ_ c₂).hom := rfl

/-- Scalar multiplication is associative: acting on a morphism by `s` then `t` agrees with
acting by the scalar product `t * s`. -/
lemma smul_assoc {c₁ c₂ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} : s • t • f = (t * s) • f := by
  simp [smul_def, tensorHom_def, End.mul_asHom]

/-- Scalar multiplication satisfies the interchange law with composition:
`(s • f) ≫ (t • g) = (s * t) • (f ≫ g)`. -/
lemma smul_comp_smul {c₁ c₂ c₃ : C} {s t : Scalar C} {f : c₁ ⟶ c₂} {g : c₂ ⟶ c₃} :
    (s • f) ≫ (t • g) = (s * t) • (f ≫ g) := by
  rw [mul_comm s t]
  simp [smul_def, End.mul_asHom]

end Scalars

section States

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

variable [DaggerCategory C] {ι : Type} [Fintype ι] {c : C}

section Effects

/-- An effect on an object `c` is a morphism from `c` into the monoidal unit `𝟙_ C`. -/
abbrev Effect (c : C) : Type _ := c ⟶ 𝟙_ C

/-- A set of effects `xᵢ : c ⟶ 𝟙_ C` is complete if every nonzero process yields a nonzero
effect, i.e. if a morphism `f : c' ⟶ c` vanishes after postcomposition with every `xᵢ`, then
`f = 0`. -/
def Effect.Complete [HasZeroMorphisms C] {ι : Type*} {c : C} (x : ι → Effect c) : Prop :=
  ∀ {c' : C} (f : c' ⟶ c), (∀ (i : ι), f ≫ x i = 0) → f = 0

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

section EffectsBicone

variable [HasZeroMorphisms C] {κ : Type*}
  (b : Bicone (fun _ : κ ↦ 𝟙_ C)) (hb : b.IsBilimit) [b.IsDagger]
  (x : κ → Effect c)

/-- Each component of the daggered lift to an explicit dagger bicone is a dagger effect. -/
@[reassoc]
lemma Effect.iota_bicone_lift_dagger (i : κ) :
    b.ι i ≫ (b.lift hb x)† = (x i)† := by
  rw [b.dagger_lift hb x, b.ι_desc]

/-- **Lemma 2.52**, disjointness half, for an explicit dagger-biproduct witness. -/
theorem Effect.disjoint_iff_isIsometry_dagger_lift :
    Effect.Disjoint x ↔ IsIsometry (b.lift hb x)† := by
  constructor
  · intro h
    refine ⟨?_⟩
    simp only [involutive_dagger]
    apply hb.isLimit.hom_ext
    rintro ⟨j⟩
    change ((b.lift hb x)† ≫ b.lift hb x) ≫ b.π j = 𝟙 b.pt ≫ b.π j
    rw [Category.assoc, b.lift_π hb x, Category.id_comp]
    apply hb.isColimit.hom_ext
    rintro ⟨i⟩
    change b.ι i ≫ ((b.lift hb x)† ≫ x j) = b.ι i ≫ b.π j
    rw [← Category.assoc, Effect.iota_bicone_lift_dagger]
    by_cases hij : i = j
    · subst j
      rw [bicone_ι_π_self, h.1 i]
    · rw [bicone_ι_π_ne b hij]
      exact h.2 (Ne.symm hij)
  · intro h
    have hh : (b.lift hb x)† ≫ b.lift hb x = 𝟙 b.pt := by
      simpa only [involutive_dagger] using h.comp_dagger_eq_id
    have key (i j : κ) : (x i)† ≫ x j = b.ι i ≫ b.π j := by
      calc
        (x i)† ≫ x j = (b.ι i ≫ (b.lift hb x)†) ≫ (b.lift hb x ≫ b.π j) := by
          rw [b.lift_π hb x, Effect.iota_bicone_lift_dagger b hb x]
        _ = b.ι i ≫ ((b.lift hb x)† ≫ b.lift hb x) ≫ b.π j := by
          simp only [Category.assoc]
        _ = b.ι i ≫ b.π j := by rw [hh, Category.id_comp]
    constructor
    · intro i
      rw [key i i, bicone_ι_π_self]
    · intro i j hij
      rw [key j i, bicone_ι_π_ne b (Ne.symm hij)]

omit [DaggerCategory C] [b.IsDagger] in
/-- **Lemma 2.52**, completeness half, for an explicit bilimit bicone. -/
theorem Effect.complete_iff_bicone_kernel_iota_eq_zero [HasKernel (b.lift hb x)] :
    Effect.Complete x ↔ kernel.ι (b.lift hb x) = 0 := by
  constructor
  · intro h
    exact h (kernel.ι (b.lift hb x)) fun i ↦ by
      rw [← b.lift_π hb x i, ← Category.assoc, kernel.condition, zero_comp]
  · intro h Y f hf
    have hX : f ≫ b.lift hb x = 0 := by
      apply hb.isLimit.hom_ext
      rintro ⟨i⟩
      change (f ≫ b.lift hb x) ≫ b.π i = 0 ≫ b.π i
      rw [Category.assoc, b.lift_π, zero_comp]
      exact hf i
    calc
      f = kernel.lift (b.lift hb x) f hX ≫ kernel.ι (b.lift hb x) :=
        (kernel.lift_ι (b.lift hb x) f hX).symm
      _ = 0 := by rw [h, comp_zero]

end EffectsBicone

section EffectsBiconeUnitary

variable [Preadditive C] {κ : Type*}
  (b : Bicone (fun _ : κ ↦ 𝟙_ C)) (hb : b.IsBilimit) [b.IsDagger]
  (x : κ → Effect c)

/-- **Lemma 2.53** for an explicit dagger-biproduct witness. -/
theorem Effect.isUnitary_bicone_lift_of_complete_disjoint
    (hx : Effect.Complete x) (hxd : Effect.Disjoint x) :
    IsUnitary (b.lift hb x) := by
  have hXX : (b.lift hb x)† ≫ b.lift hb x = 𝟙 b.pt := by
    have h := (Effect.disjoint_iff_isIsometry_dagger_lift b hb x).mp hxd
    simpa only [involutive_dagger] using h.comp_dagger_eq_id
  have hy : b.lift hb x ≫ (b.lift hb x)† - 𝟙 c = 0 := by
    refine hx (b.lift hb x ≫ (b.lift hb x)† - 𝟙 c) ?_
    have hyX : (b.lift hb x ≫ (b.lift hb x)† - 𝟙 c) ≫ b.lift hb x = 0 := by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hXX, Category.comp_id,
        sub_self]
    intro i
    have hi := congrArg (fun m ↦ m ≫ b.π i) hyX
    simpa only [Category.assoc, Bicone.lift_π, zero_comp] using hi
  let : IsIsometry (b.lift hb x) := ⟨sub_eq_zero.mp hy⟩
  exact ⟨hXX⟩

end EffectsBiconeUnitary

section EffectsBiproduct

variable [HasZeroMorphisms C] (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
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
    Effect.Disjoint x ↔ IsIsometry (biproduct.lift x)† :=
  Effect.disjoint_iff_isIsometry_dagger_lift
    (biproduct.bicone (fun _ : ι ↦ 𝟙_ C)) (biproduct.isBilimit _) x

omit [DaggerCategory C] [Fintype ι] [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)] in
/-- **Lemma 2.52**, completeness half: a family of effects is complete precisely when its
associated biproduct map has zero kernel. -/
theorem Effect.complete_iff_kernel_iota_eq_zero [HasKernel (biproduct.lift x)] :
    Effect.Complete x ↔ kernel.ι (biproduct.lift x) = 0 := by
  let : HasKernel ((biproduct.bicone (fun _ : ι ↦ 𝟙_ C)).lift (biproduct.isBilimit _) x) := by
    change HasKernel (biproduct.lift x)
    infer_instance
  exact Effect.complete_iff_bicone_kernel_iota_eq_zero
    (biproduct.bicone (fun _ : ι ↦ 𝟙_ C)) (biproduct.isBilimit _) x

end EffectsBiproduct

section EffectsUnitary

variable [Preadditive C] (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
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
    IsUnitary (biproduct.lift x) :=
  Effect.isUnitary_bicone_lift_of_complete_disjoint
    (biproduct.bicone (fun _ : ι ↦ 𝟙_ C)) (biproduct.isBilimit _) x hx hxd

end EffectsUnitary

section Probability

/-- The probability associated to a state and an effect of an object in a monoidal dagger category,
given by the scalar `a ≫ x ≫ x† ≫ a†`. -/
abbrev probability {c : C} (a : State c) (x : Effect c) : Scalar C :=
  .of (a ≫ x ≫ x† ≫ a†)

end Probability

section ProbabilityAdditive

variable [Semiadditive C]

/-- The **Born rule** for a finite family of effects resolving the identity and an isometric
state. This only needs commutative-monoid superposition, not additive inverses or biproducts. -/
theorem Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id
    {ι : Type*} [Fintype ι] {c : C} (x : ι → Effect c)
    (hx : ∑ i, x i ≫ (x i)† = 𝟙 c) (a : State c) [IsIsometry a] :
    ∑ i, probability a (x i) = 1 := by
  apply End.ext
  rw [Semiadditive.end_sum_asHom]
  calc ∑ i, (probability a (x i)).asHom
      = a ≫ (∑ i, x i ≫ (x i)†) ≫ a† := by
        simp only [Semiadditive.comp_sum, Semiadditive.sum_comp, Category.assoc]
    _ = a ≫ a† := by rw [hx, Category.id_comp]
    _ = 𝟙 (𝟙_ C) := ‹IsIsometry a›.comp_dagger_eq_id

end ProbabilityAdditive

section ProbabilityBicone

variable [Semiadditive C] {κ : Type*} [Fintype κ]
  (b : Bicone (fun _ : κ ↦ 𝟙_ C)) (hb : b.IsBilimit) [b.IsDagger]
  (x : κ → Effect c)

/-- A finite explicit dagger-biproduct lift is the sum of its rank-one pieces.
This identity only requires commutative-monoid superposition. -/
theorem Effect.bicone_lift_comp_dagger_eq_sum :
    b.lift hb x ≫ (b.lift hb x)† = ∑ i, x i ≫ (x i)† := by
  calc
    b.lift hb x ≫ (b.lift hb x)† =
        b.lift hb x ≫ (∑ i, b.π i ≫ b.ι i) ≫ (b.lift hb x)† := by
      rw [b.total hb, Category.id_comp]
    _ = ∑ i, x i ≫ (x i)† := by
      rw [← Category.assoc, Semiadditive.comp_sum, Semiadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Category.assoc, b.lift_π hb x, Category.assoc,
        Effect.iota_bicone_lift_dagger b hb x]

end ProbabilityBicone

section BornRuleBicone

variable [Preadditive C] {κ : Type*} [Fintype κ]
  (b : Bicone (fun _ : κ ↦ 𝟙_ C)) (hb : b.IsBilimit) [b.IsDagger]
  (x : κ → Effect c)

include b hb in
/-- The corrected **Born rule** for complete disjoint effects with an explicit witness. -/
theorem Effect.sum_probability_eq_one_of_complete_disjoint_bicone
    (hx : Effect.Complete x) (hxd : Effect.Disjoint x)
    (a : State c) [IsIsometry a] : ∑ i, probability a (x i) = 1 := by
  have hu := Effect.isUnitary_bicone_lift_of_complete_disjoint b hb x hx hxd
  apply Effect.sum_probability_eq_one_of_sum_comp_dagger_eq_id x _ a
  rw [← Effect.bicone_lift_comp_dagger_eq_sum b hb x]
  exact hu.comp_dagger_eq_id

end BornRuleBicone

section BornRule

variable [Preadditive C] (x : ι → Effect c) [HasBiproduct (fun _ : ι ↦ 𝟙_ C)]
  [IsDaggerBiproduct (fun _ : ι ↦ 𝟙_ C)]

/-- `x ≫ x†` is the sum of the rank-one pieces `xᵢ ≫ xᵢ†` — the diagonal part of the
matrix computation in Lemma 2.52. Uses finite bilimit identity resolution and Definition 2.39. -/
theorem Effect.lift_comp_dagger_eq_sum :
    biproduct.lift x ≫ (biproduct.lift x)† = ∑ i, x i ≫ (x i)† :=
  Effect.bicone_lift_comp_dagger_eq_sum
    (biproduct.bicone (fun _ : ι ↦ 𝟙_ C)) (biproduct.isBilimit _) x

/-- A corrected form of **Proposition 2.55 (the Born rule)**: for a finite complete disjoint
family of effects with an invertible superposition rule and an isometric state, probabilities
sum to `1`.

The printed statement omits both `Disjoint` and the invertible superposition assumption.
The latter is used by Lemma 2.53; see the file header for the scope of this correction. -/
theorem Effect.sum_probability_eq_one (hx : Effect.Complete x) (hxd : Effect.Disjoint x)
    (a : State c) [IsIsometry a] : (∑ i, probability a (x i)) = 1 :=
  Effect.sum_probability_eq_one_of_complete_disjoint_bicone
    (biproduct.bicone (fun _ : ι ↦ 𝟙_ C)) (biproduct.isBilimit _) x hx hxd a

end BornRule

end CategoryTheory.MonoidalCategory
