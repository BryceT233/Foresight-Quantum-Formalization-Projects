/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import FQFP.CQM.Category.DaggerRigid
public import FQFP.CQM.QuditCat.Monoidal

/-!
# Self-duality of a finite-dimensional Hilbert space

A finite-dimensional complex Hilbert space is its own dual, but the identification is not
canonical: it is determined by the choice of an orthonormal basis, with coevaluation the
maximally entangled state `∑ i, b i ⊗ b i` and evaluation the bilinear form that multiplies the
two coordinates. This file constructs that pairing from an explicit basis
(`exactPairingOfOrthonormalBasis`) and records its two snake equations, checked on pure tensors.
The self-dual pairing of the standard space `ℂⁿ` is the special case of the computational basis,
`RelCat`'s counterpart being `FQFP.CQM.RelCat.Rigid`.

The evaluation is the dagger of the coevaluation (`dagger_basisCoevaluation`), so the pairing is
invariant under the dagger: reversing it as in Lemma 3.45 returns the same coevaluation and
evaluation (`exactPairingDagger_self`).

The pairing here is `ExactPairing H H`, that is `H` paired with itself along a chosen orthonormal
basis, and it is *not* the canonical pairing of the book's Example 3.2, which pairs `H` with its
dual Hilbert space `H*`. The difference is visible in the cup: in `H ⊗ H*` the phases of a change
of orthonormal basis cancel, so the book's cup is independent of the basis (**Lemma 3.5**),
whereas in `H ⊗ H` they do not, so the cup of this file depends on the basis. Reaching the
canonical pairing would need an `InnerProductSpace` structure on `StrongDual ℂ H.state`, obtained
from the conjugate-linear Riesz equivalence `InnerProductSpace.toDual`; Mathlib does not provide
one, and this file does not construct it.

## Main definitions

* `QuditCat.basisForm`: the bilinear form multiplying the coordinates in an orthonormal basis.
* `QuditCat.basisCoevaluation`, `QuditCat.basisEvaluation`: its coevaluation and evaluation.
* `QuditCat.exactPairingOfOrthonormalBasis`: an exact pairing of a space with itself, from a
  chosen orthonormal basis.
* `QuditCat.instExactPairingStd`, `QuditCat.instHasRightDualStd`, `QuditCat.instHasLeftDualStd`:
  the standard space `ℂⁿ` is self-dual.

## Main results

* `QuditCat.basisForm_apply_basis`: the form on a basis vector is the corresponding bra.
* `QuditCat.coevaluation_evaluation`, `QuditCat.evaluation_coevaluation`: the two snake
  equations.
* `QuditCat.dagger_basisCoevaluation`: the evaluation is the dagger of the coevaluation.
* `QuditCat.exactPairingDagger_self`: the self-dual pairing is invariant under the dagger.

## Implementation notes

Only the standard spaces get an instance: an arbitrary object carries no canonical self-duality,
so for a general object the basis is an explicit argument. The physical identification of a qudit
with its dual therefore always comes with data, and the basis is a parameter of the construction
rather than hidden in an instance.

The evaluation is bilinear, not sesquilinear: the inner product is conjugate-linear in its first
argument, whereas an `ExactPairing` needs two complex-linear maps. Mathematically the pairing is
the one of the conjugate space `H ⊗ H ⟶ ℂ`, transported to `H ⊗ H` along the basis-dependent
isomorphism from `H` to its conjugate space. This is why the self-duality is a choice of basis,
and why the transpose `rightAdjointMate` is the plain transpose rather than the dagger.

The snakes are computed on pure tensors. The coordinate of a basis vector is evaluated with
`Finset.sum_eq_single`, and the sums are collapsed with `OrthonormalBasis.sum_repr'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.DaggerCategory
open scoped TensorProduct

namespace QuditCat

noncomputable section

variable {H : QuditCat} {ι : Type*} [Fintype ι]

/-! ### The bilinear form determined by an orthonormal basis -/

/-- The bilinear form that multiplies the coordinates of two vectors in an orthonormal basis:
`(x, y) ↦ ∑ i, ⟪b i, x⟫ * ⟪b i, y⟫`. It is the evaluation of the self-dual pairing, and it is
complex bilinear in both arguments, unlike the inner product. -/
def basisForm (b : OrthonormalBasis ι ℂ H.state) : H.state →ₗ[ℂ] H.state →ₗ[ℂ] ℂ :=
  ∑ i, (bra (b i)).smulRight (bra (b i))

/-- The bilinear form is the sum of the products of coordinates. -/
lemma basisForm_apply (b : OrthonormalBasis ι ℂ H.state) (x y : H.state) :
    basisForm b x y = ∑ i, bra (b i) x * bra (b i) y := by
  simp [basisForm, LinearMap.sum_apply, LinearMap.smulRight_apply]

/-- On a basis vector the form is the corresponding bra functional: the coordinates of `b j` are
`1` at `j` and `0` elsewhere. -/
lemma basisForm_apply_basis (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (j : ι) :
    basisForm b x (b j) = bra (b j) x := by
  classical
  rw [basisForm_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [b.inner_eq_zero hij]
  · intro hj
    simp at hj

/-- The form is symmetric in its two arguments. -/
lemma basisForm_comm (b : OrthonormalBasis ι ℂ H.state) (x y : H.state) :
    basisForm b x y = basisForm b y x := by
  simp [basisForm_apply, mul_comm]

/-! ### The self-dual pairing determined by an orthonormal basis -/

/-- The coevaluation `𝟙_ ⟶ H ⊗ H` of the self-dual pairing: the maximally entangled state
`∑ i, b i ⊗ b i` of the basis. -/
def basisCoevaluation (b : OrthonormalBasis ι ℂ H.state) : 𝟙_ QuditCat ⟶ H ⊗ H :=
  ofHom (LinearMap.toSpanSingleton ℂ (H.state ⊗[ℂ] H.state) (∑ i, b i ⊗ₜ[ℂ] b i))

/-- The evaluation `H ⊗ H ⟶ 𝟙_` of the self-dual pairing: the bilinear form `basisForm`. -/
def basisEvaluation (b : OrthonormalBasis ι ℂ H.state) : H ⊗ H ⟶ 𝟙_ QuditCat :=
  ofHom (TensorProduct.lift (basisForm b))

/-- The coevaluation sends a scalar to the corresponding multiple of the entangled state. -/
@[simp]
lemma basisCoevaluation_apply (b : OrthonormalBasis ι ℂ H.state) (c : ℂ) :
    (basisCoevaluation b) c = c • ∑ i, b i ⊗ₜ[ℂ] b i := rfl

/-- The underlying linear map of the coevaluation is the span of the entangled state. -/
lemma hom_basisCoevaluation (b : OrthonormalBasis ι ℂ H.state) :
    (basisCoevaluation b).hom = LinearMap.toSpanSingleton ℂ (H.state ⊗[ℂ] H.state)
      (∑ i, b i ⊗ₜ[ℂ] b i) := rfl

/-- The evaluation on a pure tensor is the bilinear form. -/
@[simp]
lemma basisEvaluation_apply (b : OrthonormalBasis ι ℂ H.state) (x y : H.state) :
    (basisEvaluation b) (x ⊗ₜ[ℂ] y) = basisForm b x y := by
  rw [basisEvaluation, ofHom_apply, TensorProduct.lift.tmul]

/-- The evaluation on `x ⊗ b j` is the `j`-th coordinate functional. -/
lemma basisEvaluation_apply_basis (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (j : ι) :
    (basisEvaluation b) (x ⊗ₜ[ℂ] b j) = bra (b j) x := by
  rw [basisEvaluation_apply]
  exact basisForm_apply_basis b x j

/-! ### The snake equations -/

/-- Distributing a tensor of a scalar multiple of the entangled state over the sum. -/
lemma tmul_smul_sum_tmul (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (c : ℂ) :
    x ⊗ₜ[ℂ] (c • ∑ i, b i ⊗ₜ[ℂ] b i)
      = c • ∑ i, x ⊗ₜ[ℂ] (b i ⊗ₜ[ℂ] b i) := by
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_sum, Finset.smul_sum]

/-- The same distribution for the entangled state as the left tensor factor. -/
lemma smul_sum_tmul (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (c : ℂ) :
    (c • ∑ i, b i ⊗ₜ[ℂ] b i) ⊗ₜ[ℂ] x
      = c • ∑ i, (b i ⊗ₜ[ℂ] b i) ⊗ₜ[ℂ] x := by
  rw [← TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]

/-- The sum `∑ i, ⟪b i, x⟫ ⊗ b i` is the tensor `1 ⊗ x`: the basis expansion of `x`. -/
lemma sum_bra_tmul (b : OrthonormalBasis ι ℂ H.state) (x : H.state) :
    ∑ i, bra (b i) x ⊗ₜ[ℂ] b i = (1 : ℂ) ⊗ₜ[ℂ] x := by
  conv_rhs => rw [← b.sum_repr' x, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bra_apply]
  simpa using
    (TensorProduct.smul_tmul (R := ℂ) (r := inner ℂ (b i) x) (m := (1 : ℂ)) (n := b i))

/-- The sum `∑ i, b i ⊗ ⟪b i, x⟫` is the tensor `x ⊗ 1`, the mirror image of
`sum_bra_tmul`. -/
lemma sum_tmul_bra (b : OrthonormalBasis ι ℂ H.state) (x : H.state) :
    ∑ i, b i ⊗ₜ[ℂ] bra (b i) x = x ⊗ₜ[ℂ] (1 : ℂ) := by
  conv_rhs => rw [← b.sum_repr' x, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bra_apply]
  simpa using
    (TensorProduct.smul_tmul (R := ℂ) (r := inner ℂ (b i) x) (m := b i) (n := (1 : ℂ))).symm

/-- The first snake equation, evaluated on a pure tensor. -/
lemma coevaluation_evaluation_apply (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (c : ℂ) :
    (basisEvaluation b ▷ H) ((α_ H H H).inv ((H ◁ basisCoevaluation b)
      (x ⊗ₜ[ℂ] c))) = (1 : ℂ) ⊗ₜ[ℂ] (c • x) := by
  have hterm : ∀ i : ι,
      (basisEvaluation b ▷ H) ((α_ H H H).inv (x ⊗ₜ[ℂ] (b i ⊗ₜ[ℂ] b i)))
        = bra (b i) x ⊗ₜ[ℂ] b i := by
    intro i
    rw [associator_inv_apply, whiskerRight_apply, basisEvaluation_apply]
    exact congrArg (· ⊗ₜ[ℂ] b i) (basisForm_apply_basis b x i)
  rw [whiskerLeft_apply, basisCoevaluation_apply,
    tmul_smul_sum_tmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm]
  rw [sum_bra_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul]

/-- The second snake equation, evaluated on a pure tensor. -/
lemma evaluation_coevaluation_apply (b : OrthonormalBasis ι ℂ H.state) (x : H.state) (c : ℂ) :
    (H ◁ basisEvaluation b) ((α_ H H H).hom ((basisCoevaluation b ▷ H)
      (c ⊗ₜ[ℂ] x))) = (c • x) ⊗ₜ[ℂ] (1 : ℂ) := by
  have hterm : ∀ i : ι,
      (H ◁ basisEvaluation b) ((α_ H H H).hom ((b i ⊗ₜ[ℂ] b i) ⊗ₜ[ℂ] x))
        = b i ⊗ₜ[ℂ] bra (b i) x := by
    intro i
    rw [associator_hom_apply, whiskerLeft_apply, basisEvaluation_apply, basisForm_comm]
    exact congrArg (b i ⊗ₜ[ℂ] ·) (basisForm_apply_basis b x i)
  rw [whiskerRight_apply, basisCoevaluation_apply, smul_sum_tmul,
    map_smul, map_sum, map_smul, map_sum]
  simp only [hterm]
  rw [sum_tmul_bra, TensorProduct.smul_tmul']

set_option backward.isDefEq.respectTransparency.types false in
/-- The first snake equation for the basis pairing. -/
lemma coevaluation_evaluation (b : OrthonormalBasis ι ℂ H.state) :
    (H ◁ basisCoevaluation b) ≫ (α_ H H H).inv ≫ (basisEvaluation b ▷ H)
      = (ρ_ H).hom ≫ (λ_ H).inv := by
  apply hom_ext
  apply TensorProduct.ext'
  intro x c
  change (basisEvaluation b ▷ H) ((α_ H H H).inv ((H ◁ basisCoevaluation b) (x ⊗ₜ[ℂ] c)))
    = (λ_ H).inv ((ρ_ H).hom (x ⊗ₜ[ℂ] c))
  rw [coevaluation_evaluation_apply b x c, rightUnitor_hom_apply, leftUnitor_inv_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The second snake equation for the basis pairing. -/
lemma evaluation_coevaluation (b : OrthonormalBasis ι ℂ H.state) :
    (basisCoevaluation b ▷ H) ≫ (α_ H H H).hom ≫ (H ◁ basisEvaluation b)
      = (λ_ H).hom ≫ (ρ_ H).inv := by
  apply hom_ext
  apply TensorProduct.ext'
  intro c x
  change (H ◁ basisEvaluation b) ((α_ H H H).hom ((basisCoevaluation b ▷ H) (c ⊗ₜ[ℂ] x)))
    = (ρ_ H).inv ((λ_ H).hom (c ⊗ₜ[ℂ] x))
  rw [evaluation_coevaluation_apply b x c, leftUnitor_hom_apply, rightUnitor_inv_apply]

/-- A finite-dimensional Hilbert space is its own dual, given an orthonormal basis: the
coevaluation is the maximally entangled state of that basis and the evaluation multiplies its
coordinates. Since the identification is not canonical, the basis is an explicit argument. -/
abbrev exactPairingOfOrthonormalBasis (b : OrthonormalBasis ι ℂ H.state) : ExactPairing H H where
  coevaluation' := basisCoevaluation b
  evaluation' := basisEvaluation b
  coevaluation_evaluation' := coevaluation_evaluation b
  evaluation_coevaluation' := evaluation_coevaluation b

/-- The standard space `ℂⁿ` is self-dual, via its computational basis. This is a concrete
realization for the standard spaces and does not assert a canonical self-duality of an arbitrary
qudit. -/
instance instExactPairingStd (n : ℕ) : ExactPairing (std n) (std n) :=
  exactPairingOfOrthonormalBasis (ZBasis n)

/-! ### Compatibility with the dagger -/

set_option backward.isDefEq.respectTransparency.types false in
/-- The evaluation is the dagger of the coevaluation: adjunction of the maximally entangled
state is the coordinate-multiplication form. Unlike the self-duality itself, this statement does
not depend on the choice of basis. -/
lemma dagger_basisCoevaluation (b : OrthonormalBasis ι ℂ H.state) :
    (basisCoevaluation b)† = basisEvaluation b := by
  apply hom_ext
  apply TensorProduct.ext'
  intro x y
  rw [hom_dagger, hom_basisCoevaluation,
    LinearMap.adjoint_toSpanSingleton (𝕜 := ℂ) (E := H.state ⊗[ℂ] H.state)
      (x := ∑ i, b i ⊗ₜ[ℂ] b i),
    basisEvaluation_apply, basisForm_apply]
  simp only [coe_innerₛₗ_apply, sum_inner, TensorProduct.inner_tmul, bra_apply]

/-- The self-dual pairing of an orthonormal basis is invariant under the dagger: reversing it as
in Lemma 3.45 returns the same coevaluation and evaluation. -/
theorem exactPairingDagger_self (b : OrthonormalBasis ι ℂ H.state) :
    (exactPairingDagger H H (exactPairingOfOrthonormalBasis b)).coevaluation'
        = basisCoevaluation b ∧
      (exactPairingDagger H H (exactPairingOfOrthonormalBasis b)).evaluation'
        = basisEvaluation b := by
  refine ⟨?_, ?_⟩
  · rw [exactPairingDagger_coevaluation]
    change (basisEvaluation b)† = basisCoevaluation b
    rw [← dagger_basisCoevaluation b, involutive_dagger]
  · rw [exactPairingDagger_evaluation]
    change (basisCoevaluation b)† = basisEvaluation b
    rw [dagger_basisCoevaluation]

/-! ### Duals of the standard spaces -/

/-- The standard space `ℂⁿ` has itself as right dual. -/
instance instHasRightDualStd (n : ℕ) : HasRightDual (std n) where
  rightDual := std n
  exact := exactPairingOfOrthonormalBasis (ZBasis n)

/-- The standard space `ℂⁿ` has itself as left dual. -/
instance instHasLeftDualStd (n : ℕ) : HasLeftDual (std n) where
  leftDual := std n
  exact := exactPairingOfOrthonormalBasis (ZBasis n)

/-- Instance search selects the computational-basis pairing of `std n`: its cup is the maximally
entangled state of `ZBasis n`. This lemma records the witness chosen by search, which a
computation on a standard object may rely on. -/
lemma instExactPairingStd_coevaluation (n : ℕ) :
    η_ (std n) (std n) = basisCoevaluation (ZBasis n) := rfl

/-- Instance search selects the computational-basis pairing of `std n`: its cap is the
coordinate-multiplication form of `ZBasis n`. -/
lemma instExactPairingStd_evaluation (n : ℕ) :
    ε_ (std n) (std n) = basisEvaluation (ZBasis n) := rfl

end

end QuditCat
