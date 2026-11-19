/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.Operator
public import FQFP.CQM.Qudit.Dagger
public import FQFP.CQM.Qudit.Monoidal
public import FQFP.Analysis.InnerProductSpace.PositiveTrace
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Operators on a qudit

`Qudit.endAlgEquiv` interprets a categorical operator as a linear endomorphism of
the underlying complex space. The qudit operator API uses this linear representation.
`outer v w` is the linear map `x ↦ inner ℂ w x • v`.
Its trace is `inner ℂ w v`, and `outer v v` is positive without any normalization assumption.

Coordinates use Mathlib's `LinearMap.toMatrixOrthonormal`; no second matrix algebra is defined.

## Main definitions and results

* `Qudit.Operator`: linear endomorphisms of a qudit.
* `Qudit.Operator.trace_outer`: the trace of an outer product is its inner product.
* `Qudit.Operator.sum_outer_basis`: expansion of an operator in an orthonormal basis.
* `Qudit.Operator.exists_sum_outer_of_isPositive`: positive operators are finite sums of outer
  squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory
open scoped ComplexOrder

namespace Qudit

/-- The algebra of linear operators on a qudit. -/
abbrev Operator (H : Qudit) := Module.End ℂ H.state

noncomputable section

instance {H K : Qudit} : SMul ℂ (H ⟶ K) where
  smul c f := ofHom (c • f.hom)

/-- Scalar multiplication of qudit arrows acts on their underlying linear maps. -/
@[simp] lemma hom_smul {H K : Qudit} (c : ℂ) (f : H ⟶ K) : (c • f).hom = c • f.hom := rfl

instance : Linear ℂ Qudit where
  homModule H K := Function.Injective.module ℂ
    (⟨⟨Hom.hom, hom_zero⟩, hom_add⟩ : (H ⟶ K) →+ (H.state →ₗ[ℂ] K.state))
    hom_injective hom_smul
  smul_comp _ _ _ c f g := hom_ext (g.hom.comp_smul c f.hom)
  comp_smul _ _ _ _ _ _ := hom_ext rfl

/-- Categorical operators on a qudit form the complex algebra of linear endomorphisms. -/
def endAlgEquiv (H : Qudit) : CQM.Operator H ≃ₐ[ℂ] Operator H :=
  AlgEquiv.ofLinearEquiv
    { toEquiv := End.homEquiv.trans homEquiv
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } rfl (fun _ _ ↦ rfl)

/-- The linear operator represented by a categorical endomorphism. -/
@[simp] lemma endAlgEquiv_apply {H : Qudit} (A : CQM.Operator H) :
    endAlgEquiv H A = A.asHom.hom := rfl

/-- The categorical star is represented by the Hilbert space adjoint. -/
lemma endAlgEquiv_star {H : Qudit} (A : CQM.Operator H) :
    endAlgEquiv H (star A) = (endAlgEquiv H A).adjoint := rfl

end

namespace Operator

variable {H : Qudit}

/-- The basis-independent complex trace. -/
noncomputable abbrev trace (A : Operator H) : ℂ := LinearMap.trace ℂ H.state A

/-- The outer product `∣v⟩⟨w∣`, allowing unnormalized vectors. -/
noncomputable def outer (v w : H.state) : Operator H := (bra w).smulRight v

/-- An outer product acts by an inner product followed by scalar multiplication. -/
@[simp]
lemma outer_apply (v w x : H.state) : outer v w x = inner ℂ w x • v := rfl

/-- An outer product is the composite of a bra followed by a ket. -/
lemma outer_eq_ket_comp_bra (v w : H.state) : outer v w = ket v ∘ₗ bra w := rfl

/-- Interpreting a categorical outer product of kets gives the linear outer product. -/
lemma endAlgEquiv_outer (v w : H.state) :
    endAlgEquiv H (CQM.Operator.outer (ketArrow v) (ketArrow w)) = outer v w := by
  simp only [endAlgEquiv_apply, CQM.Operator.outer_asHom, ketArrow_dagger, hom_comp]
  rfl

/-- The adjoint of an outer product exchanges its vectors. -/
@[simp]
lemma adjoint_outer (v w : H.state) : (outer v w).adjoint = outer w v := by
  rw [← endAlgEquiv_outer, ← endAlgEquiv_star, CQM.Operator.star_outer, endAlgEquiv_outer]

/-- The trace of an outer product is the corresponding inner product. -/
@[simp]
lemma trace_outer (v w : H.state) : (outer v w).trace = inner ℂ w v :=
  LinearMap.trace_smulRight (bra w) v

/-- The outer square of any vector is positive. -/
lemma isPositive_outer (v : H.state) : (outer v v).IsPositive := by
  rw [← endAlgEquiv_outer]
  exact hom_isPositive_of_isPositive (CQM.Operator.outer (ketArrow v) (ketArrow v)).asHom

/-- Multiplying an outer product on the left applies the operator to its ket. -/
lemma mul_outer (A : Operator H) (v w : H.state) : A * outer v w = outer (A v) w := by
  ext x
  simp only [mul_apply_eq_comp, outer_apply, map_smul]

/-- The trace pairing against an outer product is a matrix coefficient. -/
@[simp]
lemma trace_mul_outer (A : Operator H) (v w : H.state) :
    (A * outer v w).trace = inner ℂ w (A v) := by
  rw [mul_outer, trace_outer]

/-- Scaling both vectors of an outer square scales it by the squared modulus. -/
lemma outer_smul_self (c : ℂ) (v : H.state) :
    outer (c • v) (c • v) = (‖c‖ ^ 2 : ℂ) • outer v v := by
  ext x
  simp only [outer_apply, inner_smul_left, smul_smul, LinearMap.smul_apply]
  congr 1
  calc
    (starRingEnd ℂ c * inner ℂ v x) * c =
        (c * starRingEnd ℂ c) * inner ℂ v x := by ring
    _ = _ := by rw [Complex.mul_conj']

/-- Multiplying a vector by a global phase does not change its outer square. -/
lemma outer_smul_self_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) (v : H.state) :
    outer (c • v) (c • v) = outer v v := by
  rw [outer_smul_self, hc]
  simp

/-- Orthonormal coordinates preserve positivity in both directions. -/
lemma posSemidef_toMatrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (LinearMap.toMatrixOrthonormal b A).PosSemidef ↔ A.IsPositive :=
  LinearMap.posSemidef_toMatrix_iff b

/-- Orthonormal coordinates preserve the trace. -/
lemma trace_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (LinearMap.toMatrixOrthonormal b A).trace = A.trace :=
  (LinearMap.trace_eq_matrix_trace ℂ b.toBasis A).symm

/-- The trace of an adjoint is the conjugate trace. -/
lemma trace_adjoint (A : Operator H) : trace A.adjoint = star A.trace := by
  classical
  let b := stdOrthonormalBasis ℂ H.state
  change LinearMap.trace ℂ H.state A.adjoint = star (LinearMap.trace ℂ H.state A)
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    LinearMap.toMatrix_adjoint b b, Matrix.trace_conjTranspose]

variable {ι : Type*} [Fintype ι]

/-- Outer products distribute over finite sums in their ket. -/
lemma outer_sum_left (v : ι → H.state) (w : H.state) :
    outer (∑ i, v i) w = ∑ i, outer (v i) w := by
  ext x
  simp [Finset.smul_sum]

/-- Outer products distribute over finite sums in their bra. -/
lemma outer_sum_right (v : H.state) (w : ι → H.state) :
    outer v (∑ i, w i) = ∑ i, outer v (w i) := by
  ext x
  simp [sum_inner, Finset.sum_smul]

/-- Scaling the ket scales an outer product linearly. -/
lemma outer_smul_left (c : ℂ) (v w : H.state) : outer (c • v) w = c • outer v w := by
  ext x
  simp [smul_smul, mul_comm]

/-- Expansion of an operator into its basis columns. -/
lemma sum_outer_basis (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    ∑ i, outer (A (b i)) (b i) = A := by
  ext x
  simpa only [LinearMap.sum_apply, outer_apply, ← map_smul, ← map_sum] using
    congrArg A (b.sum_repr' x)

/-- The quadratic form of an operator with a real orthonormal diagonalization. -/
lemma re_inner_apply_eq_sum_of_eigenbasis (b : OrthonormalBasis ι ℂ H.state) (A : Operator H)
    (w : ι → ℝ) (hw : ∀ i, A (b i) = (w i : ℂ) • b i) (v : H.state) :
    (inner ℂ v (A v)).re = ∑ i, w i * ‖inner ℂ (b i) v‖ ^ 2 := by
  rw [← sum_outer_basis b A]
  simp only [LinearMap.sum_apply, hw, outer_smul_left, LinearMap.smul_apply, outer_apply,
    inner_sum, inner_smul_right, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← inner_conj_symm v (b i), Complex.mul_conj']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- A linear map on operators is determined on basis matrix units. -/
lemma basis_outer_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : OrthonormalBasis ι ℂ H.state) {f g : Operator H →ₗ[ℂ] V}
    (h : ∀ i j, f (outer (b i) (b j)) = g (outer (b i) (b j))) : f = g := by
  apply LinearMap.ext
  intro A
  rw [← sum_outer_basis b A, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← b.sum_repr' (A (b j)), outer_sum_left, map_sum, map_sum]
  simp only [outer_smul_left, map_smul, h]

/-- A positive operator has an outer-product decomposition with exactly `finrank` terms.
Zero eigenvalues contribute zero vectors, so singular and zero-dimensional cases are included. -/
lemma exists_sum_outer_of_isPositive (A : Operator H) (hA : A.IsPositive) :
    ∃ v : Fin (Module.finrank ℂ H.state) → H.state, A = ∑ i, outer (v i) (v i) := by
  let b := hA.isSymmetric.eigenvectorBasis rfl
  let v (i : Fin (Module.finrank ℂ H.state)) : H.state :=
    (Real.sqrt (hA.isSymmetric.eigenvalues rfl i) : ℂ) • b i
  refine ⟨v, (sum_outer_basis b A).symm.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [v, b]
  rw [hA.isSymmetric.apply_eigenvectorBasis, outer_smul_left, outer_smul_self]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ← Complex.ofReal_pow, Real.sq_sqrt (hA.nonneg_eigenvalues rfl i)]
  rfl

end Operator

end Qudit
