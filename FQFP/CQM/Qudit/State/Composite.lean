/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.InnerProductSpace.PartialTrace
public import FQFP.CQM.Qudit.State.Density
public import FQFP.CQM.Qudit.Monoidal

/-!
# Composite systems and reduced density operators

Tensor products use the existing Hilbert tensor product of `Qudit`.
`partialTraceRight` discards the right factor, and `partialTraceLeft` discards the left.
Both are basis-independent linear maps on all operators and preserve positivity and trace.
Their restrictions to density operators therefore require no additional normalization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ComplexOrder

namespace Qudit

noncomputable section

variable {H K : Qudit}

/-- The tensor product of two unit vectors. -/
def UnitState.tensor (v : UnitState H) (w : UnitState K) : UnitState (H ⊗ K) :=
  ⟨v.val ⊗ₜ[ℂ] w.val, by
    change inner ℂ (v.val ⊗ₜ[ℂ] w.val) (v.val ⊗ₜ[ℂ] w.val) = 1
    rw [TensorProduct.inner_tmul, v.inner_self, w.inner_self, one_mul]⟩

/-- The vector underlying a product unit state. -/
@[simp]
lemma UnitState.coe_tensor (v : UnitState H) (w : UnitState K) :
    (v.tensor w).val = v.val ⊗ₜ[ℂ] w.val := rfl

/-- A bipartite unit vector is a product if it is exactly a tensor of two unit vectors.
Any global phase can be absorbed into either factor. -/
def UnitState.IsProduct (v : UnitState (H ⊗ K)) : Prop :=
  ∃ (x : UnitState H) (y : UnitState K), v = x.tensor y

/-- The tensor of two unit vectors is a product vector. -/
lemma UnitState.isProduct_tensor (v : UnitState H) (w : UnitState K) :
    (v.tensor w).IsProduct := ⟨v, w, rfl⟩

/-- Exchange the tensor factors of a bipartite unit vector. -/
def UnitState.swap (v : UnitState (H ⊗ K)) : UnitState (K ⊗ H) :=
  ⟨TensorProduct.comm ℂ H.state K.state v.val, by
    change inner ℂ (TensorProduct.comm ℂ H.state K.state v.val)
      (TensorProduct.comm ℂ H.state K.state v.val) = 1
    rw [TensorProduct.inner_comm_comm, v.inner_self]⟩

/-- Exchanging the tensor factors twice recovers the original unit vector. -/
lemma UnitState.swap_swap (v : UnitState (H ⊗ K)) : v.swap.swap = v := by
  apply Subtype.ext
  exact (TensorProduct.comm ℂ H.state K.state).symm_apply_apply v.val

/-- Exchanging the tensor factors of a product vector exchanges its two unit factors. -/
lemma UnitState.swap_tensor (v : UnitState H) (w : UnitState K) :
    (v.tensor w).swap = w.tensor v := by
  apply Subtype.ext
  exact TensorProduct.comm_tmul _ _ _ _ _

/-- Being a product vector is independent of the ordering of the two systems. -/
lemma UnitState.isProduct_swap_iff (v : UnitState (H ⊗ K)) :
    v.swap.IsProduct ↔ v.IsProduct := by
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨y, x, by simpa only [swap_swap, swap_tensor] using congrArg UnitState.swap h⟩
  · rintro ⟨x, y, rfl⟩
    rw [swap_tensor]
    exact isProduct_tensor _ _

namespace Operator

/-- The tensor product of two operators on qudits. -/
def tensor (A : Operator H) (B : Operator K) : Operator (H ⊗ K) := TensorProduct.map A B

/-- A product operator acts separately on the two factors. -/
@[simp]
lemma tensor_apply (A : Operator H) (B : Operator K) (x : H.state) (y : K.state) :
    tensor A B (x ⊗ₜ[ℂ] y) = A x ⊗ₜ[ℂ] B y := rfl

/-- The trace of a product operator is the product of its traces. -/
@[simp]
lemma trace_tensor (A : Operator H) (B : Operator K) :
    (tensor A B).trace = A.trace * B.trace := LinearMap.trace_tensorProduct' A B

/-- Tensor products of positive operators are positive. -/
lemma isPositive_tensor {A : Operator H} {B : Operator K}
    (hA : A.IsPositive) (hB : B.IsPositive) : (tensor A B).IsPositive :=
  hA.tensorProduct hB

/-- Outer products commute with tensor products. -/
lemma tensor_outer (x y : H.state) (u v : K.state) :
    tensor (outer x y) (outer u v) = outer (x ⊗ₜ[ℂ] u) (y ⊗ₜ[ℂ] v) :=
  LinearMap.map_rankOne x y u v

/-- The right partial trace, discarding `K`. -/
abbrev partialTraceRight : Operator (H ⊗ K) →ₗ[ℂ] Operator H :=
  LinearMap.partialTraceRight

/-- The left partial trace, discarding `H`. -/
abbrev partialTraceLeft : Operator (H ⊗ K) →ₗ[ℂ] Operator K :=
  LinearMap.partialTraceLeft

/-- Compute a right partial trace in any orthonormal basis of the discarded factor. -/
lemma inner_partialTraceRight {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) (A : Operator (H ⊗ K)) (x y : H.state) :
    inner ℂ x (partialTraceRight A y) = ∑ i, inner ℂ (x ⊗ₜ[ℂ] b i) (A (y ⊗ₜ[ℂ] b i)) := by
  rw [partialTraceRight, LinearMap.partialTraceRight_eq b,
    LinearMap.inner_partialTraceRightWith]

/-- Compute a left partial trace in any orthonormal basis of the discarded factor. -/
lemma inner_partialTraceLeft {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (A : Operator (H ⊗ K)) (x y : K.state) :
    inner ℂ x (partialTraceLeft A y) = ∑ i, inner ℂ (b i ⊗ₜ[ℂ] x) (A (b i ⊗ₜ[ℂ] y)) :=
  LinearMap.inner_partialTraceLeft b A x y

/-- Right partial trace of a product operator. -/
@[simp]
lemma partialTraceRight_tensor (A : Operator H) (B : Operator K) :
    partialTraceRight (tensor A B) = B.trace • A := LinearMap.partialTraceRight_map A B

/-- Left partial trace of a product operator. -/
@[simp]
lemma partialTraceLeft_tensor (A : Operator H) (B : Operator K) :
    partialTraceLeft (tensor A B) = A.trace • B := LinearMap.partialTraceLeft_map A B

/-- Discarding an orthonormal label removes cross terms between its distinct labels. -/
lemma partialTraceRight_outer_sum_tmul {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) (v w : ι → H.state) :
    partialTraceRight (outer (∑ i, v i ⊗ₜ[ℂ] b i) (∑ i, w i ⊗ₜ[ℂ] b i)) =
      ∑ i, outer (v i) (w i) := by
  classical
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_partialTraceRight b]
  simp [outer_apply, inner_smul_right, inner_sum, sum_inner,
    TensorProduct.inner_tmul (𝕜 := ℂ) (E := H.state) (F := K.state), b.inner_eq_ite]

/-- The right marginal of the unnormalized maximally entangled vector is the identity.
The vector itself depends on the chosen basis; its marginal does not. -/
lemma partialTraceRight_outer_sum_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    partialTraceRight (outer (∑ i, b i ⊗ₜ[ℂ] b i) (∑ i, b i ⊗ₜ[ℂ] b i)) =
      (1 : Operator H) := by
  rw [partialTraceRight_outer_sum_tmul]
  simpa only [Module.End.one_apply] using sum_outer_basis b (1 : Operator H)

/-- The left marginal of the unnormalized maximally entangled vector is the identity. -/
lemma partialTraceLeft_outer_sum_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    partialTraceLeft (outer (∑ i, b i ⊗ₜ[ℂ] b i) (∑ i, b i ⊗ₜ[ℂ] b i)) =
      (1 : Operator H) := by
  classical
  apply b.toBasis.ext
  intro j
  apply ext_inner_left ℂ
  intro x
  rw [inner_partialTraceLeft b]
  simp only [outer_apply, inner_smul_right, sum_inner, inner_sum]
  simp [TensorProduct.inner_tmul (𝕜 := ℂ) (E := H.state) (F := H.state),
    b.inner_eq_ite, ite_mul]

end Operator

namespace Density

/-- The maximally mixed density operator; the dimension must be nonzero. -/
def maximallyMixed (H : Qudit) (hn : Module.finrank ℂ H.state ≠ 0) : Density H where
  op := (Module.finrank ℂ H.state : ℂ)⁻¹ • (1 : Operator H)
  positive := LinearMap.isPositive_one.smul_of_nonneg (by positivity)
  trace_one := by simp [Operator.trace, LinearMap.trace_one, hn]

/-- The maximally mixed state is the identity divided by the dimension. -/
@[simp]
lemma op_maximallyMixed (H : Qudit) (hn : Module.finrank ℂ H.state ≠ 0) :
    (maximallyMixed H hn).op = (Module.finrank ℂ H.state : ℂ)⁻¹ • (1 : Operator H) := rfl

/-- The independent product of two density operators. -/
def tensor (ρ : Density H) (σ : Density K) : Density (H ⊗ K) where
  op := Operator.tensor ρ.op σ.op
  positive := Operator.isPositive_tensor ρ.positive σ.positive
  trace_one := by rw [Operator.trace_tensor, ρ.trace_one, σ.trace_one, one_mul]

/-- The operator underlying a product density. -/
@[simp]
lemma op_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).op = Operator.tensor ρ.op σ.op := rfl

/-- Embedding pure states commutes with tensor products. -/
lemma tensor_pure (v : UnitState H) (w : UnitState K) :
    (pure v).tensor (pure w) = pure (v.tensor w) := by
  apply Density.ext
  exact Operator.tensor_outer v.val v.val w.val w.val

/-- The reduced density operator on the left factor. -/
def partialTraceRight (ρ : Density (H ⊗ K)) : Density H where
  op := Operator.partialTraceRight ρ.op
  positive := ρ.positive.partialTraceRight
  trace_one := (LinearMap.trace_partialTraceRight ρ.op).trans ρ.trace_one

/-- The reduced density operator on the right factor. -/
def partialTraceLeft (ρ : Density (H ⊗ K)) : Density K where
  op := Operator.partialTraceLeft ρ.op
  positive := ρ.positive.partialTraceLeft
  trace_one := (LinearMap.trace_partialTraceLeft ρ.op).trans ρ.trace_one

/-- Underlying operator of a right partial trace. -/
@[simp]
lemma op_partialTraceRight (ρ : Density (H ⊗ K)) :
    ρ.partialTraceRight.op = Operator.partialTraceRight ρ.op := rfl

/-- Underlying operator of a left partial trace. -/
@[simp]
lemma op_partialTraceLeft (ρ : Density (H ⊗ K)) :
    ρ.partialTraceLeft.op = Operator.partialTraceLeft ρ.op := rfl

/-- Discarding the right factor of a product state recovers the left state. -/
@[simp]
lemma partialTraceRight_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).partialTraceRight = ρ := by
  apply Density.ext
  simp

/-- Discarding the left factor of a product state recovers the right state. -/
@[simp]
lemma partialTraceLeft_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).partialTraceLeft = σ := by
  apply Density.ext
  simp

/-- Reduced density operators reproduce all local complex expectations. -/
lemma expectationComplex_partialTraceRight (ρ : Density (H ⊗ K)) (A : Operator H) :
    ρ.partialTraceRight.expectationComplex A =
      ρ.expectationComplex (Operator.tensor A 1) :=
  LinearMap.trace_mul_partialTraceRight ρ.op A

/-- Reduced density operators reproduce all local real expectations. -/
lemma expectation_partialTraceRight (ρ : Density (H ⊗ K)) (A : Operator H) :
    ρ.partialTraceRight.expectation A = ρ.expectation (Operator.tensor A 1) :=
  congrArg Complex.re (ρ.expectationComplex_partialTraceRight A)

/-- Left reduction reproduces complex expectations of right-factor observables. -/
lemma expectationComplex_partialTraceLeft (ρ : Density (H ⊗ K)) (A : Operator K) :
    ρ.partialTraceLeft.expectationComplex A =
      ρ.expectationComplex (Operator.tensor 1 A) :=
  LinearMap.trace_mul_partialTraceLeft ρ.op A

/-- Left reduction reproduces real expectations of right-factor observables. -/
lemma expectation_partialTraceLeft (ρ : Density (H ⊗ K)) (A : Operator K) :
    ρ.partialTraceLeft.expectation A = ρ.expectation (Operator.tensor 1 A) :=
  congrArg Complex.re (ρ.expectationComplex_partialTraceLeft A)

/-- Right reduction commutes with probabilistic mixing. -/
lemma partialTraceRight_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ σ : Density (H ⊗ K)) :
    (mix p hp₀ hp₁ ρ σ).partialTraceRight =
      mix p hp₀ hp₁ ρ.partialTraceRight σ.partialTraceRight := by
  apply Density.ext
  simp

/-- Left reduction commutes with probabilistic mixing. -/
lemma partialTraceLeft_mix (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ σ : Density (H ⊗ K)) :
    (mix p hp₀ hp₁ ρ σ).partialTraceLeft =
      mix p hp₀ hp₁ ρ.partialTraceLeft σ.partialTraceLeft := by
  apply Density.ext
  simp

/-- Product-basis coordinates of a tensor density have the usual Kronecker entries. -/
lemma toMatrix_tensor_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : OrthonormalBasis ι ℂ H.state)
    (c : OrthonormalBasis κ ℂ K.state) (ρ : Density H) (σ : Density K)
    (i j : ι) (k l : κ) :
    (ρ.tensor σ).toMatrix (b.tensorProduct c) (i, k) (j, l) =
      ρ.toMatrix b i j * σ.toMatrix c k l := by
  simp only [toMatrix, LinearMap.toMatrixOrthonormal_apply_apply, op_tensor,
    OrthonormalBasis.tensorProduct_apply b c, Operator.tensor_apply]
  exact TensorProduct.inner_tmul ℂ (b i) (ρ.op (b j)) (c k) (σ.op (c l))

/-- Right partial trace sums matching right indices in every product orthonormal basis. -/
lemma toMatrix_partialTraceRight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : OrthonormalBasis ι ℂ H.state)
    (c : OrthonormalBasis κ ℂ K.state) (ρ : Density (H ⊗ K)) (i j : ι) :
    ρ.partialTraceRight.toMatrix b i j =
      ∑ k, ρ.toMatrix (b.tensorProduct c) (i, k) (j, k) := by
  simp only [toMatrix, LinearMap.toMatrixOrthonormal_apply_apply, op_partialTraceRight,
    Operator.inner_partialTraceRight c, OrthonormalBasis.tensorProduct_apply b c]

/-- Left partial trace sums matching left indices in every product orthonormal basis. -/
lemma toMatrix_partialTraceLeft {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : OrthonormalBasis ι ℂ H.state)
    (c : OrthonormalBasis κ ℂ K.state) (ρ : Density (H ⊗ K)) (i j : κ) :
    ρ.partialTraceLeft.toMatrix c i j =
      ∑ k, ρ.toMatrix (b.tensorProduct c) (k, i) (k, j) := by
  simp only [toMatrix, LinearMap.toMatrixOrthonormal_apply_apply, op_partialTraceLeft,
    Operator.inner_partialTraceLeft b, OrthonormalBasis.tensorProduct_apply b c]

end Density

end

end Qudit
