/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the Choi positivity criterion and Kraus decomposition.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/Unbundled.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.Channel.RankOne

/-!
# Choi operators and completeness of finite Kraus representations

The Choi operator lives on output tensor input, using an explicit input orthonormal
basis and an unnormalized entangled vector. Complete positivity retains its original
quantification over every finite-dimensional auxiliary system.

The proof strategy follows the Choi criterion and positive spectral decomposition in
physlib `QuantumInfo/Channels/Unbundled.lean`, revision
`29215bb5263ad514047bab124c379d3a01ea1e90`. The implementation uses local coordinate-free
operators and Mathlib's rank-one decomposition, without importing physlib.

## Main definitions and results

* `Qudit.Superoperator.choi`: the Choi operator relative to an orthonormal input basis.
* `Qudit.Superoperator.isCompletelyPositive_iff_choi_positive`: the Choi positivity criterion.
* `Qudit.Superoperator.isCompletelyPositive_iff_exists_kraus`: completeness of finite Kraus
  families.
* `Qudit.QuantumChannel.exists_kraus_finrank`: a normalized Kraus family with a dimension bound.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct ComplexOrder

namespace Qudit

noncomputable section

namespace Superoperator

variable {H K : Qudit} {ι : Type*} [Fintype ι]

/-- Vectorize a linear process in an explicit input basis, with output on the left. -/
def vectorize (b : OrthonormalBasis ι ℂ H.state) :
    (H.state →ₗ[ℂ] K.state) →ₗ[ℂ] (K ⊗ H).state where
  toFun f := ∑ i, f (b i) ⊗ₜ[ℂ] b i
  map_add' f g := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [LinearMap.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul' c (f (b i)) (b i)).symm

/-- The basis-coordinate expansion of a vectorized process. -/
lemma vectorize_apply (b : OrthonormalBasis ι ℂ H.state) (f : H.state →ₗ[ℂ] K.state) :
    vectorize b f = ∑ i, f (b i) ⊗ₜ[ℂ] b i := rfl

/-- Recover a linear process by contracting the reference leg of a vector. -/
def unvectorize (b : OrthonormalBasis ι ℂ H.state) (v : (K ⊗ H).state) :
    H.state →ₗ[ℂ] K.state :=
  b.toBasis.constr ℂ fun i => ((TensorProduct.mk ℂ K.state H.state).flip (b i)).adjoint v

/-- A column of the recovered process is a contraction of the reference leg. -/
lemma unvectorize_basis (b : OrthonormalBasis ι ℂ H.state) (v : (K ⊗ H).state) (i : ι) :
    unvectorize b v (b i) = ((TensorProduct.mk ℂ K.state H.state).flip (b i)).adjoint v :=
  b.toBasis.constr_basis ℂ _ i

/-- Matrix coefficients of vectorization recover the columns of the process. -/
lemma inner_vectorize (b : OrthonormalBasis ι ℂ H.state) (f : H.state →ₗ[ℂ] K.state)
    (x : K.state) (i : ι) :
    inner ℂ (x ⊗ₜ[ℂ] b i) (vectorize b f) = inner ℂ x (f (b i)) := by
  classical
  simp [vectorize_apply, inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite]

/-- Vectorization after recovery gives the original vector, including in dimension zero. -/
lemma vectorize_unvectorize (b : OrthonormalBasis ι ℂ H.state) (v : (K ⊗ H).state) :
    vectorize b (unvectorize b v) = v := by
  apply InnerProductSpace.ext_inner_left_basis
    ((stdOrthonormalBasis ℂ K.state).tensorProduct b).toBasis
  rintro ⟨j, i⟩
  rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply,
    inner_vectorize, unvectorize_basis, LinearMap.adjoint_inner_right]
  rfl

/-- The unnormalized Choi operator, ordered as output tensor input reference. -/
def choi (b : OrthonormalBasis ι ℂ H.state) : Superoperator H K →ₗ[ℂ] Operator (K ⊗ H) where
  toFun Φ := ∑ i, ∑ j, Operator.tensor (Φ (Operator.outer (b i) (b j)))
    (Operator.outer (b i) (b j))
  map_add' Φ Ψ := by
    simp [Operator.tensor, ← TensorProduct.mapBilinear_apply, Finset.sum_add_distrib]
  map_smul' c Φ := by
    simp [Operator.tensor, ← TensorProduct.mapBilinear_apply, Finset.smul_sum]

/-- The matrix-unit expansion of the Choi operator. -/
lemma choi_apply (b : OrthonormalBasis ι ℂ H.state) (Φ : Superoperator H K) :
    choi b Φ = ∑ i, ∑ j, Operator.tensor (Φ (Operator.outer (b i) (b j)))
      (Operator.outer (b i) (b j)) := rfl

/-- Choi coefficients are the coefficients of the images of basis matrix units. -/
lemma inner_choi (b : OrthonormalBasis ι ℂ H.state) (Φ : Superoperator H K)
    (x y : K.state) (i j : ι) :
    inner ℂ (x ⊗ₜ[ℂ] b i) (choi b Φ (y ⊗ₜ[ℂ] b j)) =
      inner ℂ x (Φ (Operator.outer (b i) (b j)) y) := by
  classical
  simp [choi_apply, LinearMap.sum_apply, Operator.tensor_apply, Operator.outer_apply,
    inner_sum, TensorProduct.inner_tmul, b.inner_eq_ite, apply_ite]

/-- The Choi operator determines the superoperator on all inputs. -/
lemma choi_injective (b : OrthonormalBasis ι ℂ H.state) :
    Function.Injective (choi (K := K) b) := by
  intro Φ Ψ h
  apply Operator.basis_outer_ext b
  intro i j
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [← inner_choi b Φ x y i j, ← inner_choi b Ψ x y i j, h]

/-- Choi is amplification applied to the unnormalized maximally entangled projector. -/
lemma choi_eq_tensor_apply (b : OrthonormalBasis ι ℂ H.state) (Φ : Superoperator H K) :
    choi b Φ = tensor Φ (LinearMap.id : Superoperator H H)
      (Operator.outer (∑ i, b i ⊗ₜ[ℂ] b i) (∑ i, b i ⊗ₜ[ℂ] b i)) := by
  rw [Operator.outer_sum_left]
  simp only [Operator.outer_sum_right, ← Operator.tensor_outer,
    map_sum, tensor_apply, LinearMap.id_apply, choi_apply]

/-- Complete positivity implies positivity of the Choi operator in every input basis. -/
lemma IsCompletelyPositive.choi_positive {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) (b : OrthonormalBasis ι ℂ H.state) :
    (choi b Φ).IsPositive := by
  rw [choi_eq_tensor_apply]
  exact hΦ H _ (Operator.isPositive_outer _)

/-- The Choi operator of a pure process is the outer square of its vectorization. -/
lemma choi_conjugate (b : OrthonormalBasis ι ℂ H.state) (f : H.state →ₗ[ℂ] K.state) :
    choi b (conjugate f) = Operator.outer (vectorize b f) (vectorize b f) := by
  rw [vectorize_apply, Operator.outer_sum_left]
  simp only [choi_apply, conjugate_outer, Operator.tensor_outer]
  exact Finset.sum_congr rfl fun i _ => (Operator.outer_sum_right _ _).symm

/-- A positive Choi operator yields a finite Kraus representation. -/
lemma exists_kraus_of_choi_positive (b : OrthonormalBasis ι ℂ H.state)
    (Φ : Superoperator H K) (hΦ : (choi b Φ).IsPositive) :
    ∃ f : Fin (Module.finrank ℂ (K ⊗ H).state) → H.state →ₗ[ℂ] K.state, Φ = kraus f := by
  obtain ⟨v, hv⟩ := Operator.exists_sum_outer_of_isPositive (choi b Φ) hΦ
  refine ⟨fun i => unvectorize b (v i), choi_injective b ?_⟩
  rw [kraus, map_sum]
  simp only [choi_conjugate, vectorize_unvectorize]
  exact hv

/-- Choi's criterion, with an arbitrary explicit input orthonormal basis. -/
theorem isCompletelyPositive_iff_choi_positive (b : OrthonormalBasis ι ℂ H.state)
    (Φ : Superoperator H K) : Φ.IsCompletelyPositive ↔ (choi b Φ).IsPositive := by
  refine ⟨fun h => h.choi_positive b, fun h => ?_⟩
  obtain ⟨f, rfl⟩ := exists_kraus_of_choi_positive b Φ h
  exact isCompletelyPositive_kraus f

/-- Every completely positive map between qudits admits a finite Kraus representation. -/
lemma IsCompletelyPositive.exists_kraus {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) :
    ∃ (n : ℕ) (f : Fin n → H.state →ₗ[ℂ] K.state), Φ = kraus f := by
  obtain ⟨f, hf⟩ := exists_kraus_of_choi_positive (stdOrthonormalBasis ℂ H.state) Φ
    (hΦ.choi_positive _)
  exact ⟨Module.finrank ℂ (K ⊗ H).state, f, hf⟩

/-- A Kraus representation needs at most output dimension times input dimension;
zero operators pad the spectral family to this fixed size. -/
lemma IsCompletelyPositive.exists_kraus_finrank {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) :
    ∃ f : Fin (Module.finrank ℂ K.state * Module.finrank ℂ H.state) →
        H.state →ₗ[ℂ] K.state, Φ = kraus f := by
  have hd : Module.finrank ℂ (K ⊗ H).state =
      Module.finrank ℂ K.state * Module.finrank ℂ H.state :=
    Module.finrank_tensorProduct
  rw [← hd]
  exact exists_kraus_of_choi_positive (stdOrthonormalBasis ℂ H.state) Φ (hΦ.choi_positive _)

/-- The input marginal of Choi records the trace of each image matrix unit. -/
lemma inner_partialTraceLeft_choi (b : OrthonormalBasis ι ℂ H.state)
    (Φ : Superoperator H K) (i j : ι) :
    inner ℂ (b i) (Operator.partialTraceLeft (choi b Φ) (b j)) =
      (Φ (Operator.outer (b i) (b j))).trace := by
  rw [Operator.inner_partialTraceLeft (stdOrthonormalBasis ℂ K.state)]
  simp only [inner_choi b Φ]
  exact (LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ K.state)).symm

/-- Trace preservation is exactly the identity input marginal of the unnormalized Choi operator. -/
theorem isTracePreserving_iff_partialTraceLeft_choi (b : OrthonormalBasis ι ℂ H.state)
    (Φ : Superoperator H K) :
    Φ.IsTracePreserving ↔ Operator.partialTraceLeft (choi b Φ) = (1 : Operator H) := by
  classical
  constructor
  · intro hΦ
    apply b.toBasis.ext
    intro j
    apply InnerProductSpace.ext_inner_left_basis b.toBasis
    intro i
    simp only [OrthonormalBasis.coe_toBasis, inner_partialTraceLeft_choi,
      one_apply_eq_self]
    rw [hΦ (Operator.outer (b i) (b j)), Operator.trace_outer]
    simp [b.inner_eq_ite, eq_comm]
  · intro h
    have ht : LinearMap.trace ℂ K.state ∘ₗ Φ = LinearMap.trace ℂ H.state := by
      apply Operator.basis_outer_ext b
      intro i j
      change (Φ (Operator.outer (b i) (b j))).trace = (Operator.outer (b i) (b j)).trace
      rw [← inner_partialTraceLeft_choi b Φ i j, h, one_apply_eq_self, Operator.trace_outer]
      simp [b.inner_eq_ite, eq_comm]
    intro A
    exact congrArg (fun f => f A) ht

/-- Finite Kraus representations characterize the original amplification definition of CP. -/
theorem isCompletelyPositive_iff_exists_kraus (Φ : Superoperator H K) :
    Φ.IsCompletelyPositive ↔
      ∃ (n : ℕ) (f : Fin n → H.state →ₗ[ℂ] K.state), Φ = kraus f := by
  refine ⟨fun h => h.exists_kraus, ?_⟩
  rintro ⟨n, f, rfl⟩
  exact isCompletelyPositive_kraus f

/-- Choi positivity is independent of the chosen input basis and its index type. -/
lemma choi_positive_iff {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ H.state)
    (Φ : Superoperator H K) : (choi b Φ).IsPositive ↔ (choi c Φ).IsPositive := by
  rw [← isCompletelyPositive_iff_choi_positive, ← isCompletelyPositive_iff_choi_positive]

/-- The usual Choi matrix entries in arbitrary output coordinates. -/
lemma toMatrix_choi {κ : Type*} [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ K.state)
    (Φ : Superoperator H K) (a d : κ) (i j : ι) :
    LinearMap.toMatrixOrthonormal (c.tensorProduct b) (choi b Φ) (a, i) (d, j) =
      LinearMap.toMatrixOrthonormal c (Φ (Operator.outer (b i) (b j))) a d := by
  simp only [LinearMap.toMatrixOrthonormal_apply_apply, OrthonormalBasis.tensorProduct_apply]
  exact inner_choi b Φ (c a) (c d) i j

/-- Positivity of the ordinary Choi matrix is equivalent to complete positivity. -/
lemma isCompletelyPositive_iff_choi_matrix_posSemidef {κ : Type*} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : OrthonormalBasis ι ℂ H.state)
    (c : OrthonormalBasis κ ℂ K.state) (Φ : Superoperator H K) :
    Φ.IsCompletelyPositive ↔
      (LinearMap.toMatrixOrthonormal (c.tensorProduct b) (choi b Φ)).PosSemidef := by
  exact (isCompletelyPositive_iff_choi_positive b Φ).trans
    (Operator.posSemidef_toMatrix_iff (H := K ⊗ H) (c.tensorProduct b) (choi b Φ)).symm

end Superoperator

namespace QuantumChannel

variable {H K : Qudit}

/-- A channel has a normalized Kraus family of output dimension times input dimension. -/
lemma exists_kraus_finrank (Φ : QuantumChannel H K) :
    ∃ f : Fin (Module.finrank ℂ K.state * Module.finrank ℂ H.state) →
        H.state →ₗ[ℂ] K.state,
      Φ.toSuperoperator = Superoperator.kraus f ∧ ∑ i, (f i).adjoint ∘ₗ f i = 1 := by
  obtain ⟨f, hf⟩ := Φ.completelyPositive.exists_kraus_finrank
  exact ⟨f, hf, (Superoperator.isTracePreserving_kraus_iff f).mp (hf ▸ Φ.tracePreserving)⟩

/-- Every channel admits a finite normalized Kraus representation, without dimension assumptions. -/
lemma exists_kraus (Φ : QuantumChannel H K) :
    ∃ (n : ℕ) (f : Fin n → H.state →ₗ[ℂ] K.state),
      Φ.toSuperoperator = Superoperator.kraus f ∧ ∑ i, (f i).adjoint ∘ₗ f i = 1 := by
  obtain ⟨n, f, hf⟩ := Φ.completelyPositive.exists_kraus
  exact ⟨n, f, hf, (Superoperator.isTracePreserving_kraus_iff f).mp (hf ▸ Φ.tracePreserving)⟩

end QuantumChannel

end

end Qudit
