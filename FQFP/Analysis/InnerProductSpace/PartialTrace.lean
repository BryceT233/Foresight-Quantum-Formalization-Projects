/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Partial traces of finite-dimensional Hilbert space operators

`LinearMap.partialTraceRight` discards the right tensor factor. It is implemented as a
sum of compressions in an orthonormal basis. Its matrix coefficients are themselves
basis-independent traces, proving that every orthonormal basis gives the same map.
The left partial trace discards the left factor by first exchanging the factors.

## Main definitions and results

* `LinearMap.partialTraceRight` traces out the right tensor factor.
* `LinearMap.partialTraceLeft` traces out the left tensor factor.
* `LinearMap.partialTraceRightWith_eq` shows that the right partial trace is independent of the
  chosen orthonormal basis.
-/

@[expose] public section

open scoped TensorProduct InnerProductSpace ComplexOrder

namespace LinearMap

noncomputable section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A positive operator is a finite sum of positive rank-one operators. -/
lemma isPositive_iff_eq_sum_rankOne {A : E →ₗ[𝕜] E} :
    A.IsPositive ↔ ∃ (n : ℕ) (v : Fin n → E),
      A = ∑ i, (InnerProductSpace.rankOne 𝕜 (v i) (v i)).toLinearMap := by
  rw [← isPositive_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPositive_iff_eq_sum_rankOne]
  constructor
  · rintro ⟨n, v, h⟩
    exact ⟨n, v, by simpa using congrArg ContinuousLinearMap.toLinearMap h⟩
  · rintro ⟨n, v, h⟩
    refine ⟨n, v, ?_⟩
    ext x
    simpa using congrArg (fun f : E →ₗ[𝕜] E => f x) h

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Tensor products of rank-one operators are rank-one operators on pure tensors. -/
lemma map_rankOne (x y : E) (u v : F) :
    TensorProduct.map (InnerProductSpace.rankOne 𝕜 x y).toLinearMap
      (InnerProductSpace.rankOne 𝕜 u v).toLinearMap =
      (InnerProductSpace.rankOne 𝕜 (x ⊗ₜ u) (y ⊗ₜ v)).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, TensorProduct.inner_tmul]
  exact TensorProduct.smul_tmul_smul _ _ _ _

/-- Positivity is preserved by tensor products, including singular operators. -/
lemma IsPositive.tensorProduct {A : E →ₗ[𝕜] E} {B : F →ₗ[𝕜] F}
    (hA : A.IsPositive) (hB : B.IsPositive) : (TensorProduct.map A B).IsPositive := by
  obtain ⟨n, v, rfl⟩ := isPositive_iff_eq_sum_rankOne.mp hA
  obtain ⟨m, w, rfl⟩ := isPositive_iff_eq_sum_rankOne.mp hB
  simp only [← TensorProduct.mapBilinear_apply, map_sum, LinearMap.sum_apply]
  simp only [TensorProduct.mapBilinear_apply, map_rankOne]
  exact isPositive_sum _ fun i _ => isPositive_sum _ fun j _ =>
    (InnerProductSpace.isPositive_rankOne_self (v j ⊗ₜ w i)).toLinearMap

/-- Right partial trace computed using an explicit orthonormal basis of the discarded space. -/
def partialTraceRightWith {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 F) :
    Module.End 𝕜 (E ⊗[𝕜] F) →ₗ[𝕜] Module.End 𝕜 E where
  toFun A := ∑ i, ((TensorProduct.mk 𝕜 E F).flip (b i)).adjoint ∘ₗ A ∘ₗ
    (TensorProduct.mk 𝕜 E F).flip (b i)
  map_add' A B := by simp [comp_add, add_comp, Finset.sum_add_distrib]
  map_smul' c A := by simp [comp_smul, smul_comp, Finset.smul_sum]

/-- Matrix coefficients of a partial trace are sums of matrix coefficients of the input. -/
lemma inner_partialTraceRightWith {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 F) (A : Module.End 𝕜 (E ⊗[𝕜] F)) (x y : E) :
    ⟪x, partialTraceRightWith b A y⟫_𝕜 =
      ∑ i, ⟪x ⊗ₜ b i, A (y ⊗ₜ b i)⟫_𝕜 := by
  simp [partialTraceRightWith, sum_apply, inner_sum, adjoint_inner_right]

/-- Each coefficient is a trace on the discarded factor, hence does not depend on a basis. -/
lemma inner_partialTraceRightWith_eq_trace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 F) (A : Module.End 𝕜 (E ⊗[𝕜] F)) (x y : E) :
    ⟪x, partialTraceRightWith b A y⟫_𝕜 = trace 𝕜 F
      ((TensorProduct.mk 𝕜 E F x).adjoint ∘ₗ A ∘ₗ TensorProduct.mk 𝕜 E F y) := by
  rw [inner_partialTraceRightWith, trace_eq_sum_inner _ b]
  simp only [comp_apply, adjoint_inner_right, TensorProduct.mk_apply]

/-- Computing the right partial trace with any two orthonormal bases gives the same map. -/
lemma partialTraceRightWith_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι 𝕜 F) (c : OrthonormalBasis κ 𝕜 F) :
    partialTraceRightWith (E := E) b = partialTraceRightWith c := by
  ext A y
  apply ext_inner_left 𝕜
  intro x
  rw [inner_partialTraceRightWith_eq_trace, inner_partialTraceRightWith_eq_trace]

/-- Discard the right tensor factor of an operator. -/
def partialTraceRight : Module.End 𝕜 (E ⊗[𝕜] F) →ₗ[𝕜] Module.End 𝕜 E :=
  partialTraceRightWith (stdOrthonormalBasis 𝕜 F)

/-- The basis-independent right partial trace can be computed in any orthonormal basis. -/
lemma partialTraceRight_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 F) :
    partialTraceRight (𝕜 := 𝕜) (E := E) = partialTraceRightWith b :=
  partialTraceRightWith_eq _ b

/-- Right partial trace preserves positivity. -/
lemma IsPositive.partialTraceRight {A : Module.End 𝕜 (E ⊗[𝕜] F)} (hA : A.IsPositive) :
    (partialTraceRight A).IsPositive :=
  isPositive_sum _ fun _ _ => hA.adjoint_conj _

/-- Right partial trace preserves the total trace, without any dimension restriction. -/
lemma trace_partialTraceRight (A : Module.End 𝕜 (E ⊗[𝕜] F)) :
    trace 𝕜 E (partialTraceRight A) = trace 𝕜 (E ⊗[𝕜] F) A := by
  let b := stdOrthonormalBasis 𝕜 E
  let c := stdOrthonormalBasis 𝕜 F
  rw [partialTraceRight_eq c, trace_eq_sum_inner _ b,
    trace_eq_sum_inner _ (b.tensorProduct c)]
  simp only [inner_partialTraceRightWith, Fintype.sum_prod_type,
    OrthonormalBasis.tensorProduct_apply]

/-- The right partial trace of a product operator is the trace of its right factor times
its left factor. -/
lemma partialTraceRight_map (A : Module.End 𝕜 E) (B : Module.End 𝕜 F) :
    partialTraceRight (TensorProduct.map A B) = trace 𝕜 F B • A := by
  ext y
  apply ext_inner_left 𝕜
  intro x
  rw [partialTraceRight, inner_partialTraceRightWith,
    trace_eq_sum_inner B (stdOrthonormalBasis 𝕜 F)]
  simp [TensorProduct.inner_tmul, inner_smul_right, Finset.mul_sum, mul_comm]

/-- Right partial trace preserves the statistics of observables on the retained factor. -/
lemma trace_mul_partialTraceRight (A : Module.End 𝕜 (E ⊗[𝕜] F)) (B : Module.End 𝕜 E) :
    trace 𝕜 E (B * partialTraceRight A) =
      trace 𝕜 (E ⊗[𝕜] F) (TensorProduct.map B LinearMap.id * A) := by
  let b := stdOrthonormalBasis 𝕜 E
  let c := stdOrthonormalBasis 𝕜 F
  rw [trace_eq_sum_inner _ b, trace_eq_sum_inner _ (b.tensorProduct c)]
  simp only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply,
    Module.End.mul_apply, ← adjoint_inner_left B,
    ← adjoint_inner_left (TensorProduct.map B (LinearMap.id : F →ₗ[𝕜] F)),
    TensorProduct.adjoint_map, adjoint_id,
    TensorProduct.map_tmul, id_apply]
  simp only [partialTraceRight_eq c, inner_partialTraceRightWith]

/-- Discard the left tensor factor of an operator. -/
def partialTraceLeft : Module.End 𝕜 (E ⊗[𝕜] F) →ₗ[𝕜] Module.End 𝕜 F :=
  partialTraceRight ∘ₗ (TensorProduct.comm 𝕜 E F).conj.toLinearMap

/-- Exchanging the tensor factors carries positive operators to positive operators. -/
lemma IsPositive.comm_conj {A : Module.End 𝕜 (E ⊗[𝕜] F)} (hA : A.IsPositive) :
    ((TensorProduct.comm 𝕜 E F).conj A).IsPositive := by
  have h := hA.conj_adjoint (TensorProduct.commIsometry 𝕜 E F).toLinearMap
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm] at h
  exact h

/-- Left partial trace preserves positivity. -/
lemma IsPositive.partialTraceLeft {A : Module.End 𝕜 (E ⊗[𝕜] F)} (hA : A.IsPositive) :
    (partialTraceLeft A).IsPositive := hA.comm_conj.partialTraceRight

/-- Left partial trace preserves the total trace. -/
lemma trace_partialTraceLeft (A : Module.End 𝕜 (E ⊗[𝕜] F)) :
    trace 𝕜 F (partialTraceLeft A) = trace 𝕜 (E ⊗[𝕜] F) A := by
  rw [partialTraceLeft, comp_apply, LinearEquiv.coe_coe, trace_partialTraceRight,
    trace_conj']

/-- Left partial trace can be computed in any orthonormal basis of the discarded factor. -/
lemma inner_partialTraceLeft {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E)
    (A : Module.End 𝕜 (E ⊗[𝕜] F)) (x y : F) :
    ⟪x, partialTraceLeft A y⟫_𝕜 = ∑ i, ⟪b i ⊗ₜ x, A (b i ⊗ₜ y)⟫_𝕜 := by
  rw [partialTraceLeft, comp_apply, partialTraceRight_eq b, inner_partialTraceRightWith]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearEquiv.coe_coe, LinearEquiv.conj_apply_apply]
  simpa using (TensorProduct.inner_comm_comm
    (b i ⊗ₜ[𝕜] x) (A (b i ⊗ₜ y)))

/-- The left partial trace of a product operator is the trace of its left factor times
its right factor. -/
lemma partialTraceLeft_map (A : Module.End 𝕜 E) (B : Module.End 𝕜 F) :
    partialTraceLeft (TensorProduct.map A B) = trace 𝕜 E A • B := by
  have h : (TensorProduct.comm 𝕜 E F).conj (TensorProduct.map A B) =
      TensorProduct.map B A := by
    apply TensorProduct.ext'
    intro x y
    simp [LinearEquiv.conj_apply_apply]
  change partialTraceRight ((TensorProduct.comm 𝕜 E F).conj _) = _
  rw [h, partialTraceRight_map]

/-- Left partial trace preserves the statistics of observables on the retained factor. -/
lemma trace_mul_partialTraceLeft (A : Module.End 𝕜 (E ⊗[𝕜] F)) (B : Module.End 𝕜 F) :
    trace 𝕜 F (B * partialTraceLeft A) =
      trace 𝕜 (E ⊗[𝕜] F) (TensorProduct.map LinearMap.id B * A) := by
  let b := stdOrthonormalBasis 𝕜 E
  let c := stdOrthonormalBasis 𝕜 F
  rw [trace_eq_sum_inner _ c, trace_eq_sum_inner _ (b.tensorProduct c)]
  simp only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply,
    Module.End.mul_apply, ← adjoint_inner_left B,
    ← adjoint_inner_left (TensorProduct.map (LinearMap.id : E →ₗ[𝕜] E) B),
    TensorProduct.adjoint_map, adjoint_id, TensorProduct.map_tmul, id_apply,
    inner_partialTraceLeft b]
  exact Finset.sum_comm

end

end LinearMap
