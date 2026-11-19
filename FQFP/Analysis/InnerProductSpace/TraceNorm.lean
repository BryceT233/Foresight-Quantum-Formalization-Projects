/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.InnerProductSpace.PositiveTrace

/-!
# The finite-dimensional trace norm

The trace norm is the dual of the Hilbert-space operator norm under the trace pairing
(Watrous, *The Theory of Quantum Information*, equation (1.173), with `p = 1`).
This avoids imposing a second norm instance on linear endomorphisms. All operator
norms below are those of continuous linear maps on the given inner product space.

## Main definitions and results

* `LinearMap.traceNorm` defines the trace norm as the dual norm of the trace pairing.
* `LinearMap.sum_abs_re_inner_le_traceNorm` bounds the sum of absolute real diagonal entries in an
  orthonormal basis by the trace norm.
* `LinearMap.IsSymmetric.traceNorm_eq_sum_abs_eigenvalues` computes the trace norm of a self-adjoint
  operator from its eigenvalues.
* `LinearMap.IsSymmetric.traceNorm_map_le` bounds the trace norm after a positive trace-preserving
  map acts on a self-adjoint operator.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

namespace LinearMap

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Trace pairing with an operator, as a continuous functional on the operator-norm space. -/
def traceFunctional (A : E →ₗ[ℂ] E) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => trace ℂ E (B.toLinearMap * A)
      map_add' := fun B C => by simp [add_mul]
      map_smul' := fun c B => by simp }

/-- The trace norm, in its operator-norm dual characterization. -/
def traceNorm (A : E →ₗ[ℂ] E) : ℝ := ‖traceFunctional A‖

/-- Evaluation of the trace functional. -/
lemma traceFunctional_apply (A : E →ₗ[ℂ] E) (B : E →L[ℂ] E) :
    traceFunctional A B = trace ℂ E (B.toLinearMap * A) := rfl

/-- The trace functional is additive in its parameter. -/
lemma traceFunctional_add (A B : E →ₗ[ℂ] E) :
    traceFunctional (A + B) = traceFunctional A + traceFunctional B := by
  ext C
  simp [traceFunctional_apply, mul_add]

/-- The trace functional is homogeneous in its parameter. -/
lemma traceFunctional_smul (c : ℂ) (A : E →ₗ[ℂ] E) :
    traceFunctional (c • A) = c • traceFunctional A := by
  ext B
  simp [traceFunctional_apply]

/-- Trace norms are nonnegative. -/
lemma traceNorm_nonneg (A : E →ₗ[ℂ] E) : 0 ≤ traceNorm A :=
  norm_nonneg (traceFunctional A)

/-- The zero operator has trace norm zero. -/
lemma traceNorm_zero : traceNorm (0 : E →ₗ[ℂ] E) = 0 := by
  have h : traceFunctional (0 : E →ₗ[ℂ] E) = 0 := by
    ext B
    simp [traceFunctional_apply]
  rw [traceNorm, h]
  exact ContinuousLinearMap.opNorm_zero

/-- The triangle inequality for the trace norm. -/
lemma traceNorm_add_le (A B : E →ₗ[ℂ] E) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  simpa only [traceNorm, traceFunctional_add] using norm_add_le (traceFunctional A)
    (traceFunctional B)

/-- The trace norm of a finite sum is at most the sum of the trace norms. -/
lemma traceNorm_sum_le {ι : Type*} (s : Finset ι) (A : ι → E →ₗ[ℂ] E) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Absolute homogeneity of the trace norm. -/
lemma traceNorm_smul (c : ℂ) (A : E →ₗ[ℂ] E) :
    traceNorm (c • A) = ‖c‖ * traceNorm A := by
  let : NormedAddCommGroup ((E →L[ℂ] E) →L[ℂ] ℂ) := inferInstance
  let : NormedSpace ℂ ((E →L[ℂ] E) →L[ℂ] ℂ) := inferInstance
  rw [traceNorm, traceFunctional_smul]
  exact norm_smul c (traceFunctional A)

/-- Negation preserves the trace norm. -/
lemma traceNorm_neg (A : E →ₗ[ℂ] E) : traceNorm (-A) = traceNorm A := by
  simpa using traceNorm_smul (-1) A

/-- The trace pairing is bounded by the operator norm times the trace norm. -/
lemma norm_trace_mul_le (A B : E →ₗ[ℂ] E) :
    ‖trace ℂ E (B * A)‖ ≤ ‖B.toContinuousLinearMap‖ * traceNorm A := by
  simpa only [traceNorm, traceFunctional_apply, coe_toContinuousLinearMap, mul_comm] using
    (traceFunctional A).le_opNorm B.toContinuousLinearMap

/-- A pointwise bound on trace pairings bounds the trace norm. -/
lemma traceNorm_le {A : E →ₗ[ℂ] E} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ B : E →L[ℂ] E, ‖trace ℂ E (B.toLinearMap * A)‖ ≤ r * ‖B‖) :
    traceNorm A ≤ r := (traceFunctional A).opNorm_le_bound hr h

/-- The modulus of the trace is at most the trace norm, including on the zero space. -/
lemma norm_trace_le_traceNorm (A : E →ₗ[ℂ] E) : ‖trace ℂ E A‖ ≤ traceNorm A := by
  have h := (traceFunctional A).le_opNorm (ContinuousLinearMap.id ℂ E)
  simp only [traceFunctional_apply, ContinuousLinearMap.coe_id] at h
  exact h.trans (mul_le_of_le_one_right (traceNorm_nonneg A) ContinuousLinearMap.norm_id_le)

/-- Multiplication on the left costs at most the Hilbert-space operator norm. -/
lemma traceNorm_mul_le_opNorm (A B : E →ₗ[ℂ] E) :
    traceNorm (A * B) ≤ ‖A.toContinuousLinearMap‖ * traceNorm B := by
  apply traceNorm_le (mul_nonneg (norm_nonneg _) (traceNorm_nonneg _))
  intro C
  calc
    ‖trace ℂ E (C.toLinearMap * (A * B))‖ =
        ‖trace ℂ E ((C.toLinearMap * A) * B)‖ := by rw [mul_assoc]
    _ ≤ ‖(C.toLinearMap * A).toContinuousLinearMap‖ * traceNorm B :=
      norm_trace_mul_le B _
    _ ≤ (‖C‖ * ‖A.toContinuousLinearMap‖) * traceNorm B := by
      apply mul_le_mul_of_nonneg_right _ (traceNorm_nonneg B)
      exact ContinuousLinearMap.opNorm_comp_le C A.toContinuousLinearMap
    _ = _ := by ring

/-- Multiplication on the right costs at most the Hilbert-space operator norm. -/
lemma traceNorm_mul_le_traceNorm (A B : E →ₗ[ℂ] E) :
    traceNorm (A * B) ≤ traceNorm A * ‖B.toContinuousLinearMap‖ := by
  apply traceNorm_le (mul_nonneg (traceNorm_nonneg _) (norm_nonneg _))
  intro C
  calc
    ‖trace ℂ E (C.toLinearMap * (A * B))‖ =
        ‖trace ℂ E ((B * C.toLinearMap) * A)‖ := by
      rw [← mul_assoc, trace_mul_comm ℂ _ B, mul_assoc]
    _ ≤ ‖(B * C.toLinearMap).toContinuousLinearMap‖ * traceNorm A :=
      norm_trace_mul_le A _
    _ ≤ (‖B.toContinuousLinearMap‖ * ‖C‖) * traceNorm A := by
      apply mul_le_mul_of_nonneg_right _ (traceNorm_nonneg A)
      exact ContinuousLinearMap.opNorm_comp_le B.toContinuousLinearMap C
    _ = _ := by ring

/-- Taking adjoints preserves the Hilbert-space operator norm. -/
lemma opNorm_adjoint (A : E →ₗ[ℂ] E) :
    ‖A.adjoint.toContinuousLinearMap‖ = ‖A.toContinuousLinearMap‖ := by
  have := FiniteDimensional.complete ℂ E
  rw [adjoint_toContinuousLinearMap]
  exact norm_star A.toContinuousLinearMap

/-- Conjugation by nearby contractions has trace-norm error at most twice their distance. -/
lemma traceNorm_conjugate_sub_le (A U V : E →ₗ[ℂ] E)
    (hU : ‖U.toContinuousLinearMap‖ ≤ 1) (hV : ‖V.toContinuousLinearMap‖ ≤ 1) :
    traceNorm (U * A * U.adjoint - V * A * V.adjoint) ≤
      2 * ‖(U - V).toContinuousLinearMap‖ * traceNorm A := by
  have hsplit : U * A * U.adjoint - V * A * V.adjoint =
      (U - V) * A * U.adjoint + V * (A * (U - V).adjoint) := by
    rw [map_sub]
    noncomm_ring
  have hleft : traceNorm ((U - V) * A * U.adjoint) ≤
      ‖(U - V).toContinuousLinearMap‖ * traceNorm A := calc
    _ ≤ traceNorm ((U - V) * A) * ‖U.adjoint.toContinuousLinearMap‖ :=
      traceNorm_mul_le_traceNorm _ _
    _ ≤ traceNorm ((U - V) * A) :=
      mul_le_of_le_one_right (traceNorm_nonneg _) (by rwa [opNorm_adjoint])
    _ ≤ _ := traceNorm_mul_le_opNorm _ _
  have hright : traceNorm (V * (A * (U - V).adjoint)) ≤
      ‖(U - V).toContinuousLinearMap‖ * traceNorm A := calc
    _ ≤ ‖V.toContinuousLinearMap‖ * traceNorm (A * (U - V).adjoint) :=
      traceNorm_mul_le_opNorm _ _
    _ ≤ traceNorm (A * (U - V).adjoint) :=
      mul_le_of_le_one_left (traceNorm_nonneg _) hV
    _ ≤ traceNorm A * ‖(U - V).adjoint.toContinuousLinearMap‖ :=
      traceNorm_mul_le_traceNorm _ _
    _ = _ := by rw [opNorm_adjoint, mul_comm]
  rw [hsplit]
  exact (traceNorm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

/-- A trace norm vanishes only at the zero operator. -/
lemma traceNorm_eq_zero_iff (A : E →ₗ[ℂ] E) : traceNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    let : NormedAddCommGroup ((E →L[ℂ] E) →L[ℂ] ℂ) := inferInstance
    have hf : traceFunctional A = 0 := (norm_eq_zero (a := traceFunctional A)).mp h
    ext x
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hx := congrArg (fun f => f (InnerProductSpace.rankOne ℂ x (A x))) hf
    rw [traceFunctional_apply, trace_mul_comm] at hx
    have hr : A * (InnerProductSpace.rankOne ℂ x (A x)).toLinearMap =
        (InnerProductSpace.rankOne ℂ (A x) (A x)).toLinearMap := by
      ext y
      simp [InnerProductSpace.rankOne_apply, Module.End.mul_apply]
    rw [hr, InnerProductSpace.trace_rankOne] at hx
    exact hx
  · rintro rfl
    exact traceNorm_zero

/-- The trace norm of a self-adjoint operator is bounded by the sum of absolute eigenvalues. -/
lemma IsSymmetric.traceNorm_le_sum_abs_eigenvalues {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    traceNorm A ≤ ∑ i, |hA.eigenvalues rfl i| := by
  classical
  apply traceNorm_le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  intro B
  rw [trace_eq_sum_inner _ (hA.eigenvectorBasis rfl), Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Module.End.mul_apply, hA.apply_eigenvectorBasis, map_smul, inner_smul_right,
    norm_mul, RCLike.norm_ofReal]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    ‖inner ℂ (hA.eigenvectorBasis rfl i) (B (hA.eigenvectorBasis rfl i))‖ ≤
        ‖hA.eigenvectorBasis rfl i‖ * ‖B (hA.eigenvectorBasis rfl i)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖hA.eigenvectorBasis rfl i‖ * (‖B‖ * ‖hA.eigenvectorBasis rfl i‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ = ‖B‖ := by simp

/-- An operator diagonal in an orthonormal basis with contractive entries is a contraction. -/
lemma opNorm_le_one_of_diagonal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (A : E →ₗ[ℂ] E) (c : ι → ℂ)
    (hA : ∀ i, A (b i) = c i • b i) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖A.toContinuousLinearMap‖ ≤ 1 := by
  classical
  have hcoord (x : E) (i : ι) : inner ℂ (b i) (A x) = c i * inner ℂ (b i) x := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hA, inner_sum, inner_smul_right, b.inner_eq_ite]
    simp [mul_ite, ← b.repr_apply_apply, mul_comm]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul, coe_toContinuousLinearMap']
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← b.sum_sq_norm_inner_right (A x), ← b.sum_sq_norm_inner_right x]
  apply Finset.sum_le_sum
  intro i _
  rw [hcoord, norm_mul]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_of_le_one_left (norm_nonneg _) (hc i)) 2

/-- The sum of absolute real diagonal entries in any orthonormal basis is bounded
by the trace norm, without any self-adjointness assumption. -/
lemma sum_abs_re_inner_le_traceNorm {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (A : E →ₗ[ℂ] E) :
    ∑ i, |(inner ℂ (b i) (A (b i))).re| ≤ traceNorm A := by
  classical
  let c : ι → ℂ := fun i ↦ if 0 ≤ (inner ℂ (b i) (A (b i))).re then 1 else -1
  let S := b.toBasis.constr ℂ (fun i ↦ c i • b i)
  have hS (i) : S (b i) = c i • b i := b.toBasis.constr_basis ℂ _ i
  have hn : ‖S.toContinuousLinearMap‖ ≤ 1 :=
    opNorm_le_one_of_diagonal b S c hS (fun i ↦ by
      dsimp [c]
      split <;> simp)
  have ht : (trace ℂ E (A * S)).re = ∑ i, |(inner ℂ (b i) (A (b i))).re| := by
    rw [trace_eq_sum_inner _ b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, hS, map_smul, inner_smul_right]
    dsimp only [c]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  rw [← ht, trace_mul_comm ℂ A S]
  exact (Complex.re_le_norm _).trans
    ((norm_trace_mul_le A S).trans (mul_le_of_le_one_left (traceNorm_nonneg A) hn))

/-- On self-adjoint operators the dual trace norm is the sum of absolute eigenvalues. -/
lemma IsSymmetric.traceNorm_eq_sum_abs_eigenvalues {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    traceNorm A = ∑ i, |hA.eigenvalues rfl i| := by
  apply le_antisymm hA.traceNorm_le_sum_abs_eigenvalues
  simpa only [hA.apply_eigenvectorBasis, inner_smul_right, OrthonormalBasis.inner_eq_one,
    mul_one, Complex.coe_algebraMap, Complex.ofReal_re] using
    sum_abs_re_inner_le_traceNorm (hA.eigenvectorBasis rfl) A

/-- On positive operators the trace norm is the real trace. -/
lemma IsPositive.traceNorm_eq_re_trace {A : E →ₗ[ℂ] E} (hA : A.IsPositive) :
    traceNorm A = (trace ℂ E A).re := by
  rw [hA.isSymmetric.traceNorm_eq_sum_abs_eigenvalues]
  change _ = RCLike.re (trace ℂ E A)
  rw [hA.isSymmetric.re_trace_eq_sum_eigenvalues rfl]
  exact Finset.sum_congr rfl fun i _ ↦ abs_of_nonneg (hA.nonneg_eigenvalues rfl i)

/-- Spectral decomposition of a self-adjoint operator into rank-one orthogonal projections. -/
lemma IsSymmetric.eq_sum_smul_rankOne {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) :
    A = ∑ i, (hA.eigenvalues rfl i : ℂ) •
      (InnerProductSpace.rankOne ℂ (hA.eigenvectorBasis rfl i)
        (hA.eigenvectorBasis rfl i)).toLinearMap := by
  classical
  let b := hA.eigenvectorBasis rfl
  apply b.toBasis.ext
  intro j
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply]
  simp [b, (hA.eigenvectorBasis rfl).inner_eq_ite, smul_ite]

/-- Positive trace-preserving linear maps contract the trace norm of self-adjoint inputs.
Complete positivity is not needed for this unextended inequality. -/
lemma IsSymmetric.traceNorm_map_le {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric)
    (Φ : (E →ₗ[ℂ] E) →ₗ[ℂ] (F →ₗ[ℂ] F))
    (hpos : ∀ B, B.IsPositive → (Φ B).IsPositive)
    (htr : ∀ B, trace ℂ F (Φ B) = trace ℂ E B) :
    traceNorm (Φ A) ≤ traceNorm A := by
  classical
  let b := hA.eigenvectorBasis rfl
  have hn (i) : traceNorm (Φ (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap) = 1 := by
    rw [(hpos _
      (InnerProductSpace.isPositive_rankOne_self (b i)).toLinearMap).traceNorm_eq_re_trace,
      htr, InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
    norm_num
  calc
    traceNorm (Φ A) = traceNorm (∑ i, (hA.eigenvalues rfl i : ℂ) •
        Φ (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap) := by
      conv_lhs => rw [hA.eq_sum_smul_rankOne]
      rw [map_sum]
      simp only [map_smul, b]
    _ ≤ ∑ i, traceNorm ((hA.eigenvalues rfl i : ℂ) •
        Φ (InnerProductSpace.rankOne ℂ (b i) (b i)).toLinearMap) := traceNorm_sum_le _ _
    _ = traceNorm A := by
      simp only [traceNorm_smul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        hA.traceNorm_eq_sum_abs_eigenvalues]

/-- Centering an operator effect produces a contraction. -/
lemma opNorm_add_self_sub_one_le {A : E →ₗ[ℂ] E} (h₀ : A.IsPositive) (h₁ : A ≤ 1) :
    ‖(A + A - 1).toContinuousLinearMap‖ ≤ 1 := by
  let b := h₀.isSymmetric.eigenvectorBasis rfl
  let c (i : Fin (Module.finrank ℂ E)) : ℂ := (2 * h₀.isSymmetric.eigenvalues rfl i - 1 : ℝ)
  have heigen (i) : A (b i) = (h₀.isSymmetric.eigenvalues rfl i : ℂ) • b i :=
    h₀.isSymmetric.apply_eigenvectorBasis rfl i
  have hupper (i) : h₀.isSymmetric.eigenvalues rfl i ≤ 1 := by
    have h := (le_def.mp h₁).inner_nonneg_right (b i)
    have hb : inner ℂ (b i) (b i) = 1 := by simp [inner_self_eq_norm_sq_to_K]
    simp only [LinearMap.sub_apply, one_apply_eq_self, inner_sub_right,
      heigen, inner_smul_right, hb, mul_one] at h
    exact_mod_cast (sub_nonneg.mp h)
  apply opNorm_le_one_of_diagonal b _ c
  · intro i
    simp only [LinearMap.add_apply, LinearMap.sub_apply, one_apply_eq_self,
      heigen]
    simp [c, sub_smul, add_smul, two_mul]
  · intro i
    rw [show c i = ((2 * h₀.isSymmetric.eigenvalues rfl i - 1 : ℝ) : ℂ) from rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h₀.nonneg_eigenvalues rfl i, hupper i]

/-- A trace-zero operator paired with an effect is bounded by half its trace norm. -/
lemma abs_re_trace_mul_le_half_traceNorm {A B : E →ₗ[ℂ] E}
    (htr : trace ℂ E A = 0) (hB₀ : B.IsPositive) (hB₁ : B ≤ 1) :
    |(trace ℂ E (B * A)).re| ≤ traceNorm A / 2 := by
  have h := norm_trace_mul_le A (B + B - 1)
  have hb := opNorm_add_self_sub_one_le hB₀ hB₁
  have hbound : ‖trace ℂ E ((B + B - 1) * A)‖ ≤ traceNorm A :=
    h.trans (mul_le_of_le_one_left (traceNorm_nonneg A) hb)
  have hr := (Complex.abs_re_le_norm (trace ℂ E ((B + B - 1) * A))).trans hbound
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, htr, sub_zero,
    Complex.add_re] at hr
  rw [← two_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hr
  linarith

end

end LinearMap
