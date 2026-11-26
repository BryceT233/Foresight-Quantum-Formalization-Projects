/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the unsquared fidelity and its trace-norm formula.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/Fidelity.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Spectral.OperatorSqrt
public import FQFP.CQM.Qudit.State.Support
public import FQFP.CQM.Qudit.State.Purification.Minimal
public import FQFP.CQM.Qudit.Channel.Choi
public import FQFP.Analysis.InnerProductSpace.Gram
public import FQFP.Analysis.InnerProductSpace.TraceNorm

/-!
# Fidelity and purification overlaps

The fidelity convention is the unsquared trace norm of the product of positive square
roots. Uhlmann's theorem identifies it with the maximum modulus of purification overlaps.
One purification may be fixed. The auxiliary space need only accommodate the rank of the
other density, so the result applies to minimal purifications and singular states.
The squared-overlap version is supplied separately to make the convention explicit.
Against a pure density, fidelity is the square root of the corresponding expectation;
the squared formula is also provided through the same `Density.expectation` interface.

The mathematical statements follow Watrous, *The Theory of Quantum Information*,
Lemma 3.21 and Theorem 3.22. The maximum is attained; no supremum or invertibility premise
replaces it. See `artifacts/cqm-category/qudit-fidelity-2026-11-13.md` for the interface audit.

## Main definitions and results

* `Qudit.Density.fidelity`: the unsquared trace norm of the product of positive square roots.
* `Qudit.Density.norm_inner_le_fidelity`: purification overlaps are bounded by fidelity.
* `Qudit.Density.exists_purification_norm_inner_eq_fidelity`: Uhlmann attainment with one vector
  fixed.
* `Qudit.Density.isGreatest_purification_overlap`: the attained maximum with the sharp auxiliary
  rank bound.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct BigOperators ComplexOrder

namespace Qudit

noncomputable section

variable {H K : Qudit}

namespace Operator

/-- A linear isometry has operator norm at most one, including on the zero space. -/
lemma opNorm_linearIsometry_le_one (V : H.state →ₗᵢ[ℂ] K.state) :
    ‖V.toLinearMap.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp

/-- Finite-dimensional polar decomposition with a unitary factor, also for singular operators. -/
lemma exists_polar_isometryEquiv (A : Operator H) :
    ∃ U : H.state ≃ₗᵢ[ℂ] H.state,
      A = U.toLinearMap * sqrt (H := H) (A.adjoint * A) := by
  let P := sqrt (H := H) (A.adjoint * A)
  have hp : P.adjoint * P = A.adjoint * A := by
    change (sqrt (H := H) (A.adjoint * A)).adjoint * sqrt (H := H) (A.adjoint * A) = _
    rw [adjoint_sqrt]
    exact sqrt_mul_sqrt (H := H) _ A.isPositive_adjoint_comp_self
  obtain ⟨V, hV⟩ := P.exists_linearIsometry_comp_eq A (by
    intro x y
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right]
    exact congrArg (inner ℂ x) (LinearMap.congr_fun hp y)) le_rfl
  exact ⟨LinearIsometryEquiv.ofSurjective V
    (LinearMap.surjective_of_injective V.injective), hV.symm⟩

/-- The trace norm is unchanged by a unitary factor on the left. -/
lemma traceNorm_isometryEquiv_mul (U : H.state ≃ₗᵢ[ℂ] H.state) (A : Operator H) :
    LinearMap.traceNorm (U.toLinearMap * A) = LinearMap.traceNorm A := by
  have hb (V : H.state ≃ₗᵢ[ℂ] H.state) (B : Operator H) :
      LinearMap.traceNorm (V.toLinearMap * B) ≤ LinearMap.traceNorm B :=
    (LinearMap.traceNorm_mul_le_opNorm _ _).trans
      (mul_le_of_le_one_left (LinearMap.traceNorm_nonneg B)
        (opNorm_linearIsometry_le_one V.toLinearIsometry))
  apply le_antisymm (hb U A)
  have h := hb U.symm (U.toLinearMap * A)
  have he : U.symm.toLinearMap * (U.toLinearMap * A) = A := by
    ext x
    exact U.symm_apply_apply _
  rwa [he] at h

/-- The dual trace norm agrees with the trace of the positive absolute value.
The modulus makes the formula independent of a real-trace coercion. -/
lemma traceNorm_eq_norm_trace_sqrt_adjoint_mul (A : Operator H) :
    LinearMap.traceNorm A = ‖trace (sqrt (H := H) (A.adjoint * A))‖ := by
  obtain ⟨U, hU⟩ := exists_polar_isometryEquiv A
  calc
    LinearMap.traceNorm A = LinearMap.traceNorm (sqrt (H := H) (A.adjoint * A)) :=
      (congrArg LinearMap.traceNorm hU).trans (traceNorm_isometryEquiv_mul U _)
    _ = _ := by
      apply le_antisymm _ (LinearMap.norm_trace_le_traceNorm _)
      rw [(sqrt_positive (H := H) (A.adjoint * A)).traceNorm_eq_re_trace]
      exact Complex.re_le_norm _

/-- The trace norm is attained by pairing with a unitary operator. -/
lemma exists_isometryEquiv_norm_trace_eq (A : Operator H) :
    ∃ U : H.state ≃ₗᵢ[ℂ] H.state,
      ‖Operator.trace (H := H) (U.toLinearMap * A)‖ = LinearMap.traceNorm A := by
  obtain ⟨V, hV⟩ := exists_polar_isometryEquiv A
  let P := sqrt (H := H) (A.adjoint * A)
  change A = V.toLinearMap * P at hV
  have he : V.symm.toLinearMap * A = P := by
    conv_lhs => rw [hV]
    ext x
    exact V.symm_apply_apply _
  have hn : LinearMap.traceNorm A = LinearMap.traceNorm P := by
    exact (congrArg LinearMap.traceNorm hV).trans (traceNorm_isometryEquiv_mul V P)
  refine ⟨V.symm, ?_⟩
  rw [he, hn]
  apply le_antisymm (LinearMap.norm_trace_le_traceNorm P)
  rw [(sqrt_positive (H := H) (A.adjoint * A)).traceNorm_eq_re_trace]
  exact Complex.re_le_norm _

/-- Contractive maps on either side cannot increase the trace norm, even across dimensions. -/
lemma traceNorm_sandwich_le (A : Operator H) (f : H.state →ₗ[ℂ] K.state)
    (g : K.state →ₗ[ℂ] H.state)
    (hf : ‖f.toContinuousLinearMap‖ ≤ 1) (hg : ‖g.toContinuousLinearMap‖ ≤ 1) :
    LinearMap.traceNorm (f ∘ₗ A ∘ₗ g) ≤ LinearMap.traceNorm A := by
  apply LinearMap.traceNorm_le (LinearMap.traceNorm_nonneg A)
  intro B
  have ht : LinearMap.trace ℂ K.state (B.toLinearMap * (f ∘ₗ A ∘ₗ g)) =
      LinearMap.trace ℂ H.state ((g ∘ₗ B.toLinearMap ∘ₗ f) * A) := by
    change LinearMap.trace ℂ K.state (B.toLinearMap ∘ₗ f ∘ₗ A ∘ₗ g) = _
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    rfl
  rw [ht]
  have hn : ‖(g ∘ₗ B.toLinearMap ∘ₗ f : Operator H)‖ ≤ ‖B‖ := by
    change ‖g.toContinuousLinearMap.comp (B.comp f.toContinuousLinearMap)‖ ≤ ‖B‖
    calc
      _ ≤ ‖g.toContinuousLinearMap‖ * ‖B.comp f.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B.comp f.toContinuousLinearMap‖ := mul_le_of_le_one_left (norm_nonneg _) hg
      _ ≤ ‖B‖ * ‖f.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ := mul_le_of_le_one_right (norm_nonneg _) hf
  exact (LinearMap.norm_trace_mul_le A _).trans
    ((mul_le_mul_of_nonneg_right hn (LinearMap.traceNorm_nonneg A)).trans_eq (mul_comm _ _))

/-- The adjoint of an isometry is contractive, including between unequal dimensions. -/
lemma opNorm_adjoint_linearIsometry_le_one (V : H.state →ₗᵢ[ℂ] K.state) :
    ‖V.toLinearMap.adjoint.toContinuousLinearMap‖ ≤ 1 := by
  change ‖V.toLinearMap.toContinuousLinearMap.adjoint‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact opNorm_linearIsometry_le_one V

/-- Isometric embeddings on either side preserve the trace norm. -/
lemma traceNorm_isometry_sandwich (A : Operator H) (V W : H.state →ₗᵢ[ℂ] K.state) :
    LinearMap.traceNorm (V.toLinearMap ∘ₗ A ∘ₗ W.toLinearMap.adjoint) =
      LinearMap.traceNorm A := by
  apply le_antisymm
  · exact traceNorm_sandwich_le A _ _ (opNorm_linearIsometry_le_one V)
      (opNorm_adjoint_linearIsometry_le_one W)
  · have h := traceNorm_sandwich_le (H := K) (K := H)
      (V.toLinearMap ∘ₗ A ∘ₗ W.toLinearMap.adjoint) V.toLinearMap.adjoint W.toLinearMap
      (opNorm_adjoint_linearIsometry_le_one V) (opNorm_linearIsometry_le_one W)
    have he : V.toLinearMap.adjoint ∘ₗ
        (V.toLinearMap ∘ₗ A ∘ₗ W.toLinearMap.adjoint) ∘ₗ W.toLinearMap = A := by
      ext x
      change V.toLinearMap.adjoint (V (A (W.toLinearMap.adjoint (W x)))) = A x
      rw [show W.toLinearMap.adjoint (W x) = x from LinearMap.congr_fun W.adjoint_comp_self' x]
      exact LinearMap.congr_fun V.adjoint_comp_self' (A x)
    rwa [he] at h

end Operator

namespace Superoperator

variable {ι : Type*} [Fintype ι]

/-- Vectorization identifies the vector inner product with the Hilbert-Schmidt pairing. -/
lemma inner_vectorize_vectorize (b : OrthonormalBasis ι ℂ K.state)
    (A B : K.state →ₗ[ℂ] H.state) :
    inner ℂ (vectorize b A) (vectorize b B) = LinearMap.trace ℂ K.state (A.adjoint ∘ₗ B) := by
  conv_lhs => rw [vectorize_apply]
  rw [sum_inner, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_vectorize, LinearMap.comp_apply, LinearMap.adjoint_inner_right]

/-- The retained marginal of a vectorized amplitude is its left Gram operator. -/
lemma partialTraceRight_outer_vectorize (b : OrthonormalBasis ι ℂ K.state)
    (A : K.state →ₗ[ℂ] H.state) :
    Operator.partialTraceRight (Operator.outer (vectorize b A) (vectorize b A)) =
      A ∘ₗ A.adjoint := by
  rw [vectorize_apply, Operator.partialTraceRight_outer_sum_tmul]
  ext x
  simp only [LinearMap.sum_apply, Operator.outer_apply, LinearMap.comp_apply]
  simp_rw [← LinearMap.adjoint_inner_right]
  simpa only [map_sum, map_smul] using congrArg A (b.sum_repr' (A.adjoint x))

/-- The operator recovered from a purification factors its retained density. -/
lemma unvectorize_comp_adjoint (b : OrthonormalBasis ι ℂ K.state)
    (ψ : UnitState (H ⊗ K)) :
    unvectorize b ψ.val ∘ₗ (unvectorize b ψ.val).adjoint =
      (Density.pure ψ).partialTraceRight.op := by
  rw [← partialTraceRight_outer_vectorize b, vectorize_unvectorize]
  rfl

end Superoperator

namespace Density

/-- Unsquared fidelity: the trace norm of the product of the positive square roots. -/
def fidelity (ρ σ : Density H) : ℝ := LinearMap.traceNorm (ρ.op.sqrt * σ.op.sqrt)

/-- Fidelity is nonnegative. -/
lemma fidelity_nonneg (ρ σ : Density H) : 0 ≤ ρ.fidelity σ :=
  LinearMap.traceNorm_nonneg _

/-- Any amplitude factor of a density is its positive square root followed by a coisometry,
provided the amplitude's input space has at least the system dimension. -/
lemma exists_isometry_sqrt_factor (ρ : Density H) (A : K.state →ₗ[ℂ] H.state)
    (hA : A ∘ₗ A.adjoint = ρ.op)
    (hdim : Module.finrank ℂ H.state ≤ Module.finrank ℂ K.state) :
    ∃ V : H.state →ₗᵢ[ℂ] K.state,
      A = ρ.op.sqrt ∘ₗ V.toLinearMap.adjoint := by
  have hg : ρ.op.sqrt.adjoint ∘ₗ ρ.op.sqrt = A ∘ₗ A.adjoint := by
    rw [Operator.adjoint_sqrt, hA]
    exact ρ.op.sqrt_mul_sqrt ρ.positive
  obtain ⟨V, hV⟩ := ρ.op.sqrt.exists_linearIsometry_comp_eq A.adjoint (by
    intro x y
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.adjoint_inner_right,
      LinearMap.adjoint_adjoint]
    exact congrArg (inner ℂ x) (LinearMap.congr_fun hg y)) hdim
  refine ⟨V, ?_⟩
  have h := congrArg LinearMap.adjoint hV
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, Operator.adjoint_sqrt]
    using h.symm

/-- Fidelity equals the trace norm of the cross Gram operator of any two amplitude factors. -/
lemma fidelity_eq_traceNorm_cross (ρ σ : Density H) (A B : K.state →ₗ[ℂ] H.state)
    (hA : A ∘ₗ A.adjoint = ρ.op) (hB : B ∘ₗ B.adjoint = σ.op) :
    ρ.fidelity σ = LinearMap.traceNorm (A.adjoint ∘ₗ B) := by
  have large {L : Qudit} (C D : L.state →ₗ[ℂ] H.state)
      (hC : C ∘ₗ C.adjoint = ρ.op) (hD : D ∘ₗ D.adjoint = σ.op)
      (hdim : Module.finrank ℂ H.state ≤ Module.finrank ℂ L.state) :
      ρ.fidelity σ = LinearMap.traceNorm (C.adjoint ∘ₗ D) := by
    obtain ⟨V, hV⟩ := ρ.exists_isometry_sqrt_factor C hC hdim
    obtain ⟨W, hW⟩ := σ.exists_isometry_sqrt_factor D hD hdim
    rw [hV, hW, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, Operator.adjoint_sqrt]
    exact (Operator.traceNorm_isometry_sandwich (ρ.op.sqrt * σ.op.sqrt) V W).symm
  rcases le_total (Module.finrank ℂ H.state) (Module.finrank ℂ K.state) with hdim | hdim
  · exact large A B hA hB hdim
  · let J : K.state →ₗᵢ[ℂ] H.state := LinearIsometry.ofFinrankLE hdim
    have hf (C : K.state →ₗ[ℂ] H.state) :
        (C ∘ₗ J.toLinearMap.adjoint) ∘ₗ (C ∘ₗ J.toLinearMap.adjoint).adjoint =
          C ∘ₗ C.adjoint := by
      rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
      ext x
      change C (J.toLinearMap.adjoint (J (C.adjoint x))) = C (C.adjoint x)
      rw [show J.toLinearMap.adjoint (J (C.adjoint x)) = C.adjoint x
        from LinearMap.congr_fun J.adjoint_comp_self' _]
    have h := large (A ∘ₗ J.toLinearMap.adjoint) (B ∘ₗ J.toLinearMap.adjoint)
      ((hf A).trans hA) ((hf B).trans hB) le_rfl
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at h
    exact h.trans (Operator.traceNorm_isometry_sandwich (H := K) (A.adjoint ∘ₗ B) J J)

/-- Any two purifications on a common auxiliary space have overlap bounded by fidelity.
There is no dimension hypothesis on that space. -/
theorem norm_inner_le_fidelity (ρ σ : Density H) (ψ φ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ) (hφ : (pure φ).partialTraceRight = σ) :
    ‖inner ℂ ψ.val φ.val‖ ≤ ρ.fidelity σ := by
  let b := stdOrthonormalBasis ℂ K.state
  let A := Superoperator.unvectorize b ψ.val
  let B := Superoperator.unvectorize b φ.val
  rw [ρ.fidelity_eq_traceNorm_cross σ A B
    ((Superoperator.unvectorize_comp_adjoint b ψ).trans (congrArg Density.op hψ))
    ((Superoperator.unvectorize_comp_adjoint b φ).trans (congrArg Density.op hφ))]
  have hi : inner ℂ ψ.val φ.val = LinearMap.trace ℂ K.state (A.adjoint ∘ₗ B) := by
    rw [← Superoperator.inner_vectorize_vectorize b, Superoperator.vectorize_unvectorize,
      Superoperator.vectorize_unvectorize]
  rw [hi]
  exact LinearMap.norm_trace_le_traceNorm _

/-- An amplitude factor of a density defines a normalized purification in any auxiliary basis. -/
def purifyOfFactor (ρ : Density H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) (A : K.state →ₗ[ℂ] H.state)
    (hA : A ∘ₗ A.adjoint = ρ.op) : UnitState (H ⊗ K) :=
  ⟨Superoperator.vectorize b A, by
    have ht := (LinearMap.trace_partialTraceRight _).symm.trans
      (congrArg Operator.trace ((Superoperator.partialTraceRight_outer_vectorize b A).trans hA))
    exact (Operator.trace_outer _ _).symm.trans (ht.trans ρ.trace_one)⟩

/-- A vectorized amplitude factor has the prescribed retained marginal. -/
lemma partialTraceRight_pure_purifyOfFactor (ρ : Density H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) (A : K.state →ₗ[ℂ] H.state)
    (hA : A ∘ₗ A.adjoint = ρ.op) :
    (pure (ρ.purifyOfFactor b A hA)).partialTraceRight = ρ := by
  apply Density.ext
  exact (Superoperator.partialTraceRight_outer_vectorize b A).trans hA

/-- **Uhlmann's theorem** with one purification fixed. The target rank bound is necessary
and sufficient; the given purification already guarantees the source rank bound. -/
theorem exists_purification_norm_inner_eq_fidelity (ρ σ : Density H)
    (ψ : UnitState (H ⊗ K)) (hψ : (pure ψ).partialTraceRight = ρ)
    (hdim : Module.finrank ℂ (LinearMap.range σ.op) ≤ Module.finrank ℂ K.state) :
    ∃ φ : UnitState (H ⊗ K), (pure φ).partialTraceRight = σ ∧
      ‖inner ℂ ψ.val φ.val‖ = ρ.fidelity σ := by
  obtain ⟨φ₀, hφ₀⟩ := σ.exists_purification_iff_finrank_le.mpr hdim
  let b := stdOrthonormalBasis ℂ K.state
  let A := Superoperator.unvectorize b ψ.val
  let B := Superoperator.unvectorize b φ₀.val
  have hA := (Superoperator.unvectorize_comp_adjoint b ψ).trans (congrArg Density.op hψ)
  have hB := (Superoperator.unvectorize_comp_adjoint b φ₀).trans (congrArg Density.op hφ₀)
  obtain ⟨U, hU⟩ := Operator.exists_isometryEquiv_norm_trace_eq (H := K) (A.adjoint ∘ₗ B)
  let C := B ∘ₗ U.toLinearMap
  have hC : C ∘ₗ C.adjoint = σ.op := by
    dsimp only [C]
    rw [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    calc
      _ = B ∘ₗ B.adjoint := by
        ext x
        change B (U (U.symm (B.adjoint x))) = B (B.adjoint x)
        rw [U.apply_symm_apply]
      _ = σ.op := hB
  refine ⟨σ.purifyOfFactor b C hC, σ.partialTraceRight_pure_purifyOfFactor b C hC, ?_⟩
  change ‖inner ℂ ψ.val (Superoperator.vectorize b C)‖ = _
  have hi : inner ℂ ψ.val (Superoperator.vectorize b C) =
      LinearMap.trace ℂ K.state (A.adjoint ∘ₗ C) := by
    rw [← Superoperator.inner_vectorize_vectorize b, Superoperator.vectorize_unvectorize]
  rw [hi, ρ.fidelity_eq_traceNorm_cross σ A B hA hB]
  change ‖LinearMap.trace ℂ K.state (A.adjoint ∘ₗ B ∘ₗ U.toLinearMap)‖ = _
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  exact hU

/-- **Uhlmann's theorem** with the phase chosen so that the overlap itself is the nonnegative
real fidelity, rather than only having that modulus. -/
theorem exists_purification_inner_eq_fidelity (ρ σ : Density H)
    (ψ : UnitState (H ⊗ K)) (hψ : (pure ψ).partialTraceRight = ρ)
    (hdim : Module.finrank ℂ (LinearMap.range σ.op) ≤ Module.finrank ℂ K.state) :
    ∃ φ : UnitState (H ⊗ K), (pure φ).partialTraceRight = σ ∧
      inner ℂ ψ.val φ.val = (ρ.fidelity σ : ℂ) := by
  obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ψ hψ hdim
  obtain ⟨c, hc, hz⟩ := Complex.exists_norm_eq_mul_self (inner ℂ ψ.val φ.val)
  refine ⟨φ.phase c hc, ?_, ?_⟩
  · rwa [pure_phase]
  · rw [UnitState.coe_phase, inner_smul_right, ← hz, he]

/-- The maximum in **Uhlmann's theorem** is attained on exactly the auxiliary spaces that
can purify the target state. -/
theorem exists_purification_norm_inner_eq_fidelity_iff (ρ σ : Density H)
    (ψ : UnitState (H ⊗ K)) (hψ : (pure ψ).partialTraceRight = ρ) :
    (∃ φ : UnitState (H ⊗ K), (pure φ).partialTraceRight = σ ∧
      ‖inner ℂ ψ.val φ.val‖ = ρ.fidelity σ) ↔
      Module.finrank ℂ (LinearMap.range σ.op) ≤ Module.finrank ℂ K.state := by
  constructor
  · rintro ⟨φ, hφ, _⟩
    exact σ.finrank_range_le_of_purification φ hφ
  · exact ρ.exists_purification_norm_inner_eq_fidelity σ ψ hψ

/-- **Uhlmann's maximum**, with one purification fixed and the sharp auxiliary rank bound. -/
theorem isGreatest_purification_overlap (ρ σ : Density H) (ψ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ)
    (hdim : Module.finrank ℂ (LinearMap.range σ.op) ≤ Module.finrank ℂ K.state) :
    IsGreatest ((fun φ : UnitState (H ⊗ K) => ‖inner ℂ ψ.val φ.val‖) ''
      {φ | (pure φ).partialTraceRight = σ}) (ρ.fidelity σ) := by
  obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ψ hψ hdim
  refine ⟨⟨φ, hφ, he⟩, ?_⟩
  rintro r ⟨χ, hχ, rfl⟩
  exact ρ.norm_inner_le_fidelity σ ψ χ hψ hχ

/-- Squaring both sides gives the squared-fidelity convention for Uhlmann's maximum. -/
theorem isGreatest_purification_overlap_sq (ρ σ : Density H) (ψ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ)
    (hdim : Module.finrank ℂ (LinearMap.range σ.op) ≤ Module.finrank ℂ K.state) :
    IsGreatest ((fun φ : UnitState (H ⊗ K) => ‖inner ℂ ψ.val φ.val‖ ^ 2) ''
      {φ | (pure φ).partialTraceRight = σ}) (ρ.fidelity σ ^ 2) := by
  obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ψ hψ hdim
  refine ⟨⟨φ, hφ, congrArg (fun r : ℝ => r ^ 2) he⟩, ?_⟩
  rintro r ⟨χ, hχ, rfl⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (ρ.norm_inner_le_fidelity σ ψ χ hψ hχ) 2

/-- Starting from any two purifications on a common auxiliary space, a unitary on that
space attains fidelity while leaving both retained densities unchanged. -/
theorem exists_unitary_norm_inner_eq_fidelity (ρ σ : Density H)
    (ψ φ : UnitState (H ⊗ K))
    (hψ : (pure ψ).partialTraceRight = ρ) (hφ : (pure φ).partialTraceRight = σ) :
    ∃ (U : K ⟶ K) (_ : IsUnitary U),
      ‖inner ℂ ψ.val (φ.map (𝟙 H ⊗ₘ U)).val‖ = ρ.fidelity σ := by
  obtain ⟨χ, hχ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ψ hψ
    (σ.finrank_range_le_of_purification φ hφ)
  obtain ⟨U, hU, rfl⟩ := σ.exists_unitary_of_purifications φ χ rfl hφ hχ
  exact ⟨U, hU, he⟩

/-- A state has fidelity one with itself. -/
@[simp]
lemma fidelity_self (ρ : Density H) : ρ.fidelity ρ = 1 := by
  rw [fidelity, Operator.sqrt_mul_sqrt _ ρ.positive, ρ.positive.traceNorm_eq_re_trace]
  change ρ.op.trace.re = 1
  rw [ρ.trace_one, Complex.one_re]

/-- Fidelity between density operators is at most one. -/
lemma fidelity_le_one (ρ σ : Density H) : ρ.fidelity σ ≤ 1 := by
  obtain ⟨φ, _, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ρ.purify
    ρ.partialTraceRight_pure_purify (LinearMap.finrank_range_le σ.op)
  rw [← he]
  simpa only [ρ.purify.norm_eq_one, φ.norm_eq_one, one_mul] using
    norm_inner_le_norm (𝕜 := ℂ) ρ.purify.val φ.val

/-- Fidelity is symmetric in the two density operators. -/
lemma fidelity_comm (ρ σ : Density H) : ρ.fidelity σ = σ.fidelity ρ := by
  have h (a b : Density H) : a.fidelity b ≤ b.fidelity a := by
    obtain ⟨φ, hφ, he⟩ := a.exists_purification_norm_inner_eq_fidelity b a.purify
      a.partialTraceRight_pure_purify (LinearMap.finrank_range_le b.op)
    rw [← he, norm_inner_symm]
    exact b.norm_inner_le_fidelity a φ a.purify hφ a.partialTraceRight_pure_purify
  exact le_antisymm (h ρ σ) (h σ ρ)

/-- Two densities have zero fidelity exactly when their supports are orthogonal. -/
lemma fidelity_eq_zero_iff (ρ σ : Density H) : ρ.fidelity σ = 0 ↔ ρ.support ⟂ σ.support := by
  have hr (τ : Density H) : LinearMap.range τ.op.sqrt = τ.support := by
    simpa only [support, Operator.adjoint_sqrt, ← Module.End.mul_eq_comp,
      Operator.sqrt_mul_sqrt _ τ.positive] using τ.op.sqrt.range_self_comp_adjoint.symm
  rw [fidelity_comm, fidelity, LinearMap.traceNorm_eq_zero_iff, Module.End.mul_eq_comp,
    ← LinearMap.range_le_ker_iff, ← σ.op.sqrt_positive.isSymmetric.orthogonal_range, hr, hr]
  rfl

/-- Fidelity against a pure density is the square root of its projector expectation.
This uses the unsquared convention and includes zero expectations and singular densities. -/
lemma fidelity_pure (ρ : Density H) (v : UnitState H) :
    ρ.fidelity (pure v) = Real.sqrt (ρ.expectation (pure v).op) := by
  let r := ρ.expectation (pure v).op
  have hr : 0 ≤ r := ρ.expectation_nonneg (pure v).positive
  have hc : (r : ℂ) = inner ℂ v.val (ρ.op v.val) := by
    have hi := ρ.expectationComplex_im_eq_zero (pure v).positive.isSelfAdjoint
    have he : ρ.expectationComplex (pure v).op = inner ℂ v.val (ρ.op v.val) := by
      exact (LinearMap.trace_mul_comm ℂ (pure v).op ρ.op).trans
        (Operator.trace_mul_outer ρ.op v.val v.val)
    rw [← he]
    exact Complex.ext rfl (by simpa using hi.symm)
  have hs : (pure v).op.sqrt = (pure v).op :=
    Operator.sqrt_eq_self _ (pure v).positive (pure_mul_self v)
  have hg : (ρ.op.sqrt * (pure v).op).adjoint * (ρ.op.sqrt * (pure v).op) =
      (r : ℂ) • (pure v).op := by
    change (ρ.op.sqrt ∘ₗ (pure v).op).adjoint * _ = _
    rw [LinearMap.adjoint_comp]
    change ((pure v).op.adjoint * ρ.op.sqrt.adjoint) *
      (ρ.op.sqrt * (pure v).op) = _
    rw [adjoint_op, Operator.adjoint_sqrt, mul_assoc,
      ← mul_assoc ρ.op.sqrt, Operator.sqrt_mul_sqrt _ ρ.positive]
    ext x
    simp only [mul_apply_eq_comp, pure_apply, map_smul,
      LinearMap.smul_apply, smul_smul, hc]
    rw [mul_comm]
  have hroot : Operator.sqrt (H := H) ((r : ℂ) • (pure v).op) =
      (Real.sqrt r : ℂ) • (pure v).op := by
    apply Operator.sqrt_unique _ ((pure v).positive.smul_of_nonneg (by
      exact_mod_cast Real.sqrt_nonneg r))
    rw [smul_mul_smul_comm, pure_mul_self, ← pow_two, ← Complex.ofReal_pow,
      Real.sq_sqrt hr]
  rw [fidelity, hs, Operator.traceNorm_eq_norm_trace_sqrt_adjoint_mul, hg, hroot]
  change ‖LinearMap.trace ℂ H.state ((Real.sqrt r : ℂ) • (pure v).op)‖ = _
  rw [map_smul]
  change ‖(Real.sqrt r : ℂ) * (pure v).op.trace‖ = _
  rw [(pure v).trace_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg r)]

/-- Squared fidelity against a pure density is its projector expectation. -/
lemma fidelity_pure_sq (ρ : Density H) (v : UnitState H) :
    ρ.fidelity (pure v) ^ 2 = ρ.expectation (pure v).op := by
  rw [fidelity_pure, Real.sq_sqrt (ρ.expectation_nonneg (pure v).positive)]

/-- Fidelity with a pure density in the first argument, in the unsquared convention. -/
lemma pure_fidelity (v : UnitState H) (ρ : Density H) :
    (pure v).fidelity ρ = Real.sqrt (ρ.expectation (pure v).op) := by
  rw [fidelity_comm, fidelity_pure]

/-- Squared fidelity with a pure density in the first argument. -/
lemma pure_fidelity_sq (v : UnitState H) (ρ : Density H) :
    (pure v).fidelity ρ ^ 2 = ρ.expectation (pure v).op := by
  rw [fidelity_comm, fidelity_pure_sq]

/-- Fidelity of pure densities is the modulus of the existing unit-vector inner product. -/
lemma fidelity_pure_pure (v w : UnitState H) :
    (pure v).fidelity (pure w) = ‖inner ℂ v.val w.val‖ := by
  have hf (u : UnitState H) :
      LinearMap.toSpanSingleton ℂ H.state u.val ∘ₗ
        (LinearMap.toSpanSingleton ℂ H.state u.val).adjoint = (pure u).op := by
    rw [LinearMap.adjoint_toSpanSingleton]
    rfl
  rw [fidelity_eq_traceNorm_cross (K := 𝟙_ Qudit) (pure v) (pure w)
    (LinearMap.toSpanSingleton ℂ H.state v.val) (LinearMap.toSpanSingleton ℂ H.state w.val)
    (hf v) (hf w), LinearMap.adjoint_toSpanSingleton]
  have he : innerₛₗ ℂ v.val ∘ₗ LinearMap.toSpanSingleton ℂ H.state w.val =
      inner ℂ v.val w.val • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
    apply LinearMap.ext
    intro c
    simp [inner_smul_right, mul_comm]
  rw [he, LinearMap.traceNorm_smul,
    (LinearMap.isPositive_id (𝕜 := ℂ) (E := ℂ)).traceNorm_eq_re_trace]
  simp [LinearMap.trace_id]

/-- Squared pure-state fidelity agrees with the existing density expectation interface. -/
lemma fidelity_pure_pure_sq (v w : UnitState H) :
    (pure v).fidelity (pure w) ^ 2 = (pure v).expectation (pure w).op := by
  rw [fidelity_pure_pure, expectation_pure_pure, norm_inner_symm]

/-- Fidelity one characterizes equality of density operators. -/
lemma fidelity_eq_one_iff (ρ σ : Density H) : ρ.fidelity σ = 1 ↔ ρ = σ := by
  constructor
  · intro h
    obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ρ.purify
      ρ.partialTraceRight_pure_purify (LinearMap.finrank_range_le σ.op)
    have hp : pure ρ.purify = pure φ :=
      (expectation_pure_pure_eq_one_iff ρ.purify φ).mp (by
        rw [expectation_pure_pure, norm_inner_symm, he, h, one_pow])
    exact ρ.partialTraceRight_pure_purify.symm.trans
      ((congrArg Density.partialTraceRight hp).trans hφ)
  · rintro rfl
    exact ρ.fidelity_self

end Density

end

end Qudit
