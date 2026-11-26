/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.Decoding
public import FQFP.CQM.Qudit.Channel.Capacity.PhaseAveraging

/-!
# Spectral random phase codes

Independent phases on the square-root-weighted eigenvectors of an input density give
normalized physical vectors. After a dilation, their environment marginal fluctuates
around the environment output on the original mixed input.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct ComplexConjugate

namespace Qudit

variable {H B E : Qudit}

/-- A spectral input vector carrying the square root of its eigenvalue. -/
def Density.spectralAmplitude (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :=
  (Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i

private lemma Density.sum_outer_spectralAmplitude (ρ : Density H) :
    ∑ i, Operator.outer (ρ.spectralAmplitude i) (ρ.spectralAmplitude i) = ρ.op := by
  rw [ρ.op_eq_sum_eigenvalue_smul_outer]
  simp only [spectralAmplitude, Operator.outer_smul_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow, Real.sq_sqrt (ρ.eigenvalue_nonneg _)]

/-- A normalized physical input with the prescribed spectral weights and independent phases. -/
def Density.spectralPhaseState (ρ : Density H) (z : Fin (Module.finrank ℂ H.state) → ZMod 3) :
    UnitState H :=
  ⟨∑ i, ZMod.stdAddChar (z i) • ρ.spectralAmplitude i, by
    let c i := ZMod.stdAddChar (z i) * (Real.sqrt (ρ.eigenvalue i) : ℂ)
    change inner ℂ _ _ = 1
    simp only [spectralAmplitude, smul_smul, sum_inner, inner_sum, inner_smul_right,
      inner_smul_left, ρ.eigenbasis.inner_eq_ite, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change ∑ i, c i * conj (c i) = 1
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq, c, norm_mul, AddChar.norm_apply,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (ρ.eigenvalue_nonneg _), ← Complex.ofReal_sum, ρ.sum_eigenvalue,
      Complex.ofReal_one]⟩

private lemma Density.sum_norm_sq_spectralAmplitude (ρ : Density H) (T : H.state →ₗ[ℂ] B.state) :
    ∑ i, ‖T (ρ.spectralAmplitude i)‖ ^ 2 = ρ.expectation (T.adjoint ∘ₗ T) := by
  rw [expectation, expectationComplex, ← ρ.sum_outer_spectralAmplitude]
  simp only [Finset.mul_sum, map_sum, Operator.trace_mul_outer,
    Complex.re_sum, Operator.re_inner_adjoint_comp_self]

/-- The average squared norm after any linear filter is its acceptance probability
in the original mixed state. Taking the rejected part of a projection gives its mean loss. -/
theorem Density.expect_norm_sq_spectralPhaseState (ρ : Density H) (T : H.state →ₗ[ℂ] B.state) :
    (𝔼 z, ‖T (ρ.spectralPhaseState z).val‖ ^ 2) = ρ.expectation (T.adjoint ∘ₗ T) := by
  simpa only [spectralPhaseState, map_sum, map_smul, Superoperator.expect_norm_sq_phase_sum] using
    ρ.sum_norm_sq_spectralAmplitude T

namespace Superoperator

private lemma inner_reverse_gram {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ B.state)
    (f : B.state →ₗ[ℂ] E.state) (i j : ι) :
    inner ℂ (b i) ((f.adjoint ∘ₗ f) (b j)) = inner ℂ (b j)
      (Operator.partialTraceLeft (Operator.outer (vectorize b f) (vectorize b f)) (b i)) := by
  let e := stdOrthonormalBasis ℂ E.state
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, Operator.inner_partialTraceLeft e,
    ← e.sum_inner_mul_inner (f (b i)) (f (b j))]
  apply Finset.sum_congr rfl
  intro a _
  rw [Operator.outer_apply, inner_smul_right, inner_vectorize,
    ← inner_conj_symm (vectorize b f) (e a ⊗ₜ[ℂ] b i), inner_vectorize, inner_conj_symm]

end Superoperator

private lemma traceNorm_outer_le (u v : H.state) :
    LinearMap.traceNorm (Operator.outer u v) ≤ ‖u‖ * ‖v‖ := by
  apply LinearMap.traceNorm_le (by positivity)
  intro T
  change ‖Operator.trace (T.toLinearMap * Operator.outer u v)‖ ≤ _
  rw [Operator.trace_mul_outer]
  exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left
    (T.le_opNorm u) (norm_nonneg v)).trans_eq (by ring))

/-- Trace-norm disturbance of cutting down a pure vector, including an unnormalized
retained vector. Discarding a subsystem preserves the bound. -/
theorem Operator.traceNorm_partialTraceRight_outer_sub_le (u v : (E ⊗ B).state) :
    LinearMap.traceNorm (Operator.partialTraceRight (Operator.outer u u - Operator.outer v v)) ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hsym := (Operator.isPositive_outer u).isSymmetric.sub
    (Operator.isPositive_outer v).isSymmetric
  apply (hsym.traceNorm_map_le Operator.partialTraceRight
    (fun _ h => h.partialTraceRight) (fun _ => LinearMap.trace_partialTraceRight _)).trans
  have he : Operator.outer u u - Operator.outer v v =
      Operator.outer (u - v) u + Operator.outer v (u - v) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Operator.outer_apply,
      inner_sub_left, smul_sub, sub_smul]
    abel
  rw [he]
  calc
    _ ≤ _ := LinearMap.traceNorm_add_le _ _
    _ ≤ ‖u - v‖ * ‖u‖ + ‖v‖ * ‖u - v‖ := add_le_add (traceNorm_outer_le ..) (traceNorm_outer_le ..)
    _ = _ := by ring

/-- For the same phases used in the random code, replacing a dilation by a contraction
costs at most four times its mean squared vector loss in squared marginal trace norm. -/
theorem Density.expect_phase_marginal_disturbance_sq_le (ρ : Density H)
    (J : H.state →ₗᵢ[ℂ] (E ⊗ B).state) (T : H.state →ₗ[ℂ] (E ⊗ B).state)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    (𝔼 z, let v := (ρ.spectralPhaseState z).val
      LinearMap.traceNorm (Operator.partialTraceRight
        (Operator.outer (J v) (J v) - Operator.outer (T v) (T v))) ^ 2) ≤
      4 * ρ.expectation ((J.toLinearMap - T).adjoint ∘ₗ (J.toLinearMap - T)) := by
  rw [← ρ.expect_norm_sq_spectralPhaseState, Finset.mul_expect]
  apply Finset.expect_le_expect
  intro z _
  let v := ρ.spectralPhaseState z
  have hb := Operator.traceNorm_partialTraceRight_outer_sub_le (J v.val) (T v.val)
  have hnorm : ‖J v.val‖ + ‖T v.val‖ ≤ 2 := by
    rw [J.norm_map]
    linarith only [v.norm_eq_one, hT v.val]
  have ht := hb.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have hs := (sq_le_sq₀ (LinearMap.traceNorm_nonneg _) (by positivity)).mpr ht
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, LinearMap.sub_apply,
    LinearIsometry.coe_toLinearMap] using hs

/-- The same vector loss controls the disturbance of the mixed marginal about which the
random code concentrates. -/
theorem Density.traceNorm_mixed_marginal_disturbance_sq_le (ρ : Density H)
    (J : H.state →ₗᵢ[ℂ] (E ⊗ B).state) (T : H.state →ₗ[ℂ] (E ⊗ B).state)
    (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    LinearMap.traceNorm (Operator.partialTraceRight
      (Superoperator.conjugate J.toLinearMap ρ.op - Superoperator.conjugate T ρ.op)) ^ 2 ≤
      4 * ρ.expectation ((J.toLinearMap - T).adjoint ∘ₗ (J.toLinearMap - T)) := by
  let v := ρ.spectralAmplitude
  let L := J.toLinearMap - T
  have hsum : ∑ i, ‖v i‖ ^ 2 = 1 := by
    simp only [v, spectralAmplitude, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ρ.eigenbasis.norm_eq_one, mul_one,
      Real.sq_sqrt (ρ.eigenvalue_nonneg _), ρ.sum_eigenvalue]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun i => ‖L (v i)‖)
  rw [hsum, one_mul, ρ.sum_norm_sq_spectralAmplitude] at hcs
  have ht : LinearMap.traceNorm (Operator.partialTraceRight
      (Superoperator.conjugate J.toLinearMap ρ.op - Superoperator.conjugate T ρ.op)) ≤
      2 * ∑ i, ‖v i‖ * ‖L (v i)‖ := by
    rw [← ρ.sum_outer_spectralAmplitude, map_sum, map_sum, ← Finset.sum_sub_distrib, map_sum,
      Finset.mul_sum]
    apply (LinearMap.traceNorm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    simp only [Superoperator.conjugate_outer, LinearIsometry.coe_toLinearMap]
    apply (Operator.traceNorm_partialTraceRight_outer_sub_le _ _).trans
    change (‖J (v i)‖ + ‖T (v i)‖) * _ ≤ _
    rw [J.norm_map, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith only [hT (v i)]
  calc
    _ ≤ (2 * ∑ i, ‖v i‖ * ‖L (v i)‖) ^ 2 :=
      (sq_le_sq₀ (LinearMap.traceNorm_nonneg _) (by positivity)).mpr ht
    _ ≤ _ := by
      rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact mul_le_mul_of_nonneg_left hcs (by norm_num : 0 ≤ (4 : ℝ))

open Superoperator

/-- The phase estimate for a general linear filter on the joint output. It also applies
after projection onto typical subspaces, where the joint output may be subnormalized. -/
theorem Density.expect_phase_partialTraceRight_sq_le (ρ : Density H)
    (T : H.state →ₗ[ℂ] (E ⊗ B).state) :
    (𝔼 z, LinearMap.traceNorm (Operator.partialTraceRight
      (conjugate T (Density.pure (ρ.spectralPhaseState z)).op) -
        Operator.partialTraceRight (conjugate T ρ.op)) ^ 2) ≤
      Module.finrank ℂ E.state * (Operator.partialTraceLeft (conjugate T ρ.op) ^ 2).trace.re := by
  classical
  let τ := Operator.partialTraceLeft (conjugate T ρ.op)
  have hτ : τ.IsSymmetric := (ρ.positive.conj_adjoint T).partialTraceLeft.isSymmetric
  let b := hτ.eigenvectorBasis rfl
  let v i := T (ρ.spectralAmplitude i)
  let f i := unvectorize b (v i)
  have hsum : ∑ i, Operator.outer (v i) (v i) = conjugate T ρ.op := by
    rw [← ρ.sum_outer_spectralAmplitude, map_sum]
    simp only [conjugate_outer, v]
  have henv : ∑ i, f i ∘ₗ (f i).adjoint = Operator.partialTraceRight (conjugate T ρ.op) := by
    rw [← hsum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← partialTraceRight_outer_vectorize b, vectorize_unvectorize]
  have hrecv : ∑ i, Operator.partialTraceLeft (Operator.outer (v i) (v i)) = τ := by
    rw [← map_sum, hsum]
  have hgram : ∑ i, (f i).adjoint ∘ₗ f i = τ := by
    apply b.toBasis.ext
    intro j
    apply InnerProductSpace.ext_inner_left_basis b.toBasis
    intro k
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.sum_apply, inner_sum,
      inner_reverse_gram b, f, vectorize_unvectorize]
    rw [← inner_sum, ← LinearMap.sum_apply, hrecv]
    simp only [b, hτ.apply_eigenvectorBasis, inner_smul_right, OrthonormalBasis.inner_eq_ite,
      mul_ite, mul_one, mul_zero]
    split_ifs with h h <;> first | subst_vars; rfl | simp_all
  have hphase z : phaseAmplitude f z ∘ₗ (phaseAmplitude f z).adjoint =
      Operator.partialTraceRight (conjugate T (Density.pure (ρ.spectralPhaseState z)).op) := by
    rw [Density.op_pure, conjugate_outer,
      ← partialTraceRight_outer_vectorize b]
    congr 2
    all_goals simp only [phaseAmplitude, map_sum, map_smul, f, vectorize_unvectorize,
      Density.spectralPhaseState, v]
  simpa only [hphase, henv, hgram] using expect_phase_traceNorm_sq_le f

namespace QuantumChannel

/-- A spectral phase input simulates the mixed input on the retained output. Its mean
squared trace-norm error costs at most retained dimension times discarded-output purity. -/
theorem Dilation.expect_spectralPhaseState_traceNorm_sq_le {Φ : QuantumChannel H E}
    (d : Φ.Dilation B) (ρ : Density H) :
    (𝔼 z, LinearMap.traceNorm
      ((Φ.map (Density.pure (ρ.spectralPhaseState z))).op - (Φ.map ρ).op) ^ 2) ≤
      Module.finrank ℂ E.state *
        (LinearMap.trace ℂ B.state ((d.complementary.map ρ).op ^ 2)).re := by
  simp only [op_map, d.channel_eq, LinearMap.comp_apply]
  exact ρ.expect_phase_partialTraceRight_sq_le d.toHom.hom

/-- There is a normalized input on the physical register and reference whose environment
approximates the product output. This finite-block bound uses the full environment dimension. -/
theorem Dilation.exists_input_traceDistance_sq_le {Φ : QuantumChannel H B} (d : Φ.Dilation E)
    {R : Qudit} (ρ : Density H) (τ : Density R) :
    ∃ v : UnitState (H ⊗ R),
      (2 * (((d.complementary.tensor (id R)).map (Density.pure v)).traceDistance
        ((d.complementary.map ρ).tensor τ))) ^ 2 ≤
        Module.finrank ℂ (E ⊗ R).state * (LinearMap.trace ℂ B.state ((Φ.map ρ).op ^ 2)).re := by
  let D : (Φ.comp (partialTraceRight H R)).Dilation (E ⊗ R) :=
    ⟨d.lift R, inferInstance, (d.partialTraceRight_lift R).symm⟩
  have hc : D.complementary = d.complementary.tensor (id R) :=
    (hasMarginals_iff.mp (d.hasMarginals_lift R)).2
  have hav := D.symm.expect_spectralPhaseState_traceNorm_sq_le (ρ.tensor τ)
  rw [D.complementary_symm, hc, map_comp, map_partialTraceRight, Density.partialTraceRight_tensor,
    map_tensor, map_id] at hav
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hav
  refine ⟨(ρ.tensor τ).spectralPhaseState z, ?_⟩
  rwa [Density.traceDistance, show ∀ x : ℝ, 2 * (x / 2) = x by
    intro x
    ring]

/-- A dimension-purity bound produces an actual finite-block code with entanglement root
fidelity at least `1 - ε`. The target may be any pure state on the logical input and reference. -/
theorem Dilation.exists_code_of_dim_mul_purity_le {Φ : QuantumChannel H B} (d : Φ.Dilation E)
    {C R : Qudit} (ρ : Density H) (t : UnitState (C ⊗ R)) {ε : ℝ} (hε : 0 ≤ ε)
    (h : Module.finrank ℂ (E ⊗ R).state * (LinearMap.trace ℂ B.state ((Φ.map ρ).op ^ 2)).re
      ≤ (ε ^ 2 / 4) ^ 2) :
    ∃ Ψ : QuantumChannel C C, Φ.Emulates Ψ ∧
      1 - ε ≤ ((Ψ.tensor (id R)).map (Density.pure t)).fidelity (Density.pure t) := by
  obtain ⟨v, hv⟩ := d.exists_input_traceDistance_sq_le ρ (Density.pure t).partialTraceLeft
  apply d.exists_code_of_decoupled_vector v t (d.complementary.map ρ) hε
  have hd := (sq_le_sq₀ (mul_nonneg (by norm_num) (Density.traceDistance_nonneg ..))
    (by positivity)).mp (hv.trans h)
  have hf := Density.one_sub_fidelity_le_traceDistance
    ((d.complementary.tensor (id R)).map (Density.pure v))
    ((d.complementary.map ρ).tensor (Density.pure t).partialTraceLeft)
  linarith only [hd, hf]

end QuantumChannel

end Qudit
