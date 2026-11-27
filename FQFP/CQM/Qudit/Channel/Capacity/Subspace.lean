/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.CoherentInformation
public import FQFP.CQM.Qudit.Channel.Degradation.IsometryRecovery
public import FQFP.CQM.Qudit.Error.FidelityConcavity
public import FQFP.CQM.Qudit.Entropy.EntanglementOfFormation

/-!
# Subspace transmission with worst-case root fidelity

Joint concavity reduces the operational error test to pure inputs. Expurgation removes
large singular directions of the difference between a channel dilation and a noiseless
embedding with a fixed environment state.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit.QuantumChannel

variable {H K E : Qudit}

/-- The worst-case root fidelity test on densities is equivalent to the test on all unit vectors. -/
theorem approximates_iff_forall_pure (Φ Ψ : QuantumChannel H K) (ε : ℝ) :
    Φ.Approximates Ψ ε ↔ ∀ v : UnitState H,
      1 - ε ≤ (Φ.map (Density.pure v)).fidelity (Ψ.map (Density.pure v)) := by
  refine ⟨fun h v => h _, fun h ρ => ?_⟩
  let e := ρ.spectralEnsemble
  have hi i : 1 - ε ≤ (Φ.map (e.state i)).fidelity (Ψ.map (e.state i)) :=
    h (UnitState.ofBasis ρ.eigenbasis i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hi i) (e.weight_nonneg i)
  rw [← Finset.sum_mul, e.sum_weight, one_mul] at hsum
  have hc := Density.sum_mul_fidelity_le_fidelity_mixture e.weight e.weight_nonneg e.sum_weight
    (fun i => Φ.map (e.state i)) (fun i => Ψ.map (e.state i))
  rw [← map_mixture, ← map_mixture] at hc
  change _ ≤ (Φ.map e.mix).fidelity (Ψ.map e.mix) at hc
  simpa only [e, Density.mix_spectralEnsemble] using hsum.trans hc

/-- A small mean squared error of a linear map leaves at least half of the input dimension
on which the squared error is uniformly bounded by twice that mean bound. -/
theorem exists_subspace_norm_sq_le_of_trace (T : H.state →ₗ[ℂ] K.state) {δ : ℝ} (hδ : 0 < δ)
    (ht : (LinearMap.trace ℂ H.state (T.adjoint ∘ₗ T)).re ≤ Module.finrank ℂ H.state * δ) :
    ∃ S : Submodule ℂ H.state, Module.finrank ℂ H.state ≤ 2 * Module.finrank ℂ S ∧
      ∀ x ∈ S, ‖T x‖ ^ 2 ≤ 2 * δ * ‖x‖ ^ 2 := by
  classical
  let A := T.adjoint ∘ₗ T
  have hA : A.IsPositive := T.isPositive_adjoint_comp_self
  let b := hA.isSymmetric.eigenvectorBasis rfl
  let μ := hA.isSymmetric.eigenvalues rfl
  have he i : A (b i) = (μ i : ℂ) • b i := hA.isSymmetric.apply_eigenvectorBasis rfl i
  have hμ i : 0 ≤ μ i := hA.nonneg_eigenvalues rfl i
  let bad := Finset.univ.filter (fun i => 2 * δ < μ i)
  let W := Submodule.span ℂ (↑(bad.image b) : Set H.state)
  have hsum : ∑ i, μ i ≤ Module.finrank ℂ H.state * δ :=
    (hA.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm.le.trans ht
  have hc : (bad.card : ℝ) * (2 * δ) ≤ (Module.finrank ℂ H.state : ℝ) * δ := by
    calc
      _ = ∑ _ ∈ bad, 2 * δ := by simp
      _ ≤ ∑ i ∈ bad, μ i := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2.le
      _ ≤ ∑ i, μ i := Finset.sum_le_univ_sum_of_nonneg hμ
      _ ≤ _ := hsum
  have hc' : 2 * bad.card ≤ Module.finrank ℂ H.state := by
    exact_mod_cast (show (2 : ℝ) * bad.card ≤ Module.finrank ℂ H.state by
      apply (le_of_mul_le_mul_right ?_ hδ)
      linarith only [hc])
  have hW : Module.finrank ℂ W ≤ bad.card :=
    (finrank_span_finset_le_card (R := ℂ) (bad.image b)).trans Finset.card_image_le
  refine ⟨Wᗮ, by have := W.finrank_add_finrank_orthogonal; lia, ?_⟩
  intro x hx
  have energy : ‖T x‖ ^ 2 = ∑ i, μ i * ‖inner ℂ (b i) x‖ ^ 2 := by
    rw [← Operator.re_inner_adjoint_comp_self T x]
    exact Operator.re_inner_apply_eq_sum_of_eigenbasis b A μ he x
  rw [energy, ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 2 * δ < μ i
  · have hb : b i ∈ W := Submodule.subset_span
      (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    rw [hx _ hb]
    simp
  · exact mul_le_mul_of_nonneg_right (le_of_not_gt hi) (sq_nonneg _)

/-- Difference between a dilation of a logical channel and transmission with a fixed environment. -/
def Dilation.embeddingError {Φ : QuantumChannel H H} (d : Φ.Dilation E) (e : UnitState E) :
    H.state →ₗ[ℂ] (H ⊗ E).state :=
  d.toHom.hom - (TensorProduct.mk ℂ H.state E.state).flip e.val

/-- Comparing purifications bounds the loss of root fidelity by half the squared vector error. -/
lemma Dilation.one_sub_half_error_le_fidelity {Φ : QuantumChannel H H} (d : Φ.Dilation E)
    (e : UnitState E) (v : UnitState H) :
    1 - ‖d.embeddingError e v.val‖ ^ 2 / 2 ≤
      (Φ.map (Density.pure v)).fidelity (Density.pure v) := by
  let u := v.map d.toHom
  let w := v.tensor e
  have h := Density.norm_inner_le_fidelity (Φ.map (Density.pure v)) (Density.pure v) u w
    (by rw [d.map_eq_partialTraceRight, Density.map_pure])
    (by rw [show w = v.tensor e from rfl, ← Density.tensor_pure, Density.partialTraceRight_tensor])
  have he := norm_sub_sq (𝕜 := ℂ) u.val w.val
  rw [u.norm_eq_one, w.norm_eq_one, RCLike.re_eq_complex_re] at he
  change 1 - ‖u.val - w.val‖ ^ 2 / 2 ≤ _
  linarith [Complex.re_le_norm (inner ℂ u.val w.val)]

/-- Expurgation of a decoded channel with small mean squared dilation error gives a subcode
of at least half the original dimension, uniformly good on all input densities. -/
theorem Dilation.exists_subcode_of_trace_embeddingError {Φ : QuantumChannel H H}
    (d : Φ.Dilation E) (e : UnitState E) {δ : ℝ} (hδ : 0 < δ)
    (hH : 0 < Module.finrank ℂ H.state)
    (ht : (LinearMap.trace ℂ H.state ((d.embeddingError e).adjoint ∘ₗ d.embeddingError e)).re ≤
      Module.finrank ℂ H.state * δ) :
    ∃ (k : ℕ) (Ψ : QuantumChannel (std k) (std k)), Module.finrank ℂ H.state ≤ 2 * k ∧
      Φ.Emulates Ψ ∧ Ψ.Approximates (id _) δ := by
  obtain ⟨S, hs, herr⟩ := exists_subspace_norm_sq_le_of_trace (d.embeddingError e) hδ ht
  let k := Module.finrank ℂ S
  let J : std k ⟶ H := ofLinearIsometry
    (S.subtypeₗᵢ.comp (stdOrthonormalBasis ℂ S).repr.symm.toLinearIsometry)
  have hk : Module.finrank ℂ (std k).state ≠ 0 := by rw [finrank_std]; dsimp [k]; lia
  obtain ⟨D, hD⟩ := exists_leftInverse_ofIsometry J (replacement H (Density.maximallyMixed _ hk))
  refine ⟨k, D.comp (Φ.comp (ofIsometry J)), hs, ⟨ofIsometry J, D, rfl⟩,
    (approximates_iff_forall_pure _ _ _).2 ?_⟩
  intro v
  let u := v.map J
  have hu : u.val ∈ S := ((stdOrthonormalBasis ℂ S).repr.symm v.val).property
  have hb := herr u.val hu
  rw [u.norm_eq_one, one_pow, mul_one] at hb
  have hf := d.one_sub_half_error_le_fidelity e u
  have hrec : D.map (Density.pure u) = Density.pure v := by
    rw [show Density.pure u = (ofIsometry J).map (Density.pure v) by
      rw [map_ofIsometry, Density.map_pure], ← map_comp, hD, map_id]
  rw [map_id, map_comp, map_comp, map_ofIsometry, Density.map_pure, ← hrec]
  exact (show 1 - δ ≤ _ by linarith only [hb, hf]).trans
    (D.fidelity_le_map (Φ.map (Density.pure u)) (Density.pure u))

private def groupReference (H E R : Qudit) : (H ⊗ E) ⊗ R ⟶ (H ⊗ R) ⊗ E :=
  ((β_ H E).hom ⊗ₘ 𝟙 R) ≫ (α_ E H R).hom ≫ (β_ E (H ⊗ R)).hom

private instance (H E R : Qudit) : IsIsometry (groupReference H E R) := by
  unfold groupReference
  infer_instance

private lemma map_vectorize {R S : Qudit} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ R.state) (f : R ⟶ S) :
    (f ⊗ₘ 𝟙 R).hom (∑ i, b i ⊗ₜ[ℂ] b i) = Superoperator.vectorize b f.hom := by
  simp [Superoperator.vectorize_apply]

/-- A successful maximally entangled transmission test supplies an environment vector
whose mean squared dilation error is at most twice the root infidelity. -/
theorem Dilation.exists_trace_embeddingError_le_of_entangled {Φ : QuantumChannel H H}
    (d : Φ.Dilation E) {ι : Type*} [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℂ H.state)
    (δ : ℝ) (hf : 1 - δ ≤
      ((Φ.tensor (id H)).map (Density.pure (UnitState.maximallyEntangled b))).fidelity
        (Density.pure (UnitState.maximallyEntangled b))) :
    ∃ e : UnitState E,
      (LinearMap.trace ℂ H.state ((d.embeddingError e).adjoint ∘ₗ d.embeddingError e)).re ≤
        Module.finrank ℂ H.state * (2 * δ) := by
  let ψ := UnitState.maximallyEntangled b
  let u := (ψ.map (d.symm.lift H)).swap
  let τ := (Φ.tensor (id H)).map (Density.pure ψ)
  have hu : (Density.pure u).partialTraceRight = τ := by
    rw [Density.partialTraceRight_pure_swap, d.symm.partialTraceLeft_pure_lift,
      d.complementary_symm]
  obtain ⟨i⟩ := (Density.pure u).partialTraceLeft.spectrum.nonempty
  let e₀ := UnitState.ofBasis (Density.pure u).partialTraceLeft.eigenbasis i
  have hp : (Density.pure (ψ.tensor e₀)).partialTraceRight = Density.pure ψ := by
    rw [← Density.tensor_pure, Density.partialTraceRight_tensor]
  obtain ⟨w, hw, hi⟩ := τ.exists_purification_inner_eq_fidelity (Density.pure ψ) u hu
    ((Density.pure ψ).finrank_range_le_of_purification (ψ.tensor e₀) hp)
  obtain ⟨e, rfl⟩ := w.exists_eq_tensor_of_partialTraceRight_eq_pure ψ hw
  refine ⟨e, ?_⟩
  have hdist := norm_sub_sq (𝕜 := ℂ) u.val (ψ.tensor e).val
  rw [hi, u.norm_eq_one, (ψ.tensor e).norm_eq_one, RCLike.re_eq_complex_re, Complex.ofReal_re]
    at hdist
  have hd : ‖u.val - (ψ.tensor e).val‖ ^ 2 ≤ 2 * δ := by linarith only [hdist, hf]
  let P := groupReference H E H
  let c : ℂ := (Real.sqrt (Fintype.card ι) : ℂ)⁻¹
  have hu' : u.val = P.hom (c • Superoperator.vectorize b d.toHom.hom) := by
    have heq : d.symm.lift H ≫ (β_ E (H ⊗ H)).hom = (d.toHom ⊗ₘ 𝟙 H) ≫ P := by
      simp only [Dilation.lift, Dilation.symm, P, groupReference, Category.assoc]
      rw [← Category.assoc (d.toHom ⊗ₘ 𝟙 H), tensorHom_comp_tensorHom, Category.id_comp]
    change (d.symm.lift H ≫ (β_ E (H ⊗ H)).hom).hom ψ.val = _
    rw [heq, hom_comp, LinearMap.comp_apply, UnitState.coe_maximallyEntangled, map_smul,
      map_vectorize]
  let J := (TensorProduct.mk ℂ H.state E.state).flip e.val
  have hw' : (ψ.tensor e).val = P.hom (c • Superoperator.vectorize b J) := by
    rw [UnitState.coe_tensor, UnitState.coe_maximallyEntangled, ← TensorProduct.smul_tmul',
      map_smul, Superoperator.vectorize_apply, TensorProduct.sum_tmul, map_sum]
    exact congrArg (c • ·) (Finset.sum_congr rfl fun i _ => rfl)
  rw [hu', hw', ← map_sub, norm_hom_of_isIsometry, ← smul_sub, ← map_sub, norm_smul,
    mul_pow] at hd
  change ‖c‖ ^ 2 * ‖Superoperator.vectorize b (d.embeddingError e)‖ ^ 2 ≤ 2 * δ at hd
  have hc : ‖c‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    simp [c, Complex.norm_real, Real.sq_sqrt]
  rw [hc, Superoperator.norm_vectorize_sq, ← div_eq_inv_mul] at hd
  rw [Module.finrank_eq_card_basis b.toBasis, mul_comm]
  exact (div_le_iff₀ (by positivity)).mp hd

/-- Root fidelity for transmission of half of a maximally entangled pair in a logical basis. -/
def maximallyEntangledFidelity (Φ : QuantumChannel H H) {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι ℂ H.state) : ℝ :=
  let τ := Density.pure (UnitState.maximallyEntangled b)
  ((Φ.tensor (id H)).map τ).fidelity τ

/-- Entanglement root fidelity at least `1 - ε` gives a subcode of at least half the
logical dimension with worst-case root fidelity at least `1 - 2 * ε`. -/
theorem exists_subcode_of_maximallyEntangledFidelity (Φ : QuantumChannel H H)
    {ι : Type*} [Fintype ι] [Nonempty ι] (b : OrthonormalBasis ι ℂ H.state)
    {ε : ℝ} (hε : 0 < ε) (hf : 1 - ε ≤ Φ.maximallyEntangledFidelity b) :
    ∃ (k : ℕ) (Ψ : QuantumChannel (std k) (std k)), Module.finrank ℂ H.state ≤ 2 * k ∧
      Φ.Emulates Ψ ∧ Ψ.Approximates (id _) (2 * ε) := by
  obtain ⟨e, he⟩ := Φ.dilation.exists_trace_embeddingError_le_of_entangled b ε hf
  exact Φ.dilation.exists_subcode_of_trace_embeddingError e (by positivity)
    (by rw [Module.finrank_eq_card_basis b.toBasis]; exact Fintype.card_pos) he

/-- Arbitrarily long codes of the specified rate transmitting half of a maximally entangled pair
with root fidelity approaching one. The logical dimension `d + 1` is always positive. -/
def AchievesEntanglementRate (Φ : QuantumChannel H K) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ (n d : ℕ) (Ψ : QuantumChannel (std (d + 1)) (std (d + 1))),
      N ≤ n ∧ (Φ.tensorPower n).Emulates Ψ ∧ R * (n + 1 : ℝ) ≤ Real.logb 2 (d + 1 : ℝ) ∧
        1 - ε ≤ Ψ.maximallyEntangledFidelity (ZBasis (d + 1))

/-- Arbitrarily long entanglement transmission codes give worst-case transmission at every
strictly smaller rate. Expurgation costs at most one logical qubit per block. -/
theorem AchievesEntanglementRate.achievesRate {Φ : QuantumChannel H K} {R r : ℝ}
    (hc : Φ.AchievesEntanglementRate R) (hr : r < R) : Φ.AchievesRate r := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (R - r))
  obtain ⟨n, d, Ψ, hn, he, hR, hf⟩ := hc (ε / 2) (by positivity) N
  obtain ⟨k, Γ, hk, hΓ, ha⟩ := Ψ.exists_subcode_of_maximallyEntangledFidelity (ZBasis (d + 1))
    (by positivity : 0 < ε / 2) hf
  rw [finrank_std] at hk
  have hk' : 0 < k := by lia
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (d + 1 : ℝ)) (by exact_mod_cast hk : (d + 1 : ℝ) ≤ 2 * (k : ℝ))
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)] at hlog
  have hlen : 1 / (R - r) < (n + 1 : ℝ) :=
    hN.trans (by exact_mod_cast Nat.lt_succ_of_le hn)
  have hgap := (div_lt_iff₀ (sub_pos.mpr hr)).mp hlen
  refine ⟨n, k, Γ, he.trans hΓ, by linarith only [hgap, hR, hlog], ?_⟩
  simpa only [mul_div_cancel₀ ε (by norm_num : (2 : ℝ) ≠ 0)] using ha

/-- Whenever the given input has nonpositive coherent information, its single-use rate is
achieved by the one-dimensional logical code, for every physical channel. -/
theorem achievesRate_coherentInfo_of_nonpos (Φ : QuantumChannel H K) (ρ : Density H)
    (h : Φ.coherentInfo ρ ≤ 0) : Φ.AchievesRate (Φ.coherentInfo ρ / Real.log 2) := by
  obtain ⟨i⟩ := ρ.spectrum.nonempty
  exact (Φ.achievesRate_zero (by have := i.isLt; lia)).mono (div_nonpos_of_nonpos_of_nonneg h
    (by positivity))

/-- Entanglement transmission at rates approaching the positive coherent information of each
block suffices for the regularized lower bound under the operational worst-case error test. -/
theorem regularizedCoherentInfo_le_quantumCapacity_of_entanglement_codes (Φ : QuantumChannel H K)
    (hc : ∀ n (ρ : Density (Qudit.tensorPower H n)) (R : ℝ), 0 < R →
      R < (Φ.tensorPower n).coherentInfo ρ / Real.log 2 →
        (Φ.tensorPower n).AchievesEntanglementRate R) :
    Φ.regularizedCoherentInfo ≤ Φ.quantumCapacity := by
  apply Φ.regularizedCoherentInfo_le_quantumCapacity_of_block_bound
  intro n ρ
  apply le_of_forall_lt_imp_le_of_dense
  intro r hr
  by_cases h : 0 < r
  · obtain ⟨R, hrR, hR⟩ := exists_between hr
    exact le_csSup (bddAbove_achievesRate _) ((hc n ρ R (h.trans hrR) hR).achievesRate hrR)
  · exact (le_of_not_gt h).trans
      ((Φ.tensorPower n).isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..))

end Qudit.QuantumChannel
