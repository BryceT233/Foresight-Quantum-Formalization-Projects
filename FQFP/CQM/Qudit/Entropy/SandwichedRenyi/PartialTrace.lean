/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the sandwiched divergence under a partial trace.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/DPI.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi
public import FQFP.CQM.Qudit.State.Composite.Support
public import FQFP.Analysis.Complex.SpectralInterpolation

/-!
# Partial trace and the sandwiched Rényi divergence

Let `τ = Tr_K σ`. In the eigenbases of the input and output sandwiches, take matrix
entries of `(τ^(-z/2) ⊗ 1) σ^(z/2)`, extending each spectral power by zero on its kernel.
At `Re z = 0` each column has squared norm at most one by Parseval. At `Re z = 1`,
the marginal identity for `τ` bounds each output row after summing over the environment.
At `z = 1 - 1/α`, support inclusion lets the input sandwich recover the source state.
Three-lines interpolation of these entries, weighted by the sandwich eigenvalues, gives
contraction of the trace functional.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Complex.HadamardThreeLines
open scoped TensorProduct BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]

private def diag (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) : Operator H :=
  ∑ i, d i • Operator.outer (b i) (b i)

private lemma diag_basis (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) (i : ι) :
    diag b d (b i) = d i • b i := by
  classical
  simp [diag, Operator.outer_apply, b.inner_eq_ite]

private lemma adj_diag (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) :
    (diag b d).adjoint = diag b (fun i => star (d i)) := by
  simp only [diag, map_sum, map_smulₛₗ, Operator.adjoint_outer, Complex.star_def]

private lemma inner_diag (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) (u v : H.state) :
    inner ℂ u (diag b d v) = ∑ i, d i * (inner ℂ (b i) v * inner ℂ u (b i)) := by
  simp only [diag, LinearMap.sum_apply, LinearMap.smul_apply, Operator.outer_apply,
    inner_sum, inner_smul_right]

private lemma coord_diag (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) (v : H.state) (i : ι) :
    inner ℂ (b i) (diag b d v) = d i * inner ℂ (b i) v := by
  rw [← LinearMap.adjoint_inner_left, adj_diag, diag_basis, inner_smul_left]
  simp

private lemma norm_diag (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ) (v : H.state) :
    ‖diag b d v‖ ^ 2 = ∑ i, ‖d i‖ ^ 2 * ‖inner ℂ (b i) v‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right (diag b d v)]
  simp only [coord_diag, norm_mul, mul_pow]

private lemma norm_diag_le (b : OrthonormalBasis ι ℂ H.state) (d : ι → ℂ)
    (hd : ∀ i, ‖d i‖ ^ 2 ≤ 1) (v : H.state) : ‖diag b d v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_diag, ← b.sum_sq_norm_inner_right v]
  exact Finset.sum_le_sum fun i _ => mul_le_of_le_one_left (sq_nonneg _) (hd i)

private lemma diag_tensor (b : OrthonormalBasis ι ℂ H.state) (e : OrthonormalBasis κ ℂ K.state)
    (d : ι → ℂ) : Operator.tensor (diag b d) (1 : Operator K) =
      diag (b.tensorProduct e) (fun a => d a.1) := by
  apply (b.tensorProduct e).toBasis.ext
  rintro ⟨i, k⟩
  change Operator.tensor _ _ ((b.tensorProduct e) (i, k)) = diag _ _ ((b.tensorProduct e) (i, k))
  rw [diag_basis, OrthonormalBasis.tensorProduct_apply, Operator.tensor_apply, diag_basis,
    one_apply_eq_self, TensorProduct.smul_tmul']

private def phase (σ : Density H) (z : ℂ) : Operator H :=
  diag σ.eigenbasis (fun i => spectralFactor (σ.eigenvalue i) z)

private lemma phase_real (σ : Density H) {t : ℝ} (ht : t ≠ 0) :
    phase σ t = σ.spectralMap (fun r => r ^ (t / 2)) := by
  simp only [phase, diag, spectralMap, spectralFactor_ofReal (σ.eigenvalue_nonneg _) ht]

private lemma phase_one (σ : Density H) {z : ℂ} (hz : z.re = 1) (v : H.state) :
    ‖(phase σ z).adjoint v‖ ^ 2 = (inner ℂ v (σ.op v)).re := by
  rw [phase, adj_diag, norm_diag,
    Operator.re_inner_apply_eq_sum_of_eigenbasis σ.eigenbasis _ _ σ.apply_eigenbasis]
  simp only [norm_star, norm_sq_spectralFactor_of_re_ne_zero (σ.eigenvalue_nonneg _)
    (hz.trans_ne one_ne_zero), hz, Real.rpow_one]

private lemma phase_neg_one (σ : Density H) {z : ℂ} (hz : z.re = 1) (v : H.state) :
    (inner ℂ ((phase σ (-z)).adjoint v) (σ.op ((phase σ (-z)).adjoint v))).re ≤ ‖v‖ ^ 2 := by
  rw [Operator.re_inner_apply_eq_sum_of_eigenbasis σ.eigenbasis _ _ σ.apply_eigenbasis,
    ← σ.eigenbasis.sum_sq_norm_inner_right v]
  simp only [phase, adj_diag, coord_diag, norm_mul, norm_star, mul_pow, ← mul_assoc,
    norm_sq_spectralFactor (σ.eigenvalue_nonneg _), Complex.neg_re, hz, Real.rpow_neg_one]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : σ.eigenvalue i = 0 <;> simp [h]

private lemma undo_sandwich (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ)
    {s : ℝ} (hs : s ≠ 0) (v : H.state) :
    (inner ℂ ((phase σ s).adjoint v)
      (ρ.renyiSandwich σ s ((phase σ s).adjoint v))).re = (inner ℂ v (ρ.op v)).re := by
  let P := σ.spectralMap (fun r => r ^ (s / 2))
  let N := σ.spectralMap (fun r => r ^ (-s / 2))
  have hc : ρ.op ∘ₗ (N ∘ₗ P) = ρ.op := by
    apply σ.eigenbasis.toBasis.ext
    intro i
    change ρ.op (N (P (σ.eigenbasis i))) = ρ.op (σ.eigenbasis i)
    simp only [N, P, spectralMap_apply_eigenbasis, map_smul, smul_smul]
    by_cases hi : σ.eigenvalue i = 0
    · have hzero : ρ.op (σ.eigenbasis i) = 0 := h (by
        change σ.op (σ.eigenbasis i) = 0
        simp [σ.apply_eigenbasis, hi])
      simp only [hzero, smul_zero]
    · rw [neg_div, Real.rpow_neg (σ.eigenvalue_nonneg i), ← Complex.ofReal_mul,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos ((σ.eigenvalue_nonneg i).lt_of_ne' hi) _).ne',
        Complex.ofReal_one, one_smul]
  have hc' := congrArg LinearMap.adjoint hc
  simp only [LinearMap.adjoint_comp, N, P, adjoint_spectralMap, ρ.positive.adjoint_eq] at hc'
  rw [phase_real σ hs, adjoint_spectralMap, renyiSandwich, adjoint_spectralMap]
  change (inner ℂ (P v) (N (ρ.op (N (P v))))).re = _
  rw [show ρ.op (N (P v)) = ρ.op v from DFunLike.congr_fun hc v,
    ← LinearMap.adjoint_inner_right P, show P.adjoint = P from σ.adjoint_spectralMap _,
    show P (N (ρ.op v)) = ρ.op v from DFunLike.congr_fun hc' v]

private def transfer (σ : Density (H ⊗ K)) (z : ℂ) (c : H.state) (e : K.state)
    (v : (H ⊗ K).state) : ℂ :=
  inner ℂ (c ⊗ₜ[ℂ] e) (Operator.tensor (phase σ.partialTraceRight (-z)) 1 (phase σ z v))

private lemma transfer_adjoint (σ : Density (H ⊗ K)) (z : ℂ) (c : H.state) (e : K.state)
    (v : (H ⊗ K).state) :
    transfer σ z c e v = inner ℂ ((phase σ z).adjoint
      (((phase σ.partialTraceRight (-z)).adjoint c) ⊗ₜ[ℂ] e)) v := by
  unfold transfer
  rw [← LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_left, Operator.adjoint_tensor,
    LinearMap.adjoint_one, Operator.tensor_apply, one_apply_eq_self]

private lemma transfer_entire (σ : Density (H ⊗ K)) (c : H.state) (e : K.state)
    (v : (H ⊗ K).state) : StripBoundedEntire (fun z => transfer σ z c e v) := by
  let b := stdOrthonormalBasis ℂ K.state
  simp only [transfer, phase, diag_tensor _ b, inner_diag (H := H ⊗ K)]
  apply StripBoundedEntire.sum
  intro a
  apply StripBoundedEntire.mul
  · simpa using StripBoundedEntire.spectralFactor_affine (σ.partialTraceRight.eigenvalue a.1) 0 (-1)
  · apply StripBoundedEntire.mul _ (.const _)
    apply StripBoundedEntire.sum
    intro i
    apply StripBoundedEntire.mul _ (.const _)
    simpa using StripBoundedEntire.spectralFactor_affine (σ.eigenvalue i) 0 1

private lemma transfer_zero_sum (σ : Density (H ⊗ K)) {z : ℂ} (hz : z.re = 0)
    (c : OrthonormalBasis ι ℂ H.state) (e : OrthonormalBasis κ ℂ K.state)
    (v : (H ⊗ K).state) :
    ∑ j, ∑ k, ‖transfer σ z (c j) (e k) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have he (w : (H ⊗ K).state) : ∑ j, ∑ k, ‖inner ℂ (c j ⊗ₜ[ℂ] e k) w‖ ^ 2 = ‖w‖ ^ 2 := by
    simpa only [Fintype.sum_prod_type, OrthonormalBasis.tensorProduct_apply] using
      (c.tensorProduct e).sum_sq_norm_inner_right w
  unfold transfer
  rw [he, phase, diag_tensor _ e]
  refine (norm_diag_le (H := H ⊗ K) (σ.partialTraceRight.eigenbasis.tensorProduct e) _
    (fun i => norm_sq_spectralFactor_le_one (σ.partialTraceRight.eigenvalue_nonneg i.1)
      (by simp [hz])) (phase σ z v)).trans ?_
  exact norm_diag_le σ.eigenbasis _ (fun i =>
    norm_sq_spectralFactor_le_one (σ.eigenvalue_nonneg i) hz) v

private lemma transfer_one_sum (σ : Density (H ⊗ K)) {z : ℂ} (hz : z.re = 1)
    (c : H.state) (e : OrthonormalBasis κ ℂ K.state)
    (b : OrthonormalBasis ι ℂ (H ⊗ K).state) :
    ∑ k, ∑ i, ‖transfer σ z c (e k) (b i)‖ ^ 2 ≤ ‖c‖ ^ 2 := by
  simp only [transfer_adjoint, b.sum_sq_norm_inner_left, phase_one σ hz]
  rw [← Complex.re_sum, ← Operator.inner_partialTraceRight e σ.op]
  exact phase_neg_one σ.partialTraceRight hz c

private lemma transfer_interior_sum (ρ σ : Density (H ⊗ K)) (h : ρ.AbsolutelyContinuous σ)
    {s : ℝ} (hs : s ≠ 0) (c : H.state) (e : OrthonormalBasis κ ℂ K.state)
    (b : OrthonormalBasis ι ℂ (H ⊗ K).state) (x : ι → ℝ)
    (hx : ∀ i, ρ.renyiSandwich σ s (b i) = (x i : ℂ) • b i) :
    ∑ k, ∑ i, x i * ‖transfer σ s c (e k) (b i)‖ ^ 2 =
      (inner ℂ c (ρ.partialTraceRight.renyiSandwich σ.partialTraceRight s c)).re := by
  simp only [transfer_adjoint]
  conv_lhs => enter [2, k, 2, i, 2, 1]; rw [norm_inner_symm]
  simp only [← Operator.re_inner_apply_eq_sum_of_eigenbasis b _ x hx, undo_sandwich ρ σ h hs]
  rw [← Complex.re_sum, ← Operator.inner_partialTraceRight e ρ.op, ← Complex.ofReal_neg,
    phase_real _ (neg_ne_zero.mpr hs), renyiSandwich, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.adjoint_inner_left]
  rfl

/-- The sandwiched trace functional contracts under a right partial trace on its finite domain. -/
theorem sandwichedTraceFunctional_partialTraceRight_le (ρ σ : Density (H ⊗ K))
    {α : ℝ} (hα : 1 < α) (h : ρ.AbsolutelyContinuous σ) :
    ρ.partialTraceRight.sandwichedTraceFunctional σ.partialTraceRight α ≤
      ρ.sandwichedTraceFunctional σ α := by
  let s := 1 - α⁻¹
  let X := ρ.renyiSandwich_positive σ s
  let Y := ρ.partialTraceRight.renyiSandwich_positive σ.partialTraceRight s
  let b := X.isSymmetric.eigenvectorBasis rfl
  let c := Y.isSymmetric.eigenvectorBasis rfl
  let e := stdOrthonormalBasis ℂ K.state
  let x := X.isSymmetric.eigenvalues rfl
  let y := Y.isSymmetric.eigenvalues rfl
  apply sum_rpow_le_of_strip_transfer hα x y (X.nonneg_eigenvalues rfl)
    (Y.nonneg_eigenvalues rfl) (fun i j k z => transfer σ z (c j) (e k) (b i))
    (fun i j k => transfer_entire σ (c j) (e k) (b i))
  · intro z hz i
    simpa only [b.norm_eq_one, one_pow] using transfer_zero_sum σ hz c e (b i)
  · intro z hz j
    simpa only [c.norm_eq_one, one_pow] using transfer_one_sum σ hz (c j) e b
  · intro j
    have hs : 0 < s := sub_pos.mpr (inv_lt_one_of_one_lt₀ hα)
    rw [transfer_interior_sum ρ σ h hs.ne' (c j) e b x (X.isSymmetric.apply_eigenvectorBasis rfl)]
    have hj : ρ.partialTraceRight.renyiSandwich σ.partialTraceRight s (c j) =
        (y j : ℂ) • c j := Y.isSymmetric.apply_eigenvectorBasis rfl j
    rw [hj, inner_smul_right, c.inner_eq_one, mul_one, Complex.ofReal_re]

/-- Discarding the right subsystem decreases sandwiched Rényi relative entropy for every
order strictly greater than one, including when the input divergence is infinite. -/
theorem sandwichedRenyiRelativeEntropy_partialTraceRight_le (ρ σ : Density (H ⊗ K))
    (α : Set.Ioi (1 : ℝ)) : ρ.partialTraceRight.sandwichedRenyiRelativeEntropy
      σ.partialTraceRight α ≤ ρ.sandwichedRenyiRelativeEntropy σ α := by
  by_cases h : ρ.AbsolutelyContinuous σ
  · simp only [sandwichedRenyiRelativeEntropy, h, h.partialTraceRight, reduceIte]
    have hq := sandwichedTraceFunctional_partialTraceRight_le ρ σ α.property h
    rcases (ρ.partialTraceRight.sandwichedTraceFunctional_nonneg σ.partialTraceRight α).eq_or_lt
        with hz | hp
    · simp [← hz]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Real.log_le_log hp hq)
      (sub_nonneg.mpr α.property.le))
  · rw [(sandwichedRenyiRelativeEntropy_eq_top_iff ρ σ α).mpr h]
    exact le_top

end

end Qudit.Density
