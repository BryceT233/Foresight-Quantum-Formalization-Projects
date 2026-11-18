/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Order.AtTopBotIxx

/-!
# The right limit of sandwiched Rényi relative entropy at one

The derivative of the trace functional has two contributions. Differentiating the trace
of the sandwich gives the negative reference log expectation. The varying outer power
contributes the source log expectation, including at zero eigenvalues.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

-- Extend the spectral multiplier by one on the kernel so it varies smoothly at order one.
private def weight (σ : Density H) (a : ℝ) : Operator H :=
  σ.spectralMap (fun x => Real.exp (Real.log x * (-(1 - a⁻¹) / 2)))

private lemma weight_one (σ : Density H) : weight σ 1 = 1 := by
  simp [weight, spectralMap_const]

private lemma sandwich_eq_weight (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) (a : ℝ) :
    ρ.renyiSandwich σ (1 - a⁻¹) = weight σ a ∘ₗ ρ.op ∘ₗ weight σ a := by
  let N := σ.spectralMap (fun x => x ^ (-(1 - a⁻¹) / 2))
  have hr : ρ.op ∘ₗ N = ρ.op ∘ₗ weight σ a := by
    apply σ.eigenbasis.toBasis.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, N, weight,
      spectralMap_apply_eigenbasis, map_smul]
    by_cases hz : σ.eigenvalue i = 0
    · have hi := (absolutelyContinuous_iff_of_right_eigenbasis ρ σ σ.eigenbasis _
        σ.apply_eigenbasis).mp h i hz
      rw [hi, smul_zero, smul_zero]
    · rw [Real.rpow_def_of_pos ((σ.eigenvalue_nonneg i).lt_of_ne' hz)]
  have hl := congrArg LinearMap.adjoint hr
  simp only [LinearMap.adjoint_comp, ρ.positive.adjoint_eq, N, weight, adjoint_spectralMap] at hl
  change N ∘ₗ ρ.op ∘ₗ N.adjoint = _
  rw [show N.adjoint = N from σ.adjoint_spectralMap _, hr, ← LinearMap.comp_assoc, hl,
    LinearMap.comp_assoc]
  rfl

private lemma sandwich_one (ρ σ : Density H) :
    ρ.renyiSandwich σ (1 - (1 : ℝ)⁻¹) = ρ.op := by
  simp only [renyiSandwich, inv_one, sub_self, neg_zero, zero_div, Real.rpow_zero,
    spectralMap_const, Complex.ofReal_one, one_smul, LinearMap.adjoint_one]
  rfl

/-- At order one the trace functional is the trace of the source state. -/
lemma sandwichedTraceFunctional_one (ρ σ : Density H) : ρ.sandwichedTraceFunctional σ 1 = 1 := by
  rw [sandwichedTraceFunctional_eq_sum_of_eigenbasis _ _ 1 ρ.eigenbasis ρ.eigenvalue]
  · simpa only [Real.rpow_one] using ρ.sum_eigenvalue
  · simpa only [sandwich_one] using ρ.apply_eigenbasis

private lemma tendsto_weight_apply {ι : Type*} {l : Filter ι} {a : ι → ℝ} {v : ι → H.state}
    {u : H.state} (σ : Density H) (ha : Tendsto a l (𝓝 1)) (hv : Tendsto v l (𝓝 u)) :
    Tendsto (fun i => weight σ (a i) (v i)) l (𝓝 u) := by
  have he : Tendsto (fun i => -(1 - (a i)⁻¹) / 2) l (𝓝 (-(1 - (1 : ℝ)⁻¹) / 2)) :=
    ((tendsto_const_nhds.sub (ha.inv₀ one_ne_zero)).neg).div_const _
  have hw : Tendsto (fun i => weight σ (a i) (v i)) l (𝓝 (weight σ 1 u)) := by
    simp only [weight, spectralMap, LinearMap.sum_apply, LinearMap.smul_apply]
    apply tendsto_finsetSum
    intro j _
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul he))).smul
        ((Operator.outer (σ.eigenbasis j) (σ.eigenbasis j)).continuous_of_finiteDimensional
          |>.continuousAt.tendsto.comp hv)
  simpa only [weight_one, Module.End.one_apply] using hw

private lemma tendsto_sandwich_apply {ι : Type*} {l : Filter ι} {a : ι → ℝ} {v : ι → H.state}
    {u : H.state} (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ)
    (ha : Tendsto a l (𝓝 1)) (hv : Tendsto v l (𝓝 u)) :
    Tendsto (fun i => ρ.renyiSandwich σ (1 - (a i)⁻¹) (v i)) l (𝓝 (ρ.op u)) := by
  simp only [sandwich_eq_weight ρ σ h, LinearMap.comp_apply]
  exact tendsto_weight_apply σ ha (ρ.op.continuous_of_finiteDimensional.continuousAt.tendsto.comp
    (tendsto_weight_apply σ ha hv))

private lemma hasDerivAt_trace_sandwich (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) :
    HasDerivAt (fun a : ℝ => (ρ.renyiSandwich σ (1 - a⁻¹)).trace.re)
      (-ρ.expectation σ.logOp) 1 := by
  let d i := (inner ℂ (σ.eigenbasis i) (ρ.op (σ.eigenbasis i))).re
  have ht (a : ℝ) : (ρ.renyiSandwich σ (1 - a⁻¹)).trace.re =
      ∑ i, Real.exp (Real.log (σ.eigenvalue i) * (a⁻¹ - 1)) * d i := by
    rw [sandwich_eq_weight ρ σ h, Operator.trace, LinearMap.trace_eq_sum_inner _ σ.eigenbasis,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_left (weight σ a)]
    simp only [weight, adjoint_spectralMap,
      spectralMap_apply_eigenbasis, map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, d]
    ring_nf
  simp only [ht, ρ.expectation_eq_sum_of_diagonal σ.eigenbasis σ.logOp
    (fun i => Real.log (σ.eigenvalue i)) (fun i => σ.logOp_apply_of_eigenvector
      (σ.apply_eigenbasis i)), ← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  have hi := (((hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0)).sub_const 1).const_mul
    (Real.log (σ.eigenvalue i))).exp.mul_const (d i)
  simpa [d] using hi

-- The two tangent bounds have the same limit even when the varying base tends to zero.
private lemma rpow_slope_bounds {x a : ℝ} (hx : 0 ≤ x) (ha : 1 < a) :
    x * Real.log x ≤ (x ^ a - x) / (a - 1) ∧
      (x ^ a - x) / (a - 1) ≤ x ^ a * Real.log (x ^ a) / a := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [Real.zero_rpow (zero_lt_one.trans ha).ne']
  have hy := Real.rpow_pos_of_pos hx a
  have hlo := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hup := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hy.ne' hx.ne', Real.log_rpow hx] at hlo
  rw [Real.log_div hx.ne' hy.ne', Real.log_rpow hx] at hup
  rw [Real.log_rpow hx, show x ^ a * (a * Real.log x) / a = x ^ a * Real.log x by
    field_simp [(zero_lt_one.trans ha).ne'], le_div_iff₀ (sub_pos.mpr ha),
    div_le_iff₀ (sub_pos.mpr ha)]
  constructor
  · linarith only [(le_div_iff₀ hx).mp (le_sub_iff_add_le.mp hlo)]
  · linarith only [(le_div_iff₀ hy).mp (le_sub_iff_add_le.mp hup)]

private lemma tendsto_rpow_slope {ι : Type*} {l : Filter ι} {x a : ι → ℝ} {z : ℝ}
    (hx : Tendsto x l (𝓝 z)) (ha : Tendsto a l (𝓝 1)) (hn : ∀ i, 0 ≤ x i)
    (hp : ∀ᶠ i in l, 1 < a i) :
    Tendsto (fun i => (x i ^ a i - x i) / (a i - 1)) l (𝓝 (z * Real.log z)) := by
  have hpow : Tendsto (fun i => x i ^ a i) l (𝓝 z) := by
    simpa only [Real.rpow_one] using hx.rpow ha (.inr zero_lt_one)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((Real.continuous_mul_log.tendsto z).comp hx)
  · simpa only [div_one] using (((Real.continuous_mul_log.tendsto z).comp hpow).div ha one_ne_zero)
  · exact hp.mono fun i hi => (rpow_slope_bounds (hn i) hi).1
  · exact hp.mono fun i hi => (rpow_slope_bounds (hn i) hi).2

-- Extract convergent eigenframes rather than differentiating individual eigenvectors.
private lemma tendsto_trace_power_correction (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) :
    Tendsto (fun a : ℝ => (ρ.sandwichedTraceFunctional σ a -
      (ρ.renyiSandwich σ (1 - a⁻¹)).trace.re) / (a - 1)) (𝓝[>] 1)
      (𝓝 (ρ.expectation ρ.logOp)) := by
  let X (a : ℝ) := ρ.renyiSandwich_positive σ (1 - a⁻¹)
  let b (a : ℝ) := (X a).isSymmetric.eigenvectorBasis rfl
  let x (a : ℝ) := (X a).isSymmetric.eigenvalues rfl
  have he (a i) : ρ.renyiSandwich σ (1 - a⁻¹) (b a i) = (x a i : ℂ) • b a i :=
    (X a).isSymmetric.apply_eigenvectorBasis rfl i
  have ht (a : ℝ) : (ρ.sandwichedTraceFunctional σ a -
      (ρ.renyiSandwich σ (1 - a⁻¹)).trace.re) / (a - 1) =
      ∑ i, (x a i ^ a - x a i) / (a - 1) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    exact congrArg (fun t => (ρ.sandwichedTraceFunctional σ a - t) / (a - 1))
      ((X a).isSymmetric.re_trace_eq_sum_eigenvalues rfl)
  simp only [ht]
  apply tendsto_of_subseq_tendsto
  intro a ha
  obtain ⟨v, hv, φ, hφ, hvφ⟩ := (Qudit.isCompact_orthonormal H _).tendsto_subseq
    (x := fun n i => b (a n) i) (fun n => (b (a n)).orthonormal)
  refine ⟨φ, ?_⟩
  let c n := a (φ n)
  have hc : Tendsto c atTop (𝓝[>] 1) := ha.comp hφ.tendsto_atTop
  have hc' := hc.mono_right nhdsWithin_le_nhds
  have hb (i) : Tendsto (fun n => b (c n) i) atTop (𝓝 (v i)) := tendsto_pi_nhds.mp hvφ i
  let y i := (inner ℂ (v i) (ρ.op (v i))).re
  have hlim (i) : Tendsto (fun n => x (c n) i) atTop (𝓝 (y i)) := by
    have hd := Complex.continuous_re.continuousAt.tendsto.comp
      ((hb i).inner (tendsto_sandwich_apply ρ σ h hc' (hb i)))
    simpa only [Function.comp_def, he, inner_smul_right, OrthonormalBasis.inner_eq_one,
      mul_one, Complex.ofReal_re] using hd
  have hy (i) : ρ.op (v i) = (y i : ℂ) • v i :=
    tendsto_nhds_unique_of_eventuallyEq (tendsto_sandwich_apply ρ σ h hc' (hb i))
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim i)).smul (hb i))
      (Eventually.of_forall fun n => he (c n) i)
  let B := OrthonormalBasis.mk hv
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  have hB (i) : ρ.op (B i) = (y i : ℂ) • B i := by
    simpa only [B, OrthonormalBasis.coe_mk] using hy i
  rw [logOp, expectation_spectralMap_self,
    ρ.sum_eigenvalue_eq_of_eigenbasis B y hB (fun r => r * Real.log r)]
  exact tendsto_finsetSum _ fun i _ => tendsto_rpow_slope (hlim i) hc'
    (fun n => (X (c n)).nonneg_eigenvalues rfl i) (hc.eventually self_mem_nhdsWithin)

/-- The right derivative of the sandwiched trace functional at one is the Umegaki
trace formula whenever the reference support contains the source support. -/
theorem hasDerivWithinAt_sandwichedTraceFunctional_one (ρ σ : Density H)
    (h : ρ.AbsolutelyContinuous σ) :
    HasDerivWithinAt (ρ.sandwichedTraceFunctional σ) (ρ.relativeEntropyReal σ) (Set.Ioi 1) 1 := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (1 : ℝ)) (lt_irrefl _)).mp
    (hasDerivAt_trace_sandwich ρ σ h).hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (1 : ℝ)) (lt_irrefl _),
    relativeEntropyReal, expectation_sub]
  simp only [slope_fun_def_field, sandwich_one, ρ.trace_one, Complex.one_re,
    sandwichedTraceFunctional_one] at ht ⊢
  have hs := (tendsto_trace_power_correction ρ σ h).add ht
  rw [sub_eq_add_neg (ρ.expectation ρ.logOp)]
  simpa only [← add_div, sub_add_sub_cancel] using hs

/-- As the order decreases to one, sandwiched Rényi relative entropy converges to
Umegaki relative entropy in the extended nonnegative reals. The order ranges over
`Set.Ioi 1`, whose bottom filter represents approach to one from the right. -/
theorem tendsto_sandwichedRenyiRelativeEntropy_one (ρ σ : Density H) :
    Tendsto (ρ.sandwichedRenyiRelativeEntropy σ) atBot (𝓝 (ρ.relativeEntropy σ)) := by
  classical
  change Tendsto (fun a => ρ.sandwichedRenyiRelativeEntropy σ a) _ _
  by_cases h : ρ.AbsolutelyContinuous σ
  · simp only [sandwichedRenyiRelativeEntropy, relativeEntropy, h, reduceIte]
    apply ENNReal.tendsto_ofReal
    apply (tendsto_comp_coe_Ioi_atBot (a := (1 : ℝ)) (f := fun a =>
      Real.log (ρ.sandwichedTraceFunctional σ a) / (a - 1))).mpr
    have hd := (ρ.hasDerivWithinAt_sandwichedTraceFunctional_one σ h).log
      ((ρ.sandwichedTraceFunctional_one σ).trans_ne one_ne_zero)
    have hl := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (1 : ℝ)) (lt_irrefl _)).mp hd
    simpa only [slope_fun_def_field, sandwichedTraceFunctional_one, Real.log_one, sub_zero,
      div_one] using hl
  · simp only [sandwichedRenyiRelativeEntropy, relativeEntropy, h, reduceIte]
    exact tendsto_const_nhds

end

end Qudit.Density
