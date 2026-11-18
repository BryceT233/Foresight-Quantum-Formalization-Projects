/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.Monotonicity
public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.Tensor
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Max-relative entropy and the infinite-order limit

The normalized trace power of a positive operator lies between its operator norm and
that norm times the dimension to the reciprocal order. The sandwich converges in
operator norm even for a singular reference, since its negative powers vanish on the kernel.
Taking the limit in the channel data processing inequality yields the same inequality at infinity.
Tensor additivity likewise passes to the limit by continuity of addition in `ENNReal`.
-/

@[expose] public section

open CategoryTheory DaggerCategory Filter
open scoped Topology BigOperators

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

open Classical in
/-- Max-relative entropy in nats. On the reference support it is the logarithm of
the operator norm of the sandwich by the inverse square root of the reference. -/
def maxRelativeEntropy (ρ σ : Density H) : ENNReal :=
  if ρ.AbsolutelyContinuous σ then
    ENNReal.ofReal (Real.log ‖LinearMap.toContinuousLinearMap (ρ.renyiSandwich σ 1)‖)
  else ⊤

/-- Max-relative entropy is infinite precisely when support inclusion fails. -/
lemma maxRelativeEntropy_eq_top_iff (ρ σ : Density H) :
    ρ.maxRelativeEntropy σ = ⊤ ↔ ¬ρ.AbsolutelyContinuous σ := by
  by_cases h : ρ.AbsolutelyContinuous σ <;> simp [maxRelativeEntropy, h]

private lemma tendsto_inv_order :
    Tendsto (fun a : Set.Ioi (1 : ℝ) => a.val⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_Ioi_atTop.mp tendsto_id)

private lemma tendsto_sandwich_norm_atTop (ρ σ : Density H) :
    Tendsto (fun a : Set.Ioi (1 : ℝ) =>
      ‖LinearMap.toContinuousLinearMap (ρ.renyiSandwich σ (1 - a.val⁻¹))‖) atTop
      (𝓝 ‖LinearMap.toContinuousLinearMap (ρ.renyiSandwich σ 1)‖) := by
  let W (s : ℝ) := LinearMap.toContinuousLinearMap (σ.spectralMap (fun x => x ^ (-s / 2)))
  have hs : Tendsto (fun a : Set.Ioi (1 : ℝ) => 1 - a.val⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub tendsto_inv_order
  have hw : Tendsto (fun a : Set.Ioi (1 : ℝ) => W (1 - a.val⁻¹)) atTop (𝓝 (W 1)) := by
    simp only [W, spectralMap, map_sum, map_smul]
    apply tendsto_finsetSum
    intro i _
    apply Filter.Tendsto.smul _ tendsto_const_nhds
    apply Complex.continuous_ofReal.continuousAt.tendsto.comp
    have he := hs.neg.div_const 2
    by_cases hi : σ.eigenvalue i = 0
    · simp only [hi, Real.zero_rpow (by norm_num : -(1 : ℝ) / 2 ≠ 0)]
      apply tendsto_const_nhds.congr
      intro a
      exact (Real.zero_rpow (div_ne_zero (neg_ne_zero.mpr (sub_pos.mpr
        (inv_lt_one_of_one_lt₀ a.property)).ne') (by norm_num))).symm
    · exact (Real.continuous_const_rpow hi).continuousAt.tendsto.comp he
  simp only [renyiSandwich, adjoint_spectralMap]
  exact (hw.mul (tendsto_const_nhds (x := LinearMap.toContinuousLinearMap ρ.op) |>.mul hw)).norm

private lemma norm_rpow_bounds [Nontrivial H.state] (A : Operator H) (hA : A.IsPositive)
    {p : ℝ} (hp : 0 < p) :
    let S := ∑ i, (hA.isSymmetric.eigenvalues rfl i) ^ p
    let M := ‖LinearMap.toContinuousLinearMap A‖
    M ^ p ≤ S ∧ S ≤ (Module.finrank ℂ H.state : ℝ) * M ^ p := by
  let B := LinearMap.toContinuousLinearMap A
  have hmem : (‖B‖ : ℂ) ∈ _root_.spectrum ℂ B := spectrum.algebraMap_mem ℂ
    (CStarAlgebra.norm_mem_spectrum_of_nonneg B (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA))
  rw [ContinuousLinearMap.spectrum_eq] at hmem
  obtain ⟨j, hj⟩ := hA.isSymmetric.exists_eigenvalues_eq rfl
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hmem)
  have hj' := Complex.ofReal_injective hj
  constructor
  · rw [← hj']
    exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hA.nonneg_eigenvalues rfl i) p)
      (Finset.mem_univ j)
  · have hle (i) : hA.isSymmetric.eigenvalues rfl i ≤ ‖B‖ := by
      have hm := (hA.isSymmetric.hasEigenvalue_eigenvalues rfl i).mem_spectrum
      change _ ∈ _root_.spectrum ℂ B.toLinearMap at hm
      rw [← ContinuousLinearMap.spectrum_eq] at hm
      simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hA.nonneg_eigenvalues rfl i)] using spectrum.norm_le_norm_of_mem hm
    simpa [B] using Finset.sum_le_sum (s := Finset.univ) fun i _ =>
      Real.rpow_le_rpow (hA.nonneg_eigenvalues rfl i) (hle i) hp.le

/-- The trace functional to the reciprocal order converges to the operator norm
of the inverse-square-root sandwich, including for singular reference states. -/
theorem tendsto_sandwichedTraceFunctional_rpow_inv_atTop (ρ σ : Density H) :
    Tendsto (fun a : Set.Ioi (1 : ℝ) => (ρ.sandwichedTraceFunctional σ a) ^ a.val⁻¹) atTop
      (𝓝 ‖LinearMap.toContinuousLinearMap (ρ.renyiSandwich σ 1)‖) := by
  have : Nontrivial H.state := not_subsingleton_iff_nontrivial.mp fun _ =>
    ρ.op_ne_zero (Subsingleton.elim _ _)
  let d : ℝ := Module.finrank ℂ H.state
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Module.finrank_pos (R := ℂ) (M := H.state)
  have hdim : Tendsto (fun a : Set.Ioi (1 : ℝ) => d ^ a.val⁻¹) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      (Real.continuous_const_rpow hd.ne').continuousAt.tendsto.comp tendsto_inv_order
  have hn := ρ.tendsto_sandwich_norm_atTop σ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hn (by simpa only [one_mul] using hdim.mul hn)
  all_goals
    intro a
    have ha := zero_lt_one.trans a.property
    obtain ⟨hl, hu⟩ := norm_rpow_bounds _ (ρ.renyiSandwich_positive σ (1 - a.val⁻¹)) ha
  · change _ ^ a.val ≤ ρ.sandwichedTraceFunctional σ a at hl
    simpa only [Real.rpow_rpow_inv (norm_nonneg _) ha.ne'] using
      Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hl (inv_nonneg.mpr ha.le)
  · change ρ.sandwichedTraceFunctional σ a ≤ d * _ ^ a.val at hu
    simpa only [Real.mul_rpow hd.le (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_rpow_inv (norm_nonneg _) ha.ne'] using
      Real.rpow_le_rpow (ρ.sandwichedTraceFunctional_nonneg σ a) hu (inv_nonneg.mpr ha.le)

/-- Sandwiched Rényi relative entropy converges to max-relative entropy as the order
tends to infinity, with the limit taken in the extended nonnegative reals. -/
theorem tendsto_sandwichedRenyiRelativeEntropy_atTop (ρ σ : Density H) :
    Tendsto (ρ.sandwichedRenyiRelativeEntropy σ) atTop (𝓝 (ρ.maxRelativeEntropy σ)) := by
  change Tendsto (fun a => ρ.sandwichedRenyiRelativeEntropy σ a) _ _
  by_cases h : ρ.AbsolutelyContinuous σ
  · have hroot := ρ.tendsto_sandwichedTraceFunctional_rpow_inv_atTop σ
    have hnorm : 1 ≤ ‖LinearMap.toContinuousLinearMap (ρ.renyiSandwich σ 1)‖ := by
      apply ge_of_tendsto hroot
      exact .of_forall fun a => Real.one_le_rpow (ρ.one_le_sandwichedTraceFunctional σ a.property h)
        (inv_nonneg.mpr (zero_lt_one.trans a.property).le)
    have hs : Tendsto (fun a : Set.Ioi (1 : ℝ) => 1 - a.val⁻¹) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub tendsto_inv_order
    have hlog := (hroot.log (zero_lt_one.trans_le hnorm).ne').div hs one_ne_zero
    simp only [div_one] at hlog
    simp only [sandwichedRenyiRelativeEntropy, maxRelativeEntropy, h, reduceIte]
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    apply hlog.congr
    intro a
    simp only [Pi.div_apply]
    rw [Real.log_rpow (zero_lt_one.trans_le (ρ.one_le_sandwichedTraceFunctional σ a.property h))]
    field_simp [(zero_lt_one.trans a.property).ne', (sub_pos.mpr a.property).ne']
  · simpa only [sandwichedRenyiRelativeEntropy, maxRelativeEntropy, h, reduceIte] using
      (tendsto_const_nhds : Tendsto (fun _ : Set.Ioi (1 : ℝ) => (⊤ : ENNReal)) atTop (𝓝 ⊤))

/-- A common isometric embedding preserves max-relative entropy, including infinite values. -/
theorem maxRelativeEntropy_map_isometry {K : Qudit} (ρ σ : Density H)
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).maxRelativeEntropy (σ.map V) = ρ.maxRelativeEntropy σ := by
  apply tendsto_nhds_unique ((ρ.map V).tendsto_sandwichedRenyiRelativeEntropy_atTop (σ.map V))
  exact (ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop σ).congr fun a =>
    (ρ.sandwichedRenyiRelativeEntropy_map_isometry σ a V).symm

/-- Simultaneous unitary transport preserves max-relative entropy. -/
@[simp]
theorem maxRelativeEntropy_map_unitary {K : Qudit} (ρ σ : Density H)
    (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).maxRelativeEntropy (σ.map U) = ρ.maxRelativeEntropy σ :=
  ρ.maxRelativeEntropy_map_isometry σ U

/-- Max-relative entropy bounds the sandwiched Rényi relative entropy at every order above one. -/
theorem sandwichedRenyiRelativeEntropy_le_maxRelativeEntropy (ρ σ : Density H)
    (a : Set.Ioi (1 : ℝ)) :
    ρ.sandwichedRenyiRelativeEntropy σ a ≤ ρ.maxRelativeEntropy σ :=
  ge_of_tendsto (ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop σ)
    ((eventually_ge_atTop a).mono fun _ h => ρ.monotone_sandwichedRenyiRelativeEntropy σ h)

/-- Umegaki relative entropy bounds max-relative entropy from below. -/
theorem relativeEntropy_le_maxRelativeEntropy (ρ σ : Density H) :
    ρ.relativeEntropy σ ≤ ρ.maxRelativeEntropy σ :=
  ge_of_tendsto (ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop σ)
    (.of_forall (ρ.relativeEntropy_le_sandwichedRenyiRelativeEntropy σ))

/-- The max-relative entropy of a state with respect to itself vanishes. -/
lemma maxRelativeEntropy_self (ρ : Density H) : ρ.maxRelativeEntropy ρ = 0 := by
  apply tendsto_nhds_unique (ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop ρ)
  exact tendsto_const_nhds.congr fun a => (ρ.sandwichedRenyiRelativeEntropy_self a).symm

/-- Max-relative entropy vanishes exactly for equal density states. -/
theorem maxRelativeEntropy_eq_zero_iff (ρ σ : Density H) :
    ρ.maxRelativeEntropy σ = 0 ↔ ρ = σ := by
  constructor
  · intro h
    exact (ρ.relativeEntropy_eq_zero_iff σ).mp
      (bot_unique ((ρ.relativeEntropy_le_maxRelativeEntropy σ).trans_eq h))
  · rintro rfl
    exact ρ.maxRelativeEntropy_self

/-- Max-relative entropy is additive on tensor products of independent state pairs,
including when either factor has infinite divergence. -/
theorem maxRelativeEntropy_tensor {K : Qudit} (ρ σ : Density H) (τ ω : Density K) :
    (ρ.tensor τ).maxRelativeEntropy (σ.tensor ω) =
      ρ.maxRelativeEntropy σ + τ.maxRelativeEntropy ω := by
  apply tendsto_nhds_unique ((ρ.tensor τ).tendsto_sandwichedRenyiRelativeEntropy_atTop (σ.tensor ω))
  exact ((ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop σ).add
    (τ.tendsto_sandwichedRenyiRelativeEntropy_atTop ω)).congr fun a =>
      (ρ.sandwichedRenyiRelativeEntropy_tensor σ τ ω a).symm

/-- Appending a common ancillary state preserves max-relative entropy. -/
theorem maxRelativeEntropy_tensor_right {K : Qudit} (ρ σ : Density H) (τ : Density K) :
    (ρ.tensor τ).maxRelativeEntropy (σ.tensor τ) = ρ.maxRelativeEntropy σ := by
  rw [maxRelativeEntropy_tensor, maxRelativeEntropy_self, add_zero]

/-- Prepending a common ancillary state preserves max-relative entropy. -/
theorem maxRelativeEntropy_tensor_left {K : Qudit} (ρ σ : Density H) (τ : Density K) :
    (τ.tensor ρ).maxRelativeEntropy (τ.tensor σ) = ρ.maxRelativeEntropy σ := by
  rw [maxRelativeEntropy_tensor, maxRelativeEntropy_self, zero_add]

end

end Qudit.Density

namespace Qudit.QuantumChannel

/-- Data processing for max-relative entropy under any quantum channel, including
singular references and infinite divergences. -/
theorem maxRelativeEntropy_map_le {H K : Qudit} (Φ : QuantumChannel H K) (ρ σ : Density H) :
    (Φ.map ρ).maxRelativeEntropy (Φ.map σ) ≤ ρ.maxRelativeEntropy σ :=
  le_of_tendsto_of_tendsto' ((Φ.map ρ).tendsto_sandwichedRenyiRelativeEntropy_atTop (Φ.map σ))
    (ρ.tendsto_sandwichedRenyiRelativeEntropy_atTop σ) (Φ.sandwichedRenyiRelativeEntropy_map_le ρ σ)

end Qudit.QuantumChannel
