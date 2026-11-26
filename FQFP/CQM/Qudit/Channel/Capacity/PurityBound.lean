/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.PhaseCoding
public import FQFP.CQM.Qudit.Channel.Capacity.TypicalSubspace
public import FQFP.CQM.Qudit.Channel.Dilation.Tensor

/-!
# An achievable rate from the output purity

Parallel copies of the finite phase code give worst-case transmission when the logical
dimension times the full environment dimension times the receiver purity decays. This
estimate uses the untruncated spectra.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Filter
open scoped BigOperators Topology

namespace Qudit

variable {A B E : Qudit}

/-- The purity of a density operator, equal to the sum of its squared eigenvalues. -/
def Density.purity (ρ : Density A) : ℝ := (LinearMap.trace ℂ A.state (ρ.op ^ 2)).re

lemma Density.purity_eq_sum_sq (ρ : Density A) : ρ.purity = ∑ i, ρ.eigenvalue i ^ 2 := by
  rw [purity, LinearMap.trace_eq_sum_inner _ ρ.eigenbasis, Complex.re_sum]
  simp only [sq, mul_apply_eq_comp, ρ.apply_eigenbasis, map_smul, inner_smul_right,
    ρ.eigenbasis.inner_eq_one, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma Density.purity_nonneg (ρ : Density A) : 0 ≤ ρ.purity := by
  rw [ρ.purity_eq_sum_sq]
  positivity

/-- The maximally mixed state has purity reciprocal to the register dimension. -/
lemma Density.purity_maximallyMixed (A : Qudit) (h : Module.finrank ℂ A.state ≠ 0) :
    (Density.maximallyMixed A h).purity = (Module.finrank ℂ A.state : ℝ)⁻¹ := by
  rw [purity, Density.op_maximallyMixed, sq, smul_mul_assoc, mul_smul_comm, one_mul, map_smul,
    map_smul, LinearMap.trace_one]
  simp [h]

/-- Purity multiplies for independently prepared states. -/
lemma Density.purity_tensor (ρ : Density A) (σ : Density B) :
    (ρ.tensor σ).purity = ρ.purity * σ.purity := by
  obtain ⟨e, he⟩ := ρ.exists_equiv_eigenvalue_tensor σ
  simp only [purity_eq_sum_sq, ← e.sum_comp, Fintype.sum_prod_type, he, mul_pow,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Purity of an independent block of positive length. -/
lemma Density.purity_tensorPower (ρ : Density A) (n : ℕ) :
    (ρ.tensorPower n).purity = ρ.purity ^ (n + 1) := by
  induction n with
  | zero => exact (pow_one _).symm
  | succ n ih => exact (ρ.purity_tensor _).trans (by rw [ih, pow_succ' _ (n + 1)])

namespace QuantumChannel

/-- Every channel admits worst-case codes at nonnegative rates for which the exponential
rate factor times environment dimension times output purity is strictly below one. -/
theorem Dilation.achievesRate_of_dim_mul_purity_lt_one {Φ : QuantumChannel A B} (d : Φ.Dilation E)
    (ρ : Density A) {R : ℝ} (hR : 0 ≤ R)
    (h : Real.exp (R * Real.log 2) * Module.finrank ℂ E.state * (Φ.map ρ).purity < 1) :
    Φ.AchievesRate R := by
  let q := Real.exp (R * Real.log 2) * Module.finrank ℂ E.state * (Φ.map ρ).purity
  have hq : 0 ≤ q := mul_nonneg (by positivity) (Φ.map ρ).purity_nonneg
  intro ε hε
  have htol : 0 < ((ε / 2) ^ 2 / 4) ^ 2 := by positivity
  have hlim : Tendsto (fun n : ℕ => 3 * q ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul, mul_zero] using
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hq h).mul_const q).const_mul 3)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds htol)).exists
  let m : ℝ := n + 1
  let x := Real.exp (m * (R * Real.log 2))
  have hx : 1 ≤ x := Real.one_le_exp (mul_nonneg (by dsimp [m]; positivity)
    (mul_nonneg hR (by positivity)))
  let k := ⌊2 * x⌋₊
  have hk : 2 * x < (k + 1 : ℝ) := Nat.lt_floor_add_one _
  have hk' : (k + 1 : ℝ) ≤ 3 * x := by
    linarith only [Nat.floor_le (show 0 ≤ 2 * x by linarith), hx]
  have hdim : (Module.finrank ℂ (Qudit.tensorPower E n ⊗ std (k + 1)).state : ℝ) *
      (((Φ.tensorPower n).map (ρ.tensorPower n)).purity) ≤ ((ε / 2) ^ 2 / 4) ^ 2 := by
    change (Module.finrank ℂ
      (TensorProduct ℂ (Qudit.tensorPower E n).state (std (k + 1)).state) : ℝ) * _ ≤ _
    rw [Module.finrank_tensorProduct, finrank_tensorPower, finrank_std, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add_one, Φ.map_tensorPower, Density.purity_tensorPower]
    apply le_trans _ hn.le
    calc
      _ ≤ (Module.finrank ℂ E.state : ℝ) ^ (n + 1) * (3 * x) * (Φ.map ρ).purity ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk' (by positivity))
          (pow_nonneg (Φ.map ρ).purity_nonneg _)
      _ = 3 * q ^ (n + 1) := by
        have hexp : x = Real.exp (R * Real.log 2) ^ (n + 1) := by
          rw [← Real.exp_nat_mul]; simp only [x, m, Nat.cast_add_one]
        rw [hexp]
        dsimp [q]
        ring
  obtain ⟨Ψ, he, hf⟩ := (d.tensorPower n).exists_code_of_dim_mul_purity_le (ρ.tensorPower n)
    (UnitState.maximallyEntangled (ZBasis (k + 1))) (show 0 ≤ ε / 2 by positivity) hdim
  obtain ⟨s, Γ, hs, hΓ, hgood⟩ := Ψ.exists_subcode_of_maximallyEntangledFidelity (ZBasis (k + 1))
    (show 0 < ε / 2 by positivity) hf
  refine ⟨n, s, Γ, he.trans hΓ, ?_, by simpa only [show 2 * (ε / 2) = ε by ring] using hgood⟩
  rw [finrank_std] at hs
  have hs' : x ≤ s := by
    have hcast : (k + 1 : ℝ) ≤ 2 * s := by exact_mod_cast hs
    linarith only [hk, hcast]
  have hl := Real.log_le_log (Real.exp_pos _) hs'
  rw [Real.log_exp] at hl
  rw [Real.logb, le_div_iff₀ (by positivity)]
  dsimp [m] at hl
  linarith only [hl]

/-- The untruncated random coding lower bound in qubits per use, for any realization of a
channel. A smaller realizing environment gives a stronger bound. -/
theorem Dilation.neg_logb_dim_mul_purity_le_quantumCapacity {Φ : QuantumChannel A B}
    (d : Φ.Dilation E) (ρ : Density A) :
    -Real.logb 2 (Module.finrank ℂ E.state * (Φ.map ρ).purity) ≤ Φ.quantumCapacity := by
  let p : ℝ := Module.finrank ℂ E.state * (Φ.map ρ).purity
  have hp : 0 ≤ p := mul_nonneg (Nat.cast_nonneg _) (Φ.map ρ).purity_nonneg
  have hQ : 0 ≤ Φ.quantumCapacity := Φ.isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..)
  change -Real.logb 2 p ≤ _
  rcases hp.eq_or_lt with hz | hpos
  · simpa only [← hz, Real.logb_zero, neg_zero] using hQ
  apply le_of_forall_lt_imp_le_of_dense
  intro r hr
  by_cases hr' : 0 ≤ r
  · apply le_csSup Φ.bddAbove_achievesRate
    apply d.achievesRate_of_dim_mul_purity_lt_one ρ hr'
    rw [mul_assoc]
    change Real.exp (r * Real.log 2) * p < 1
    rw [← Real.exp_log hpos, ← Real.exp_add, ← Real.exp_zero, Real.exp_lt_exp]
    rw [Real.logb, ← neg_div] at hr
    linarith only [(lt_div_iff₀ (by positivity : 0 < Real.log 2)).mp hr]
  · exact (le_of_not_ge hr').trans hQ

/-- Applying the purity coding theorem to a joint input on any positive block gives
a lower bound per physical use by block flattening. -/
theorem neg_logb_dim_mul_purity_div_blockLength_le_quantumCapacity (Φ : QuantumChannel A B)
    (n : ℕ) (d : (Φ.tensorPower n).Dilation E) (ρ : Density (Qudit.tensorPower A n)) :
    -Real.logb 2 (Module.finrank ℂ E.state * ((Φ.tensorPower n).map ρ).purity) / (n + 1) ≤
      Φ.quantumCapacity := by
  apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
  exact (d.neg_logb_dim_mul_purity_le_quantumCapacity ρ).trans (Φ.quantumCapacity_tensorPower_le n)

/-- When the receiver and environment are maximally mixed, the phase-coding lower bound
is exactly the forward coherent information in qubits. -/
theorem Dilation.coherentInfo_div_log_two_le_quantumCapacity_of_maximallyMixed
    {Φ : QuantumChannel A B} (d : Φ.Dilation E) (ρ : Density A)
    {hB : Module.finrank ℂ B.state ≠ 0} {hE : Module.finrank ℂ E.state ≠ 0}
    (hb : Φ.map ρ = Density.maximallyMixed B hB)
    (he : d.complementary.map ρ = Density.maximallyMixed E hE) :
    Φ.coherentInfo ρ / Real.log 2 ≤ Φ.quantumCapacity := by
  have h := d.neg_logb_dim_mul_purity_le_quantumCapacity ρ
  rw [hb, Density.purity_maximallyMixed, Real.logb, ← div_eq_mul_inv,
    Real.log_div (by exact_mod_cast hE) (by exact_mod_cast hB)] at h
  rw [d.coherentInfo_eq, hb, he, Density.vonNeumannEntropy_maximallyMixed,
    Density.vonNeumannEntropy_maximallyMixed]
  rwa [← neg_div, neg_sub] at h

end QuantumChannel

end Qudit
