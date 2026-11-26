/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Capacity/Capacity.lean: the informal coherent-information coding bound
and the lower-bound direction of regularized capacity. The proofs here use Qudit's
forward coherent information and its worst-case root-fidelity error criterion.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.TypicalCoding
public import FQFP.CQM.Qudit.Channel.Dilation.Tensor

/-!
# Direct quantum channel coding theorem

Independent phase codes on long memoryless blocks decouple the environment and reference.
The register dimension grows at the rate in qubits, and the typicality window is in nats.
Entanglement recovery and subcode selection give the worst-case transmission criterion.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Filter
open scoped BigOperators Topology

namespace Qudit

variable {A B E : Qudit}

/-- The reference half of a maximally entangled input is maximally mixed. -/
lemma UnitState.partialTraceLeft_pure_maximallyEntangled {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι ℂ A.state) :
    (Density.pure (UnitState.maximallyEntangled b)).partialTraceLeft =
      Density.maximallyMixed A (by
        rw [Module.finrank_eq_card_basis b.toBasis]
        exact Fintype.card_ne_zero) := by
  rw [← UnitState.partialTraceRight_pure_maximallyEntangled b]
  apply Density.ext
  simp only [Density.op_partialTraceLeft, Density.op_partialTraceRight, Density.op_pure,
    UnitState.coe_maximallyEntangled]
  rw [Operator.outer_smul_self (H := A ⊗ A), map_smul, map_smul,
    Operator.partialTraceLeft_outer_sum_basis b, Operator.partialTraceRight_outer_sum_basis b]

/-- A uniform spectrum has no surprisal fluctuations. -/
lemma Density.entropyVariance_maximallyMixed (A : Qudit) (h : Module.finrank ℂ A.state ≠ 0) :
    (Density.maximallyMixed A h).entropyVariance = 0 := by
  let τ := Density.maximallyMixed A h
  have he (i : Fin (Module.finrank ℂ A.state)) :
      τ.op (τ.eigenbasis i) = (↑((Module.finrank ℂ A.state : ℝ)⁻¹) : ℂ) • τ.eigenbasis i := by
    simp [τ]
  rw [Density.entropyVariance, τ.sum_eigenvalue_eq_of_eigenbasis τ.eigenbasis _ he
    (fun x => x * (-Real.log x - τ.vonNeumannEntropy) ^ 2)]
  simp [τ]

namespace QuantumChannel

private lemma block_phase_error {Φ : QuantumChannel A B} (d : Φ.Dilation E) (ρ : Density A)
    (n k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let m : ℝ := n + 1
    let d' := d.tensorPower n
    let τ := Density.maximallyMixed (std (k + 1)) (by simp [finrank_std])
    ∃ v : UnitState (Qudit.tensorPower A n ⊗ std (k + 1)),
      (2 * (((d'.complementary.tensor (id _)).map (Density.pure v)).traceDistance
        (((d.complementary.map ρ).tensorPower n).tensor τ))) ^ 2 ≤
      3 * (8 * (((d.complementary.map ρ).entropyVariance + (Φ.map ρ).entropyVariance) /
        (m * δ ^ 2)) + (k + 1 : ℝ) * Real.exp (m * (2 * δ - Φ.coherentInfo ρ))) := by
  intro m d' τ
  let σ := ((d.complementary.map ρ).tensorPower n).tensor τ
  let μ := (Φ.map ρ).tensorPower n
  let w := m * δ
  have hm : 0 < m := by dsimp [m]; positivity
  have hw : 0 < w := mul_pos hm hδ
  obtain ⟨v, hv⟩ := d'.exists_decoupled_input_of_typical_projections (ρ.tensorPower n) τ w
  simp only [d', Dilation.complementary_tensorPower, map_tensorPower] at hv
  refine ⟨v, ?_⟩
  rw [show d'.complementary = d.complementary.tensorPower n from d.complementary_tensorPower n]
  apply hv.trans
  change 3 * (8 * ((1 - σ.expectation _) + (1 - μ.expectation _)) +
    ((σ.typicalIndices w).card : ℝ) * _) ≤ _
  have ht₁ : 1 - σ.expectation (σ.typicalProjection w) ≤
      (d.complementary.map ρ).entropyVariance / (m * δ ^ 2) := by
    rw [Density.expectation_typicalProjection]
    apply (σ.one_sub_typical_weight_le hw).trans_eq
    simp only [σ, τ, Density.entropyVariance_tensor, Density.entropyVariance_tensorPower,
      Density.entropyVariance_maximallyMixed, add_zero]
    change m * _ / (m * δ) ^ 2 = _
    field_simp
  have ht₂ : 1 - μ.expectation (μ.typicalProjection w) ≤ (Φ.map ρ).entropyVariance /
      (m * δ ^ 2) := by
    rw [Density.expectation_typicalProjection]
    exact (Φ.map ρ).one_sub_typical_weight_tensorPower_le n hδ
  have hprod := mul_le_mul (σ.card_typicalIndices_le w) (μ.sum_sq_typical_eigenvalues_le w)
    (by positivity) (Real.exp_pos _).le
  have he : Real.exp (σ.vonNeumannEntropy + w) * Real.exp (-μ.vonNeumannEntropy + w) =
      (k + 1 : ℝ) * Real.exp (m * (2 * δ - Φ.coherentInfo ρ)) := by
    dsimp only [σ, μ, τ]
    rw [← Real.exp_add, Density.vonNeumannEntropy_tensor, Density.vonNeumannEntropy_tensorPower,
      Density.vonNeumannEntropy_tensorPower, Density.vonNeumannEntropy_maximallyMixed,
      finrank_std, Nat.cast_add_one, d.coherentInfo_eq]
    conv_rhs => lhs; rw [← Real.exp_log (show 0 < (k + 1 : ℝ) by positivity)]
    rw [← Real.exp_add]
    congr 1
    dsimp [m, w]
    ring
  rw [he] at hprod
  rw [add_div]
  gcongr

/-- Positive rates strictly below forward coherent information (converted from nats to
qubits) admit decoupled physical inputs on arbitrarily long blocks. -/
theorem admitsDecoupledInputs_of_lt_coherentInfo (Φ : QuantumChannel A B) (ρ : Density A)
    {R : ℝ} (hR : 0 < R) (hr : R < Φ.coherentInfo ρ / Real.log 2) :
    Φ.AdmitsDecoupledInputs R := by
  let d := Φ.dilation
  let g := Φ.coherentInfo ρ - R * Real.log 2
  have hg : 0 < g := sub_pos.mpr ((lt_div_iff₀ (by positivity : 0 < Real.log 2)).mp hr)
  let δ := g / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let V := (d.complementary.map ρ).entropyVariance + (Φ.map ρ).entropyVariance
  let m (n : ℕ) : ℝ := n + 1
  have hm : Tendsto m atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hv : Tendsto (fun n => V / (m n * δ ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_mul_const_atTop_of_pos (sq_pos_of_pos hδ)).mpr hm)
  have hex : Tendsto (fun n => Real.exp (m n * (-g / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg (by linarith : -g / 2 < 0)).mpr hm)
  have hlim : Tendsto (fun n => 3 * (8 * (V / (m n * δ ^ 2)) +
      2 * Real.exp (m n * (-g / 2)))) atTop (𝓝 0) := by
    simpa using (((hv.const_mul 8).add (hex.const_mul 2)).const_mul 3)
  intro η hη N
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop N).and
    (hlim.eventually (gt_mem_nhds (show 0 < (2 * η) ^ 2 by positivity)))).exists
  let x := Real.exp (m n * (R * Real.log 2))
  let k := ⌊x⌋₊
  have hx : 1 ≤ x := Real.one_le_exp (mul_nonneg (by dsimp [m]; positivity)
    (mul_nonneg hR.le (by positivity)))
  have hk : x < (k + 1 : ℝ) := Nat.lt_floor_add_one _
  have hk' : (k + 1 : ℝ) ≤ 2 * x := by
    linarith only [Nat.floor_le (zero_le_one.trans hx), hx]
  obtain ⟨v, hv⟩ := block_phase_error d ρ n k hδ
  refine ⟨n, k, _, d.tensorPower n, v, (d.complementary.map ρ).tensorPower n, hn, ?_, ?_⟩
  · rw [Real.logb, le_div_iff₀ (by positivity)]
    have hl := Real.log_le_log (Real.exp_pos _) hk.le
    rw [Real.log_exp] at hl
    dsimp [m] at hl
    linarith only [hl]
  · rw [UnitState.partialTraceLeft_pure_maximallyEntangled]
    have hxexp : (2 * x) * Real.exp (m n * (2 * δ - Φ.coherentInfo ρ)) =
        2 * Real.exp (m n * (-g / 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [δ, g]
      ring
    have hprod := (mul_le_mul_of_nonneg_right hk' (Real.exp_pos _).le).trans_eq hxexp
    have hbound := hv.trans ((show 3 * (8 * (V / (m n * δ ^ 2)) +
      (k + 1 : ℝ) * Real.exp (m n * (2 * δ - Φ.coherentInfo ρ))) ≤
        3 * (8 * (V / (m n * δ ^ 2)) + 2 * Real.exp (m n * (-g / 2))) by gcongr).trans hsmall.le)
    have hdist := (sq_le_sq₀ (mul_nonneg (by norm_num) (Density.traceDistance_nonneg ..))
      (mul_nonneg (by norm_num) hη.le)).mp hbound
    have hf := Density.one_sub_fidelity_le_traceDistance
      (((d.tensorPower n).complementary.tensor (id _)).map (Density.pure v))
      (((d.complementary.map ρ).tensorPower n).tensor (Density.maximallyMixed (std (k + 1))
        (by simp [finrank_std])))
    linarith only [hdist, hf]

/-- Every rate strictly below the single-input coherent information in qubits is achievable
with worst-case root fidelity arbitrarily close to one. -/
theorem achievesRate_of_lt_coherentInfo (Φ : QuantumChannel A B) (ρ : Density A)
    {R : ℝ} (h : R < Φ.coherentInfo ρ / Real.log 2) : Φ.AchievesRate R := by
  by_cases hR : 0 < R
  · obtain ⟨r, hRr, hr⟩ := exists_between h
    have hc := Φ.admitsDecoupledInputs_of_lt_coherentInfo ρ (hR.trans hRr) hr
    exact hc.achievesEntanglementRate.achievesRate hRr
  · obtain ⟨i⟩ := ρ.spectrum.nonempty
    exact (Φ.achievesRate_zero (by have := i.isLt; lia)).mono (le_of_not_gt hR)

/-- Forward coherent information in qubits lower-bounds operational capacity. -/
theorem coherentInfo_div_log_two_le_quantumCapacity (Φ : QuantumChannel A B) (ρ : Density A) :
    Φ.coherentInfo ρ / Real.log 2 ≤ Φ.quantumCapacity := by
  apply le_of_forall_lt_imp_le_of_dense
  exact fun _ h => le_csSup Φ.bddAbove_achievesRate (Φ.achievesRate_of_lt_coherentInfo ρ h)

/-- The regularized forward coherent information is an achievable capacity lower bound in
qubits per channel use. Block inputs may be entangled across sites. -/
theorem regularizedCoherentInfo_le_quantumCapacity (Φ : QuantumChannel A B) :
    Φ.regularizedCoherentInfo ≤ Φ.quantumCapacity :=
  Φ.regularizedCoherentInfo_le_quantumCapacity_of_block_bound fun n ρ =>
    (Φ.tensorPower n).coherentInfo_div_log_two_le_quantumCapacity ρ

end QuantumChannel

end Qudit
