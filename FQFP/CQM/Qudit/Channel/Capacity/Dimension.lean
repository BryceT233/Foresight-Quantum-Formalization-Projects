/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Capacity/Capacity.lean: input and output dimension bounds on achievable rates,
boundedness of achievable rates, and the input dimension bound on capacity.
These statements are informal upstream. The file also proposes the capacities of identity
and replacement channels and monotonicity under composition. The proofs below are local.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity
public import FQFP.CQM.Qudit.Channel.MeasurePrepare

/-!
# Dimension bounds for quantum communication

A POVM on a system of dimension `k` can correctly identify a family of equiprobable messages
with total (unnormalized) success probability at most `k`. A code approximating the identity
has success probability at least `(1 - ε)²` on each logical basis state. Pulling its decoding
measurement back to the physical register bounds the rate in qubits per use.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace Qudit

variable {H K S : Qudit}

/-- The expectation of a positive operator in any density is bounded by its trace. -/
lemma Density.expectation_le_trace (ρ : Density H) {A : Operator H} (hA : A.IsPositive) :
    ρ.expectation A ≤ A.trace.re := by
  change (LinearMap.trace ℂ H.state (A * ρ.op)).re ≤ (LinearMap.trace ℂ H.state A).re
  rw [LinearMap.trace_eq_sum_inner _ ρ.eigenbasis, LinearMap.trace_eq_sum_inner A ρ.eigenbasis,
    Complex.re_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [mul_apply_eq_comp, ρ.apply_eigenbasis, map_smul, inner_smul_right,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_of_le_one_left (hA.re_inner_nonneg_right _) (ρ.eigenvalue_le_one i)

/-- For one state per message, the sum of correct decoding probabilities is at most the
dimension of the system being measured. -/
theorem POVM.sum_probability_le_finrank {ι : Type*} [Fintype ι] (M : POVM H ι)
    (ρ : ι → Density H) : ∑ i, M.probability (ρ i) i ≤ Module.finrank ℂ H.state := by
  calc
    _ ≤ ∑ i, (M.op i).trace.re :=
      Finset.sum_le_sum fun i _ => (ρ i).expectation_le_trace (M.positive i)
    _ = _ := by rw [← Complex.re_sum, ← map_sum, M.sum_op, LinearMap.trace_one]; simp

namespace QuantumChannel

/-- A code factoring through `H` and approximating the identity on `S` must satisfy the
one-shot dimension bound, also when either register has dimension zero. -/
theorem Approximates.finrank_mul_sq_le {E : QuantumChannel S H} {D : QuantumChannel H S}
    {ε : ℝ} (h : (D.comp E).Approximates (id S) ε) (hε : ε ≤ 1) :
    (Module.finrank ℂ S.state : ℝ) * (1 - ε) ^ 2 ≤ Module.finrank ℂ H.state := by
  let b := stdOrthonormalBasis ℂ S.state
  let ρ i := Density.pure (UnitState.ofBasis b i)
  let M := (POVM.ofBasis b).pullback D
  have hsuccess i : (1 - ε) ^ 2 ≤ M.probability (E.map (ρ i)) i := by
    have hf := h (ρ i)
    rw [map_id, map_comp] at hf
    have hs := pow_le_pow_left₀ (sub_nonneg.mpr hε) hf 2
    rw [Density.fidelity_pure_sq] at hs
    rw [POVM.probability_pullback]
    exact hs
  have hs := (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsuccess i)).trans
    (M.sum_probability_le_finrank fun i => E.map (ρ i))
  simpa using hs

private lemma logb_two_natCast_nonneg (k : ℕ) : 0 ≤ Real.logb 2 k := by
  cases k with
  | zero => simp
  | succ k => exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_pos k)

/-- A rate in qubits per use is bounded by the input log-dimension. -/
theorem AchievesRate.le_log_finrank_input {Φ : QuantumChannel H K} {R : ℝ}
    (h : Φ.AchievesRate R) : R ≤ Real.logb 2 (Module.finrank ℂ H.state) := by
  let k := Module.finrank ℂ H.state
  change R ≤ Real.logb 2 k
  by_contra! hR
  -- Choose a tolerance whose squared-fidelity penalty costs only half of the alleged rate gap,
  -- even for a single use.
  let t := (R - Real.logb 2 k) / 4
  have ht : 0 < t := by dsimp [t]; linarith
  let q : ℝ := (2 : ℝ) ^ (-t)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq' : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr ht)
  obtain ⟨n, d, Ψ, ⟨E, D, rfl⟩, hr, ha⟩ := h (1 - q) (sub_pos.mpr hq')
  rw [← comp_assoc] at ha
  have hc := ha.finrank_mul_sq_le (by linarith : 1 - q ≤ 1)
  rw [finrank_std, finrank_tensorPower, Nat.cast_pow, sub_sub_cancel] at hc
  change (d : ℝ) * q ^ 2 ≤ (k : ℝ) ^ (n + 1) at hc
  have hpos : 0 < R := (logb_two_natCast_nonneg k).trans_lt hR
  have hd : d ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, Real.logb_zero] at hr
    exact (not_lt_of_ge hr) (mul_pos hpos (by positivity))
  have hd' : 0 < (d : ℝ) := by positivity
  have hb := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos hd' (pow_pos hq 2)) hc
  rw [Real.logb_mul hd'.ne' (pow_pos hq 2).ne', Real.logb_pow, Real.logb_pow,
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)] at hb
  push_cast at hb
  have hgap := mul_nonneg (sub_nonneg.mpr hR.le) (Nat.cast_nonneg (α := ℝ) n)
  dsimp [t] at hb
  nlinarith

/-- A rate in qubits per use is bounded by the output log-dimension. -/
theorem AchievesRate.le_log_finrank_output {Φ : QuantumChannel H K} {R : ℝ}
    (h : Φ.AchievesRate R) : R ≤ Real.logb 2 (Module.finrank ℂ K.state) := by
  have he : (id K).Emulates Φ := ⟨Φ, id K, by rw [id_comp, id_comp]⟩
  exact (he.achievesRate h).le_log_finrank_input

/-- The achievable rates of every channel form a bounded-above set. -/
theorem bddAbove_achievesRate (Φ : QuantumChannel H K) : BddAbove {R | Φ.AchievesRate R} :=
  ⟨_, fun _ h => AchievesRate.le_log_finrank_input h⟩

/-- Capacity is the least upper bound after adjoining zero. This also describes channels
whose achievable-rate set is empty under the real supremum convention. -/
theorem isLUB_insert_zero_achievesRate (Φ : QuantumChannel H K) :
    IsLUB (insert 0 {R | Φ.AchievesRate R}) Φ.quantumCapacity := by
  rcases Set.eq_empty_or_nonempty {R | Φ.AchievesRate R} with he | hn
  · simpa only [quantumCapacity, he, Real.sSup_empty, insert_empty_eq] using
      (isLUB_singleton (a := (0 : ℝ)))
  · obtain ⟨R, hR⟩ := hn
    have h₀ : Φ.AchievesRate 0 := by
      intro ε hε
      obtain ⟨n, d, Ψ, he, _, ha⟩ := hR ε hε
      exact ⟨n, d, Ψ, he, by simpa only [zero_mul] using logb_two_natCast_nonneg d, ha⟩
    rw [Set.insert_eq_of_mem (s := {R | Φ.AchievesRate R}) h₀]
    exact isLUB_csSup ⟨R, hR⟩ Φ.bddAbove_achievesRate

/-- Capacity is bounded by the smaller of the input and output log-dimensions. -/
theorem quantumCapacity_le_min_log_finrank (Φ : QuantumChannel H K) :
    Φ.quantumCapacity ≤ min (Real.logb 2 (Module.finrank ℂ H.state))
      (Real.logb 2 (Module.finrank ℂ K.state)) := by
  apply Φ.isLUB_insert_zero_achievesRate.2
  rintro R (rfl | h)
  · exact le_min (logb_two_natCast_nonneg _) (logb_two_natCast_nonneg _)
  · exact le_min (AchievesRate.le_log_finrank_input h) (AchievesRate.le_log_finrank_output h)

/-- Exact simulation cannot increase the operational quantum capacity. -/
theorem Emulates.quantumCapacity_le {L : Qudit} {Φ : QuantumChannel H K} {Ψ : QuantumChannel S L}
    (h : Φ.Emulates Ψ) : Ψ.quantumCapacity ≤ Φ.quantumCapacity :=
  Ψ.isLUB_insert_zero_achievesRate.2 fun _ hr =>
    Φ.isLUB_insert_zero_achievesRate.1 ((Set.insert_subset_insert (fun _ => h.achievesRate)) hr)

/-- A serial composition transmits at most the capacity of either channel. -/
theorem quantumCapacity_comp_le (D : QuantumChannel K S) (E : QuantumChannel H K) :
    (D.comp E).quantumCapacity ≤ min E.quantumCapacity D.quantumCapacity := by
  have he : E.Emulates (D.comp E) := ⟨id H, D, by rw [comp_id]⟩
  have hd : D.Emulates (D.comp E) := ⟨E, id S, by rw [id_comp]⟩
  exact le_min he.quantumCapacity_le hd.quantumCapacity_le

/-- The noiseless channel transmits exactly the logarithm of its dimension in qubits per use. -/
theorem quantumCapacity_id (H : Qudit) :
    (id H).quantumCapacity = Real.logb 2 (Module.finrank ℂ H.state) := by
  refine le_antisymm ((id H).quantumCapacity_le_min_log_finrank.trans (min_le_left ..)) ?_
  exact le_csSup ((id H).bddAbove_achievesRate) (id_achievesRate_log_finrank H)

/-- Discarding the input and preparing a fixed state has zero quantum capacity. -/
theorem quantumCapacity_replacement (H : Qudit) (σ : Density K) :
    (replacement H σ).quantumCapacity = 0 := by
  have h : (id (𝟙_ Qudit)).Emulates (replacement H σ) :=
    ⟨CausalQudit.discard ⟨H⟩, σ.toState, by rw [id_comp]; rfl⟩
  refine le_antisymm ?_ ((replacement H σ).isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..))
  simpa only [quantumCapacity_id, state_tensorUnit, Module.finrank_self, Nat.cast_one,
    Real.logb_one] using h.quantumCapacity_le

end QuantumChannel

end Qudit
