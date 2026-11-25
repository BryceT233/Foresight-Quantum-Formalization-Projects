/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Capacity/Capacity.lean: the informal coherent-information lower bound
and regularized capacity formula. We normalize the entropic side in qubits per use
and prove the operational statements for channels with an exact decoder and replacements.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.Blocking
public import FQFP.CQM.Qudit.Channel.Degradation.Basic
public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Exchange

/-!
# Coherent information per channel use

The block may have an arbitrary joint input, including entangled inputs. Its coherent
information is computed in nats, converted to qubits and divided by the number of uses.
The regularization is defined independently of achievable rates.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

variable {H K L M : Qudit}

/-- Independent local channels cannot increase mutual information. -/
theorem mutualInfo_map_tensor_le (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (ρ : Density (H ⊗ L)) : ((Φ.tensor Ψ).map ρ).mutualInfo ≤ ρ.mutualInfo := by
  rw [← Density.relativeEntropyReal_tensor_marginals, ← ρ.relativeEntropyReal_tensor_marginals,
    partialTraceRight_map_tensor, partialTraceLeft_map_tensor, ← map_tensor]
  exact (Φ.tensor Ψ).relativeEntropyReal_map_le _ _ ρ.absolutelyContinuous_tensor_marginals

/-- Reference-output mutual information adds the unchanged reference entropy to coherent
information. -/
lemma mutualInfo_map_purify (Φ : QuantumChannel H K) (ρ : Density H) :
    ((Φ.tensor (id H)).map (Density.pure ρ.purify)).mutualInfo =
      Φ.coherentInfo ρ + ρ.vonNeumannEntropy := by
  rw [Density.mutualInfo, partialTraceRight_map_tensor, Density.partialTraceRight_pure_purify,
    entropy_reference_output, coherentInfo]
  ring

/-- Postprocessing the receiver's system cannot increase coherent information. -/
theorem IsDegradableTo.coherentInfo_le {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    (h : Φ.IsDegradableTo Ψ) (ρ : Density H) : Ψ.coherentInfo ρ ≤ Φ.coherentInfo ρ := by
  obtain ⟨D, rfl⟩ := h
  have h := mutualInfo_map_tensor_le D (id H) ((Φ.tensor (id H)).map (Density.pure ρ.purify))
  rw [← map_comp, ← tensor_comp, id_comp, mutualInfo_map_purify, mutualInfo_map_purify] at h
  exact le_of_add_le_add_right h

/-- Coherent information of a block in qubits per use, for a specified joint input. -/
def coherentInfoRate (Φ : QuantumChannel H K) (n : ℕ) (ρ : Density (Qudit.tensorPower H n)) : ℝ :=
  (Φ.tensorPower n).coherentInfo ρ / Real.log 2 / (n + 1)

/-- The index zero represents one use of the channel. -/
@[simp] lemma coherentInfoRate_zero (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.coherentInfoRate 0 ρ = Φ.coherentInfo ρ / Real.log 2 := by
  change Φ.coherentInfo ρ / Real.log 2 / ((0 : ℕ) + 1 : ℝ) = _
  norm_num

private lemma log_finrank_per_use (H : Qudit) (n : ℕ) :
    Real.log (Module.finrank ℂ (Qudit.tensorPower H n).state) / Real.log 2 / (n + 1) =
      Real.logb 2 (Module.finrank ℂ H.state) := by
  rw [← Real.logb, finrank_tensorPower, Nat.cast_pow, Real.logb_pow, Nat.cast_add, Nat.cast_one]
  exact mul_div_cancel_left₀ _ (by positivity)

/-- Both the input and output dimensions bound the coherent information per use. -/
theorem coherentInfoRate_le_min_log_finrank (Φ : QuantumChannel H K) (n : ℕ)
    (ρ : Density (Qudit.tensorPower H n)) :
    Φ.coherentInfoRate n ρ ≤ min (Real.logb 2 (Module.finrank ℂ H.state))
      (Real.logb 2 (Module.finrank ℂ K.state)) := by
  have divide {x y : ℝ} (h : x ≤ y) :
      x / Real.log 2 / (n + 1) ≤ y / Real.log 2 / (n + 1) :=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h (by positivity)) (by positivity)
  rw [← log_finrank_per_use H n, ← log_finrank_per_use K n]
  exact le_min (divide (((Φ.tensorPower n).coherentInfo_le_input_entropy ρ).trans
    ρ.vonNeumannEntropy_le_log_finrank))
    (divide (((Φ.tensorPower n).coherentInfo_le_output_entropy ρ).trans
      ((Φ.tensorPower n).map ρ).vonNeumannEntropy_le_log_finrank))

/-- Supremum of coherent information in qubits per use over all nonempty blocks and inputs. -/
def regularizedCoherentInfo (Φ : QuantumChannel H K) : ℝ :=
  sSup {r | ∃ n ρ, Φ.coherentInfoRate n ρ = r}

/-- The regularization is the least upper bound of the block rates with zero adjoined,
including when the input space admits no states. -/
theorem isLUB_insert_zero_coherentInfoRate (Φ : QuantumChannel H K) :
    IsLUB (insert 0 {r | ∃ n ρ, Φ.coherentInfoRate n ρ = r}) Φ.regularizedCoherentInfo := by
  let rates := {r | ∃ n ρ, Φ.coherentInfoRate n ρ = r}
  change IsLUB (insert 0 rates) (sSup rates)
  rcases Set.eq_empty_or_nonempty rates with he | hn
  · simpa only [he, Real.sSup_empty, insert_empty_eq] using (isLUB_singleton (a := (0 : ℝ)))
  · obtain ⟨_, n, ρ, rfl⟩ := hn
    obtain ⟨i⟩ := ρ.spectrum.nonempty
    have hz : 0 ∈ rates := ⟨n, Density.pure (UnitState.ofBasis ρ.eigenbasis i), by
      simp [coherentInfoRate]⟩
    rw [Set.insert_eq_of_mem hz]
    refine isLUB_csSup ⟨0, hz⟩ ?_
    refine ⟨min (Real.logb 2 (Module.finrank ℂ H.state))
      (Real.logb 2 (Module.finrank ℂ K.state)), ?_⟩
    rintro _ ⟨j, σ, rfl⟩
    exact Φ.coherentInfoRate_le_min_log_finrank j σ

/-- Every normalized block value is a lower bound for the entropic supremum. -/
lemma coherentInfoRate_le_regularizedCoherentInfo (Φ : QuantumChannel H K) (n : ℕ)
    (ρ : Density (Qudit.tensorPower H n)) : Φ.coherentInfoRate n ρ ≤ Φ.regularizedCoherentInfo :=
  Φ.isLUB_insert_zero_coherentInfoRate.1 (Set.mem_insert_of_mem _ ⟨n, ρ, rfl⟩)

/-- A pure input gives zero coherent information; the empty supremum also has value zero. -/
lemma regularizedCoherentInfo_nonneg (Φ : QuantumChannel H K) : 0 ≤ Φ.regularizedCoherentInfo :=
  Φ.isLUB_insert_zero_coherentInfoRate.1 (Set.mem_insert ..)

/-- A single-use coding bound on each block channel implies the regularized operational
lower bound: flatten each block code and divide its rate by the number of physical uses. -/
theorem regularizedCoherentInfo_le_quantumCapacity_of_block_bound (Φ : QuantumChannel H K)
    (h : ∀ n (ρ : Density (Qudit.tensorPower H n)),
      (Φ.tensorPower n).coherentInfo ρ / Real.log 2 ≤ (Φ.tensorPower n).quantumCapacity) :
    Φ.regularizedCoherentInfo ≤ Φ.quantumCapacity := by
  apply Φ.isLUB_insert_zero_coherentInfoRate.2
  rintro _ (rfl | ⟨n, ρ, rfl⟩)
  · exact Φ.isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..)
  · exact (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
      ((h n ρ).trans (Φ.quantumCapacity_tensorPower_le n))

/-- Regularized coherent information obeys the same dimension bounds as operational capacity. -/
theorem regularizedCoherentInfo_le_min_log_finrank (Φ : QuantumChannel H K) :
    Φ.regularizedCoherentInfo ≤ min (Real.logb 2 (Module.finrank ℂ H.state))
      (Real.logb 2 (Module.finrank ℂ K.state)) := by
  apply Φ.isLUB_insert_zero_coherentInfoRate.2
  rintro _ (rfl | ⟨n, ρ, rfl⟩)
  · exact (Φ.isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..)).trans
      Φ.quantumCapacity_le_min_log_finrank
  · exact Φ.coherentInfoRate_le_min_log_finrank n ρ

/-- Receiver postprocessing acts independently on each site of a block. -/
lemma IsDegradableTo.tensorPower {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    (h : Φ.IsDegradableTo Ψ) (n : ℕ) : (Φ.tensorPower n).IsDegradableTo (Ψ.tensorPower n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact h.tensor ih

/-- Receiver postprocessing cannot increase the regularized coherent information. -/
theorem IsDegradableTo.regularizedCoherentInfo_le {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    (h : Φ.IsDegradableTo Ψ) : Ψ.regularizedCoherentInfo ≤ Φ.regularizedCoherentInfo := by
  apply Ψ.isLUB_insert_zero_coherentInfoRate.2
  rintro _ (rfl | ⟨n, ρ, rfl⟩)
  · exact Φ.regularizedCoherentInfo_nonneg
  · apply le_trans _ (Φ.coherentInfoRate_le_regularizedCoherentInfo n ρ)
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right ((h.tensorPower n).coherentInfo_le ρ) (by positivity))
      (by positivity)

/-- A noiseless channel attains its regularized coherent information in one use. -/
theorem regularizedCoherentInfo_id (H : Qudit) :
    (id H).regularizedCoherentInfo = Real.logb 2 (Module.finrank ℂ H.state) := by
  refine le_antisymm ((id H).regularizedCoherentInfo_le_min_log_finrank.trans (min_le_left ..)) ?_
  by_cases h : Module.finrank ℂ H.state = 0
  · simpa [h] using (id H).regularizedCoherentInfo_nonneg
  · simpa [Real.logb] using
      (id H).coherentInfoRate_le_regularizedCoherentInfo 0 (Density.maximallyMixed H h)

/-- A maximally mixed noiseless block transmits the same number of qubits per site at every
positive block length. -/
theorem coherentInfoRate_id_maximallyMixed (H : Qudit) (n : ℕ)
    (h : Module.finrank ℂ (Qudit.tensorPower H n).state ≠ 0) :
    (id H).coherentInfoRate n (Density.maximallyMixed _ h) =
      Real.logb 2 (Module.finrank ℂ H.state) := by
  rw [coherentInfoRate, tensorPower_id, coherentInfo_id, Density.vonNeumannEntropy_maximallyMixed,
    log_finrank_per_use]

/-- A channel admitting exact recovery of every input satisfies the regularized capacity formula. -/
theorem quantumCapacity_eq_regularizedCoherentInfo_of_recovery {Φ : QuantumChannel H K}
    (h : Φ.IsDegradableTo (id H)) : Φ.quantumCapacity = Φ.regularizedCoherentInfo := by
  have hsim : Φ.Emulates (id H) := by
    obtain ⟨D, hD⟩ := h
    exact ⟨id H, D, by rwa [comp_id]⟩
  have hid := isDegradableTo_of_id Φ
  rw [le_antisymm (Φ.quantumCapacity_le_min_log_finrank.trans (min_le_left ..))
    ((quantumCapacity_id H) ▸ hsim.quantumCapacity_le)]
  rw [← regularizedCoherentInfo_id]
  exact le_antisymm h.regularizedCoherentInfo_le hid.regularizedCoherentInfo_le

/-- For an exactly recoverable channel, one-use coherent information in qubits bounds
operational capacity from below at every input. -/
theorem coherentInfo_div_log_two_le_quantumCapacity_of_recovery {Φ : QuantumChannel H K}
    (h : Φ.IsDegradableTo (id H)) (ρ : Density H) :
    Φ.coherentInfo ρ / Real.log 2 ≤ Φ.quantumCapacity := by
  simpa only [coherentInfoRate_zero, quantumCapacity_eq_regularizedCoherentInfo_of_recovery h]
    using Φ.coherentInfoRate_le_regularizedCoherentInfo 0 ρ

/-- Antidegradable channels satisfy the one-use capacity lower bound at every input. -/
theorem IsAntidegradable.coherentInfo_div_log_two_le_quantumCapacity {Φ : QuantumChannel H K}
    (h : Φ.IsAntidegradable) (ρ : Density H) :
    Φ.coherentInfo ρ / Real.log 2 ≤ Φ.quantumCapacity := by
  have hle := h.coherentInfo_le ρ
  rw [coherentInfo_complementary] at hle
  exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)).trans
    (Φ.isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..))

/-- A replacement channel has zero regularized coherent information. -/
theorem regularizedCoherentInfo_replacement (H : Qudit) (σ : Density K) :
    (replacement H σ).regularizedCoherentInfo = 0 := by
  let D : QuantumChannel H (𝟙_ Qudit) := CausalQudit.discard ⟨H⟩
  refine le_antisymm ((isDegradableTo_replacement D σ).regularizedCoherentInfo_le.trans ?_)
    (regularizedCoherentInfo_nonneg _)
  simpa only [state_tensorUnit, Module.finrank_self, Nat.cast_one, Real.logb_one] using
    D.regularizedCoherentInfo_le_min_log_finrank.trans (min_le_right ..)

end Qudit.QuantumChannel
