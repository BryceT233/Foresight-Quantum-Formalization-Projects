/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.Dimension

/-!
# Reblocking operational quantum codes

A code using a block channel repeatedly can be used directly on its individual sites.
Reassociation of the tensor factors transports both encoder and decoder exactly.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

variable {H K L M S T : Qudit}

/-- Independent uses of an identity channel give the identity on the entire register. -/
lemma tensorPower_id (H : Qudit) (n : ℕ) : (id H).tensorPower n = id (Qudit.tensorPower H n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((id H).tensor ((id H).tensorPower n)) = _
    exact (congrArg ((id H).tensor ·) ih).trans (tensor_id_id H _)

/-- Reassociating three parallel channels is an exact simulation. -/
lemma emulates_tensor_assoc (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (Γ : QuantumChannel S T) :
    (Φ.tensor (Ψ.tensor Γ)).Emulates ((Φ.tensor Ψ).tensor Γ) := by
  let i := α_ (⟨H⟩ : CausalQudit) ⟨L⟩ ⟨S⟩
  let j := α_ (⟨K⟩ : CausalQudit) ⟨M⟩ ⟨T⟩
  refine ⟨i.hom, j.inv, ?_⟩
  change (i.hom ≫ (Φ.asHom ⊗ₘ (Ψ.asHom ⊗ₘ Γ.asHom))) ≫ j.inv = _
  rw [← associator_naturality, Category.assoc, j.hom_inv_id, Category.comp_id]
  rfl

/-- A flat register simulates two consecutive blocks, with their original tensor bracketing. -/
lemma tensorPower_emulates_tensor (Φ : QuantumChannel H K) (a b : ℕ) :
    (Φ.tensorPower (a + b + 1)).Emulates ((Φ.tensorPower a).tensor (Φ.tensorPower b)) := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    exact Emulates.refl _
  | succ a ih =>
    rw [Nat.succ_add]
    exact ((Emulates.refl Φ).tensor ih).trans (emulates_tensor_assoc Φ _ _)

/-- Each use of a block channel costs exactly its number of physical sites. -/
lemma tensorPower_emulates_blocks (Φ : QuantumChannel H K) (n m : ℕ) :
    ∃ j, j + 1 = (n + 1) * (m + 1) ∧
      (Φ.tensorPower j).Emulates ((Φ.tensorPower n).tensorPower m) := by
  induction m with
  | zero => exact ⟨n, by simp, Emulates.refl _⟩
  | succ m ih =>
    obtain ⟨j, hj, he⟩ := ih
    refine ⟨n + j + 1, ?_, (Φ.tensorPower_emulates_tensor n j).trans ((Emulates.refl _).tensor he)⟩
    rw [Nat.mul_succ, ← hj]
    lia

/-- A rate achievable per block gives its quotient by the block length per physical use. -/
theorem AchievesRate.of_tensorPower {Φ : QuantumChannel H K} {R : ℝ} {n : ℕ}
    (h : (Φ.tensorPower n).AchievesRate R) : Φ.AchievesRate (R / (n + 1)) := by
  intro ε hε
  obtain ⟨m, d, Ψ, he, hR, hδ⟩ := h ε hε
  obtain ⟨j, hj, hj'⟩ := Φ.tensorPower_emulates_blocks n m
  refine ⟨j, d, Ψ, hj'.trans he, ?_, hδ⟩
  have hlen : (j : ℝ) + 1 = (n + 1 : ℝ) * (m + 1 : ℝ) := by exact_mod_cast hj
  rwa [hlen, ← mul_assoc, div_mul_cancel₀ _ (by positivity)]

/-- A block of parallel uses has at most the sum of the individual operational capacities. -/
theorem quantumCapacity_tensorPower_le (Φ : QuantumChannel H K) (n : ℕ) :
    (Φ.tensorPower n).quantumCapacity ≤ Φ.quantumCapacity * (n + 1) := by
  apply (Φ.tensorPower n).isLUB_insert_zero_achievesRate.2
  rintro R (rfl | h)
  · exact mul_nonneg (Φ.isLUB_insert_zero_achievesRate.1 (Set.mem_insert ..)) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mp
    exact le_csSup Φ.bddAbove_achievesRate (AchievesRate.of_tensorPower h)

end Qudit.QuantumChannel
