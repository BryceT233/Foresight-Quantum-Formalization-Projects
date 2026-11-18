/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.VonNeumann.Composite
public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.State.Purification.Basic

/-!
# Coherent information of a state through a channel

The channel acts on the left subsystem of the existing purification. Coherent
information is output entropy minus joint output-reference entropy, following
Watrous, *The Theory of Quantum Information*, Definition 8.14 (8.39), with natural
logarithms instead of base two. No optimization over input states is included.

## Main definitions and results

* `Qudit.QuantumChannel.coherentInfo`: output entropy minus joint output-reference entropy.
* `Qudit.QuantumChannel.coherentInfo_id`: the identity channel retains the input entropy.
* `Qudit.QuantumChannel.coherentInfo_pure`: pure inputs have zero coherent information.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K : Qudit}

/-- Coherent information in nats: output entropy minus joint output-reference entropy. -/
def coherentInfo (Φ : QuantumChannel H K) (ρ : Density H) : ℝ :=
  (Φ.map ρ).vonNeumannEntropy -
    ((Φ.tensor (id H)).map (Density.pure ρ.purify)).vonNeumannEntropy

/-- The identity channel transmits the entire input entropy as coherent information. -/
@[simp]
lemma coherentInfo_id (ρ : Density H) : (id H).coherentInfo ρ = ρ.vonNeumannEntropy := by
  have hid : (id H).tensor (id H) = id (H ⊗ H) := by
    apply QuantumChannel.ext
    exact Superoperator.tensor_id_id H H
  simp [coherentInfo, hid, map_id]

/-- A pure input has zero coherent information through every channel. -/
@[simp]
lemma coherentInfo_pure (Φ : QuantumChannel H K) (ψ : UnitState H) :
    Φ.coherentInfo (Density.pure ψ) = 0 := by
  obtain ⟨φ, hφ⟩ := (Density.pure ψ).purify.exists_eq_tensor_of_partialTraceRight_eq_pure ψ
    (Density.partialTraceRight_pure_purify _)
  rw [coherentInfo, hφ, ← Density.tensor_pure, map_tensor, map_id,
    Density.vonNeumannEntropy_tensor, Density.vonNeumannEntropy_pure, add_zero, sub_self]

/-- Coherent information cannot exceed the entropy of the channel output. -/
lemma coherentInfo_le_output_entropy (Φ : QuantumChannel H K) (ρ : Density H) :
    Φ.coherentInfo ρ ≤ (Φ.map ρ).vonNeumannEntropy :=
  sub_le_self _ (Density.vonNeumannEntropy_nonneg _)

end

end Qudit.QuantumChannel
