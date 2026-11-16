/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Complementary
public import FQFP.CQM.Qudit.Channel.Composite
public import FQFP.CQM.Qudit.Channel.MeasurePrepare

/-!
# Degradation of quantum channels

`Φ.IsDegradableTo Ψ` means that a channel applied after `Φ` realizes `Ψ`, as an equality
on all operators. Outputs may have different dimensions. The explicit preorder on channels
with a fixed input orders less informative channels below more informative ones.
Degradability and antidegradability use the chosen complementary channel.

## Main definitions

* `Qudit.QuantumChannel.IsDegradableTo`: simulation of one channel by postprocessing another.
* `Qudit.QuantumChannel.IsDegradable`: simulation of the complementary output from the main output.
* `Qudit.QuantumChannel.IsAntidegradable`: simulation in the reverse direction.
* `Qudit.QuantumChannel.degradablePreorder`: the explicit postprocessing preorder with fixed input.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K L M N P : Qudit}

/-- A channel degrades to another when quantum postprocessing realizes the latter. -/
def IsDegradableTo (Φ : QuantumChannel H K) (Ψ : QuantumChannel H L) : Prop :=
  ∃ D : QuantumChannel K L, D.comp Φ = Ψ

/-- The reverse of channel degradation. -/
abbrev IsAntidegradableTo (Φ : QuantumChannel H K) (Ψ : QuantumChannel H L) : Prop :=
  Ψ.IsDegradableTo Φ

/-- A channel is degradable if its output can simulate its chosen environment output. -/
def IsDegradable (Φ : QuantumChannel H K) : Prop := Φ.IsDegradableTo Φ.complementary

/-- A channel is antidegradable if its chosen environment output can simulate its output. -/
def IsAntidegradable (Φ : QuantumChannel H K) : Prop := Φ.complementary.IsDegradableTo Φ

/-- Every channel degrades to itself by identity postprocessing. -/
lemma IsDegradableTo.refl (Φ : QuantumChannel H K) : Φ.IsDegradableTo Φ :=
  ⟨id K, id_comp Φ⟩

/-- Postprocessings compose, even when all three output dimensions differ. -/
lemma IsDegradableTo.trans {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    {Χ : QuantumChannel H M} (h : Φ.IsDegradableTo Ψ) (h' : Ψ.IsDegradableTo Χ) :
    Φ.IsDegradableTo Χ := by
  obtain ⟨D, rfl⟩ := h
  obtain ⟨D', rfl⟩ := h'
  exact ⟨D'.comp D, comp_assoc _ _ _⟩

/-- Preprocessing both channels preserves their degradation relation. -/
lemma IsDegradableTo.comp {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    (h : Φ.IsDegradableTo Ψ) (Γ : QuantumChannel M H) :
    (Φ.comp Γ).IsDegradableTo (Ψ.comp Γ) := by
  obtain ⟨D, rfl⟩ := h
  exact ⟨D, (comp_assoc _ _ _).symm⟩

/-- Independent degradations give a degradation of product channels. -/
lemma IsDegradableTo.tensor {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    {Φ' : QuantumChannel M N} {Ψ' : QuantumChannel M P}
    (h : Φ.IsDegradableTo Ψ) (h' : Φ'.IsDegradableTo Ψ') :
    (Φ.tensor Φ').IsDegradableTo (Ψ.tensor Ψ') := by
  obtain ⟨D, rfl⟩ := h
  obtain ⟨D', rfl⟩ := h'
  exact ⟨D.tensor D', (tensor_comp _ _ _ _).symm⟩

/-- The identity channel can simulate every channel with its input. -/
lemma isDegradableTo_of_id (Φ : QuantumChannel H K) : (id H).IsDegradableTo Φ :=
  ⟨Φ, comp_id Φ⟩

/-- A replacement channel after any channel is the same replacement channel. -/
lemma replacement_comp (Φ : QuantumChannel H K) (σ : Density L) :
    (replacement K σ).comp Φ = replacement H σ := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change (replacement K σ).toSuperoperator (Φ.toSuperoperator A) = _
  rw [replacement_apply, Φ.tracePreserving, replacement_apply]

/-- Every channel can be degraded to any fixed-state replacement channel. -/
lemma isDegradableTo_replacement (Φ : QuantumChannel H K) (σ : Density L) :
    Φ.IsDegradableTo (replacement H σ) := ⟨replacement K σ, replacement_comp Φ σ⟩

/-- The identity channel is degradable. -/
lemma isDegradable_id (H : Qudit) : (id H).IsDegradable :=
  isDegradableTo_of_id _

/-- Every replacement channel is antidegradable, including replacement by a mixed state. -/
lemma isAntidegradable_replacement (H : Qudit) (σ : Density K) :
    (replacement H σ).IsAntidegradable := isDegradableTo_replacement _ σ

/-- Channels with a fixed input, ordered by quantum postprocessing. The output qudit
is bundled so the relation compares different output dimensions. This is deliberately
an explicit preorder rather than a global instance on channels. -/
@[instance_reducible]
def degradablePreorder (H : Qudit) : Preorder (Σ K : Qudit, QuantumChannel H K) where
  le Φ Ψ := Ψ.2.IsDegradableTo Φ.2
  le_refl Φ := IsDegradableTo.refl Φ.2
  le_trans _ _ _ h h' := h'.trans h

end

end Qudit.QuantumChannel
