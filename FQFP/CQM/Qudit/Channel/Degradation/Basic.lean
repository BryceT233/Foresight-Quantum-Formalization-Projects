/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for degradability, antidegradability and the degradation preorder.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean
QuantumInfo/Channels/DegradableOrder.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.Postprocessing
public import FQFP.CQM.Qudit.Channel.Dilation.Complementary
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

/-- Channel degradation is postprocessing in the category of causal processes. -/
lemma isDegradableTo_iff (Φ : QuantumChannel H K) (Ψ : QuantumChannel H L) :
    Φ.IsDegradableTo Ψ ↔ CQM.IsDegradableTo Φ.asHom Ψ.asHom := Iff.rfl

/-- The reverse of channel degradation. -/
abbrev IsAntidegradableTo (Φ : QuantumChannel H K) (Ψ : QuantumChannel H L) : Prop :=
  Ψ.IsDegradableTo Φ

/-- A channel is degradable if its output can simulate its chosen environment output. -/
def IsDegradable (Φ : QuantumChannel H K) : Prop := Φ.IsDegradableTo Φ.complementary

/-- A channel is antidegradable if its chosen environment output can simulate its output. -/
def IsAntidegradable (Φ : QuantumChannel H K) : Prop := Φ.complementary.IsDegradableTo Φ

/-- Every channel degrades to itself by identity postprocessing. -/
lemma IsDegradableTo.refl (Φ : QuantumChannel H K) : Φ.IsDegradableTo Φ :=
  CQM.IsDegradableTo.refl Φ.asHom

/-- Postprocessings compose, even when all three output dimensions differ. -/
lemma IsDegradableTo.trans {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    {Χ : QuantumChannel H M} (h : Φ.IsDegradableTo Ψ) (h' : Ψ.IsDegradableTo Χ) :
    Φ.IsDegradableTo Χ :=
  ((isDegradableTo_iff _ _).mp h).trans ((isDegradableTo_iff _ _).mp h')

/-- Preprocessing both channels preserves their degradation relation. -/
lemma IsDegradableTo.comp {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    (h : Φ.IsDegradableTo Ψ) (Γ : QuantumChannel M H) :
    (Φ.comp Γ).IsDegradableTo (Ψ.comp Γ) :=
  ((isDegradableTo_iff _ _).mp h).precomp Γ.asHom

/-- Independent degradations give a degradation of product channels. -/
lemma IsDegradableTo.tensor {Φ : QuantumChannel H K} {Ψ : QuantumChannel H L}
    {Φ' : QuantumChannel M N} {Ψ' : QuantumChannel M P}
    (h : Φ.IsDegradableTo Ψ) (h' : Φ'.IsDegradableTo Ψ') :
    (Φ.tensor Φ').IsDegradableTo (Ψ.tensor Ψ') :=
  ((isDegradableTo_iff _ _).mp h).tensor ((isDegradableTo_iff _ _).mp h')

/-- The identity channel can simulate every channel with its input. -/
lemma isDegradableTo_of_id (Φ : QuantumChannel H K) : (id H).IsDegradableTo Φ :=
  CQM.isDegradableTo_of_id Φ.asHom

/-- A replacement channel after any channel is the same replacement channel. -/
lemma replacement_comp (Φ : QuantumChannel H K) (σ : Density L) :
    (replacement K σ).comp Φ = replacement H σ := by
  change Φ.asHom ≫ SemiCartesianMonoidalCategory.toUnit _ ≫ σ.toState = _
  rw [SemiCartesianMonoidalCategory.comp_toUnit_assoc]
  rfl

/-- Every channel can be degraded to any fixed-state replacement channel. -/
lemma isDegradableTo_replacement (Φ : QuantumChannel H K) (σ : Density L) :
    Φ.IsDegradableTo (replacement H σ) :=
  CQM.isDegradableTo_toUnit_comp Φ.asHom σ.toState

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
