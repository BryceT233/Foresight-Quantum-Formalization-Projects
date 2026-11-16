/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Complementary

/-!
# Quantum channels acting on purifications

A single isometry lifts a channel to all input purifications with a fixed reference
system. Its output environment groups the channel environment and the old reference
on the right, so the existing `Density.partialTraceRight` recovers the channel output.

## Main results

* `Qudit.QuantumChannel.exists_purification_map`: a common isometry lifts a channel on every input
  purification with a fixed reference.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K : Qudit}

/-- A common isometry sends every input purification to a purification of its channel output.
The same map works for all input states and preserves their vector inner products. -/
theorem exists_purification_map (Φ : QuantumChannel H K) (R : Qudit) :
    ∃ (n : ℕ) (W : H ⊗ R ⟶ K ⊗ (std n ⊗ R)) (_ : IsIsometry W),
      ∀ ψ : UnitState (H ⊗ R),
        (Density.pure (ψ.map W)).partialTraceRight =
          Φ.map (Density.pure ψ).partialTraceRight :=
  ⟨Module.finrank ℂ K.state * Module.finrank ℂ H.state, Φ.dilation.lift R,
    inferInstance, Φ.dilation.partialTraceRight_pure_lift⟩

end

end Qudit.QuantumChannel
