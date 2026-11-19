/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for source derivations for the Fourier circuit on arbitrary inputs.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/QFTArbitrary.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierOperator
public import FQFP.QuantumProgram.Logic.CountedUnitary

/-!
# Total correctness of the counted Fourier circuit on superpositions

Gate-prefix vectors give pure-state invariants for the ladder, stage, and reversal loops.
The operator equality identifies the final assertion with the independently specified DFT.
-/

@[expose] public section

open CategoryTheory Qudit

namespace QuantumProgram.FourierIteration

noncomputable section

variable {n : ℕ} [NeZero n]

/-- A ladder transports an arbitrary stage-dependent input by its controlled-phase gates. -/
theorem sourceDeriv_ladder_map (v : ℕ → UnitState (Memory n)) (P : Store → Prop)
    (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) P) (ladder n)
      (.ofEffect (fun σ => Assertion.pure
        (UnitaryProgram.prefixState (rungGate n σ.1) (v σ.1) (n - 1 - σ.1)) σ) P) := by
  let w := fun k => UnitaryProgram.prefixState (rungGate n k) (v k)
  have d := count_rungs P hP (fun k t => Assertion.pure (w k t) ()) (by
    apply SourceDerivTot.unitary_pure (Store := Store) (k := 2) _ _
      (fun σ => w σ.1 σ.2) (fun σ => w σ.1 (σ.2 + 1)) (fun _ h => rung_injective h.2)
    exact fun σ _ => UnitaryProgram.prefixState_step _ _ _)
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ h => ⟨h.1, le_rfl⟩)

private theorem sourceDeriv_stage_map (v : ℕ → UnitState (Memory n)) (P : ℕ → Prop) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) fun σ => P σ.1)
      ((hadamard n).seq (ladder n))
      (.ofEffect (fun σ => Assertion.pure (UnitState.map (stageProgram n σ.1).denoteHom
        (v σ.1)) σ) fun σ => P σ.1) := by
  let w := fun k => UnitState.map (hadamardGate n k).denoteHom (v k)
  apply SourceDerivTot.seq _ (sourceDeriv_ladder_map w (fun σ => P σ.1) (fun _ _ => Iff.rfl))
  exact SourceDerivTot.unitary_pure (Store := Store) _ _ (fun σ => v σ.1) (fun σ => w σ.1)
    (fun _ _ => Function.injective_of_subsingleton _) (fun _ _ => rfl)

/-- The counted stage loop acts on any unit input by the full stage sequence. -/
theorem sourceDeriv_iteration_map (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (iteration n)
      (.ofEffect (Assertion.pure (UnitaryProgram.prefixState (stageProgram n) v n))
        fun _ => True) := by
  apply SourceDerivTot.countedUnitary stageCounter n _ (stageProgram n) v
  · exact fun w => sourceDeriv_stage_map w (· < n)
  · exact fun z => stage_identity fun k => k < n ∧ ((n - k : ℕ) : ℤ) = z

/-- The counted reversal applies the mirror gates to arbitrary, possibly entangled input. -/
theorem sourceDeriv_reversal_map (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (reversal n)
      (.ofEffect (Assertion.pure (UnitaryProgram.prefixState (mirrorGate n) v (n / 2)))
        fun _ => True) := by
  apply SourceDerivTot.countedUnitary stageCounter (n / 2) _ (mirrorGate n) v
  · intro w
    exact SourceDerivTot.unitary_pure (Store := Store) _ _ (fun σ => w σ.1)
      (fun σ => UnitState.map (mirrorGate n σ.1).denoteHom (w σ.1))
      (fun _ h => swap_injective h) (fun _ _ => rfl)
  · exact fun _ => SourceDerivTot.unitary_identity _ _ _ (fun _ h => swap_injective h.1)

/-- Source total correctness of the original counted command with the DFT output assertion. -/
theorem sourceDeriv_circuit_qftOp (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (circuit n)
      (.ofEffect (Assertion.pure (UnitState.map (qftGate n) v))
        fun _ => True) := by
  let w := UnitaryProgram.prefixState (stageProgram n) v n
  have hv : UnitaryProgram.prefixState (mirrorGate n) w (n / 2) =
      UnitState.map (qftGate n) v :=
    Subtype.ext (qftCirOp_apply_eq n v.val)
  rw [← hv]
  exact .seq (sourceDeriv_iteration_map v) (sourceDeriv_reversal_map w)

/-- The counted circuit terminates with the DFT of any normalized input in any initial store. -/
theorem validTot_circuit_qftOp (v : UnitState (Memory n)) :
    validTot (Assertion.pure v) (circuit n)
      (Assertion.pure (UnitState.map (qftGate n) v)) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_circuit_qftOp v).sound

end

end QuantumProgram.FourierIteration
