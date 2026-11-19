/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for total correctness of the counted inverse Fourier circuit.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/InverseQFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.InverseFourier

/-!
# Total correctness of the counted inverse Fourier circuit

The invariant of the inner loop is the input acted on by the negative-angle rungs
already executed. The outer loop then composes these ladders with the Hadamards in
reverse stage order. The resulting triple applies to arbitrary unit vectors.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram.InverseFourier

open FourierIteration

noncomputable section

variable {n : ℕ} [NeZero n]

/-- The two wires selected by an active inverse rung are distinct. -/
theorem inverseRung_injective {σ : Store} (hk : σ.1 < n) (ht : σ.2 < σ.1) :
    Function.Injective ![control n (n - 1 - σ.1), control n (n - 1 - σ.2)] := by
  have hlt : control n (n - 1 - σ.1) < control n (n - 1 - σ.2) := by
    change (n - 1 - σ.1) % n < (n - 1 - σ.2) % n
    rw [Nat.mod_eq_of_lt (by lia : n - 1 - σ.1 < n), Nat.mod_eq_of_lt (by lia : n - 1 - σ.2 < n)]
    lia
  have hne := hlt.ne
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

private theorem counted_rungs (P : Store → Prop) (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ)
    (hk : ∀ σ, P σ → σ.1 < n)
    (J : ℕ → ℕ → Set.Icc (0 : Operator (Memory n)) 1)
    (step : let active := fun σ : Store => P σ ∧ σ.2 < σ.1
      SourceDerivTot (.ofEffect (fun σ => J σ.1 σ.2) active) (inverseRung n)
        (.ofEffect (fun σ => J σ.1 (σ.2 + 1)) active)) :
    SourceDerivTot (.ofEffect (fun σ => J σ.1 0) P) (inverseLadder n)
      (.ofEffect (fun σ => J σ.1 σ.1) fun σ => P σ ∧ σ.2 = σ.1) :=
  SourceDerivTot.countedGateFamily rungCounter Prod.fst P hP
    (fun _ _ => rfl) (fun t σ => J σ.1 t) (fun _ _ _ => rfl) _ _
    (fun σ h ht => inverseRung_injective (hk σ h) ht) step

/-- The inner counter runs exactly the inverted rungs of the selected stage. -/
theorem sourceDeriv_inverseLadder (v : ℕ → UnitState (Memory n)) (P : Store → Prop)
    (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ) (hk : ∀ σ, P σ → σ.1 < n) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) P)
      (inverseLadder n) (.ofEffect (fun σ => Assertion.pure
        (UnitaryProgram.prefixState (inverseRungGate n σ.1) (v σ.1) σ.1) σ)
          fun σ => P σ ∧ σ.2 = σ.1) := by
  let w := fun k => UnitaryProgram.prefixState (inverseRungGate n k) (v k)
  apply counted_rungs P hP hk (fun k t => Assertion.pure (w k t) ())
  exact SourceDerivTot.unitary_pure (Store := Store) _ _
    (fun σ => w σ.1 σ.2) (fun σ => w σ.1 (σ.2 + 1))
    (fun σ h => inverseRung_injective (hk σ h.1) h.2)
    (fun _ _ => UnitaryProgram.prefixState_step ..)

private theorem stage_step (v : ℕ → UnitState (Memory n)) :
    let active := fun σ : Store => σ.1 < n
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) active)
      ((inverseLadder n).seq (inverseHadamard n))
      (.ofEffect (fun σ => Assertion.pure
        (UnitState.map (inverseStageProgram n σ.1).denoteHom (v σ.1)) σ) active) := by
  let w := fun k => UnitaryProgram.prefixState (inverseRungGate n k) (v k) k
  apply SourceDerivTot.seq (sourceDeriv_inverseLadder v (fun σ => σ.1 < n)
    (fun _ _ => Iff.rfl) (fun _ h => h))
  refine .conseq ?_ (SourceDerivTot.unitary_pure (Store := Store) (k := 1) _ _
    (φ := fun σ => σ.1 < n) (fun σ => w σ.1) (fun σ => UnitState.map
      (hadamardGate n (n - 1 - σ.1)).denoteHom (w σ.1))
    (fun _ _ => Function.injective_of_subsingleton _) (fun _ _ => rfl)) ?_
  · exact fun _ h => ⟨h.1, le_rfl⟩
  · exact fun _ h => ⟨h, le_rfl⟩

private theorem stage_identity (P : ℕ → Prop) (hk : ∀ k, P k → k < n) :
    let A := CQAssertion.ofEffect Assertion.identity (fun σ : Store => P σ.1)
    SourceDerivTot A ((inverseLadder n).seq (inverseHadamard n)) A := by
  have d := counted_rungs (n := n) (fun σ => P σ.1) (fun _ _ => Iff.rfl)
    (fun σ => hk σ.1) (fun _ _ => Assertion.identity ())
    (SourceDerivTot.unitary_identity _ _ _ (fun σ h => inverseRung_injective (hk σ.1 h.1) h.2))
  apply SourceDerivTot.seq d
  refine .conseq ?_ (SourceDerivTot.unitary_identity (k := 1) _ _ (fun σ : Store => P σ.1)
    (fun _ _ => Function.injective_of_subsingleton _)) ?_
  · exact fun _ h => ⟨h.1, le_rfl⟩
  · exact fun _ h => ⟨h, le_rfl⟩

/-- The outer counted loop undoes the stages in order from the rightmost to the leftmost wire. -/
theorem sourceDeriv_inverseIteration (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (inverseIteration n)
      (.ofEffect (Assertion.pure (UnitaryProgram.prefixState (inverseStageProgram n) v n))
        fun _ => True) := by
  apply SourceDerivTot.countedUnitary stageCounter n _ (inverseStageProgram n) v
  · exact stage_step
  · intro z
    exact stage_identity (fun k => k < n ∧ ((n - k : ℕ) : ℤ) = z) (fun _ h => h.1)

/-- The counted inverse circuit establishes the inverse-DFT assertion in every initial store. -/
theorem sourceDeriv_inverseCircuit (v : UnitState (Memory n)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (inverseCircuit n)
      (.ofEffect (Assertion.pure (UnitState.map (qftGate n)† v)) fun _ => True) := by
  let w := UnitaryProgram.prefixState (mirrorGate n) v (n / 2)
  have hu : UnitaryProgram.prefixState (inverseStageProgram n) w n =
      UnitState.map (qftGate n)† v :=
    Subtype.ext (LinearMap.congr_fun iqftRevCirOp_eq_iqftOp v.val)
  rw [← hu]
  exact .seq (sourceDeriv_reversal_map v) (sourceDeriv_inverseIteration w)

/-- Total correctness of the inverse QFT on every normalized input, including superpositions. -/
theorem validTot_inverseCircuit (v : UnitState (Memory n)) :
    validTot (Assertion.pure v) (inverseCircuit n)
      (Assertion.pure (UnitState.map (qftGate n)† v)) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_inverseCircuit v).sound

/-- The Fourier phase product decodes to its original big-endian bit word in the counted circuit. -/
theorem sourceDeriv_decode (x : Fin n → Fin 2) :
    SourceDerivTot (.ofEffect (Assertion.pure (fourierState x)) fun _ => True) (inverseCircuit n)
      (.ofEffect (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i)))
        fun _ => True) := by
  have hx : UnitState.map (qftGate n)† (fourierState x) =
      product (fun i => UnitState.ofBasis (ZBasis 2) (x i)) := by
    exact Subtype.ext (iqftOp_product_phaseState x)
  simpa only [hx] using sourceDeriv_inverseCircuit (fourierState x)

/-- The decoded computational word is the total-correctness postcondition. -/
theorem validTot_decode (x : Fin n → Fin 2) :
    validTot (Assertion.pure (fourierState x)) (inverseCircuit n)
      (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_decode x).sound

end

end QuantumProgram.InverseFourier
