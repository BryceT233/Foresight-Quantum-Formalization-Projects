/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for inverse Fourier decoding with a read-only classical input.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/InverseQFTClassicalTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.InverseFourierCorrectness
public import FQFP.QuantumProgram.StoreLens

/-!
# Inverse Fourier transform with a read-only classical word

The counters occupy the first component of the store. The reversal and inverse stages
track product states determined by the word in the second component throughout execution.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.FourierClassical

open FourierIteration InverseFourier

noncomputable section

/-- Two writable loop counters and the read-only big-endian word. -/
abbrev Store (n : ℕ) := FourierIteration.Store × (Fin n → Fin 2)

variable {n : ℕ}

/-- The computational basis assertion selected by the stored word. -/
def basisAssertion (n : ℕ) : Assertion (Store n) (Memory n) := fun σ =>
  Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (σ.2 i)) σ

/-- The Fourier assertion selected by the stored word, including the empty word. -/
def fourierAssertion (n : ℕ) : Assertion (Store n) (Memory n) := fun σ =>
  Assertion.pure (UnitState.map (qftGate n)
    (product fun i => UnitState.ofBasis (ZBasis 2) (σ.2 i))) σ

/-- Fixing the stored word recovers the basis assertion on the original two-counter store. -/
theorem basisAssertion_specialize (c : FourierIteration.Store) (x : Fin n → Fin 2) :
    basisAssertion n (c, x) = Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))
      c := rfl

/-- Fixing the stored word selects its normalized DFT at every width. -/
theorem fourierAssertion_specialize (c : FourierIteration.Store) (x : Fin n → Fin 2) :
    fourierAssertion n (c, x) = Assertion.pure (UnitState.map (qftGate n)
      (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) c := rfl

/-- The inverse precondition has expectation one on the corresponding normalized Fourier input. -/
theorem fourierAssertion_expectation (σ : Store n) :
    (Density.pure (UnitState.map (qftGate n)
      (product fun i => UnitState.ofBasis (ZBasis 2) (σ.2 i)))).expectation
        (fourierAssertion n σ) = 1 := by
  simp only [Density.expectation, Density.expectationComplex, fourierAssertion, Assertion.pure,
    Density.pure_mul_self, Density.trace_one, Complex.one_re]

variable [NeZero n]

/-- At each store the Fourier assertion is the projector onto its suffix-phase product. -/
theorem fourierAssertion_apply (σ : Store n) :
    fourierAssertion n σ = Assertion.pure (fourierState σ.2) σ := by
  have h := qftOp_basis σ.2
  rw [registerBasis_apply] at h
  exact congrArg (fun v => Assertion.pure v σ) (Subtype.ext h)

/-- Run the original inverse circuit on the two counters of the extended store. -/
def inverseCircuit (n : ℕ) [NeZero n] : Command (Store n) (Fin n) (Memory n) :=
  (InverseFourier.inverseCircuit n).mapStore StoreLens.fst

/-- The inverse circuit preserves every bit of the classical word at every write. -/
theorem inverseCircuit_preserves_word :
    (inverseCircuit n).PreservesParameters Prod.snd :=
  Command.preservesParameters_mapStore _ _ _ fun _ _ => rfl

private abbrev stage (n : ℕ) : CounterLens (Store n) :=
  stageCounter.pullback StoreLens.fst fun _ _ => rfl

private abbrev rung (n : ℕ) : CounterLens (Store n) :=
  rungCounter.pullback StoreLens.fst fun _ _ => rfl

/-- The mirror network restores the stage order of the stored word's Fourier phases. -/
theorem sourceDeriv_reversal :
    SourceDerivTot (.ofEffect (fourierAssertion n) fun _ => True)
      ((reversal n).mapStore StoreLens.fst)
      (.ofEffect (fun σ => Assertion.pure (stageState σ.2 n) σ) fun _ => True) := by
  let v := fun (σ : Store n) (i : Fin n) => Qubit.phaseState (suffixAngle σ.2 i.rev)
  let J := fun k (σ : Store n) => Assertion.pure (product (reversalFactors (v σ) k)) σ
  have d := SourceDerivTot.countedGateFamily (stage n) (fun _ => n / 2) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) J (fun _ _ _ => rfl)
    (fun σ => ![control n σ.1.1, (control n σ.1.1).rev]) (fun σ _ => mirrorGate n σ.1.1)
    (fun _ _ h => swap_injective h)
    (SourceDerivTot.unitary_pure _ _ (fun σ => product (reversalFactors (v σ) σ.1.1))
      (fun σ => product (reversalFactors (v σ) (σ.1.1 + 1))) (fun _ h => swap_injective h.2)
      (fun σ h => mirrorGate_product (v σ) h.2))
  apply SourceDerivTot.conseq _ d _
  · intro σ h
    refine ⟨h, le_of_eq ?_⟩
    change (fourierAssertion n σ).val = (J 0 σ).val
    rw [fourierAssertion_apply]
    simp only [J, reversalFactors_zero]
    rfl
  · intro σ _
    refine ⟨trivial, le_of_eq ?_⟩
    simp only [CQAssertion.ofEffect, J, reversalFactors_full, stageState_full, Function.comp_def,
      v, Fin.rev_rev]

private theorem rung_step (x : Fin n → Fin 2) {k t : ℕ} (hk : k < n) (ht : t < k) :
    (inverseRungGate n k t).toOperator (ladderState x (n - 1 - k) (k - t)).val =
      (ladderState x (n - 1 - k) (k - (t + 1))).val := by
  have h := rungGate_ladderState x (n - 1 - k) (k - 1 - t) (by lia)
  rw [show k - t = (k - 1 - t) + 1 by lia, ← h,
    show k - (t + 1) = k - 1 - t by lia]
  exact inverseRung_cancel hk ht _

private theorem counted_rungs (P : Store n → Prop) (hP : ∀ σ t, P ((rung n).set σ t) ↔ P σ)
    (hk : ∀ σ, P σ → σ.1.1 < n) (J : ℕ → Assertion (Store n) (Memory n))
    (hJ : ∀ t σ u, J t ((rung n).set σ u) = J t σ)
    (step : let active := fun σ : Store n => P σ ∧ σ.1.2 < σ.1.1
      SourceDerivTot (.ofEffect (fun σ => J σ.1.2 σ) active)
        ((inverseRung n).mapStore StoreLens.fst) (.ofEffect (fun σ => J (σ.1.2 + 1) σ) active)) :
    SourceDerivTot (.ofEffect (J 0) P) ((inverseLadder n).mapStore StoreLens.fst)
      (.ofEffect (fun σ => J σ.1.1 σ) fun σ => P σ ∧ σ.1.2 = σ.1.1) :=
  SourceDerivTot.countedGateFamily (rung n) (fun σ => σ.1.1) P hP (fun _ _ => rfl) J hJ _ _
    (fun σ h ht => inverseRung_injective (hk σ h) ht) step

/-- The inner loop undoes the active ladder for the stored word, preserving its classical guard. -/
theorem sourceDeriv_inverseLadder (P : Store n → Prop)
    (hP : ∀ σ t, P ((rungCounter.set σ.1 t), σ.2) ↔ P σ) (hk : ∀ σ, P σ → σ.1.1 < n) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (stageState σ.2 (n - σ.1.1)) σ) P)
      ((inverseLadder n).mapStore StoreLens.fst)
      (.ofEffect (fun σ => Assertion.pure (ladderState σ.2 (n - 1 - σ.1.1) 0) σ)
        fun σ => P σ ∧ σ.1.2 = σ.1.1) := by
  let w := fun t (σ : Store n) => ladderState σ.2 (n - 1 - σ.1.1) (σ.1.1 - t)
  have d := counted_rungs P hP hk (fun t σ => Assertion.pure (w t σ) σ) (fun _ _ _ => rfl)
    (SourceDerivTot.unitary_pure _ _ (fun σ => w σ.1.2 σ) (fun σ => w (σ.1.2 + 1) σ)
      (fun σ h => inverseRung_injective (hk σ h.1) h.2) (fun σ h => rung_step σ.2 (hk σ h.1) h.2))
  apply SourceDerivTot.conseq _ d _
  · intro σ h
    have hs := hk σ h
    have he := ladderState_full σ.2 (n - 1 - σ.1.1) (by lia)
    rw [show n - 1 - (n - 1 - σ.1.1) = σ.1.1 by lia,
      show n - 1 - σ.1.1 + 1 = n - σ.1.1 by lia] at he
    exact ⟨h, le_of_eq (by simp only [CQAssertion.ofEffect, w, Nat.sub_zero, he])⟩
  · exact fun σ h => ⟨h, le_of_eq (by simp only [w, Nat.sub_self])⟩

/-- The outer loop undoes the stages while reading their decreasing indices and the stored word. -/
theorem sourceDeriv_inverseIteration :
    SourceDerivTot (.ofEffect (fun σ : Store n => Assertion.pure (stageState σ.2 n) σ)
      fun _ => True)
      ((inverseIteration n).mapStore StoreLens.fst)
      (.ofEffect (basisAssertion n) fun _ => True) := by
  let J := fun k (σ : Store n) => Assertion.pure (stageState σ.2 (n - k)) σ
  have d := SourceDerivTot.countedFamily (stage n) (fun _ => n) (fun _ => True)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) J (fun _ _ _ => rfl)
    (((inverseLadder n).seq (inverseHadamard n)).mapStore StoreLens.fst)
  apply SourceDerivTot.conseq _ (d ?_ ?_) _
  · exact fun _ h => ⟨h, le_rfl⟩
  · apply SourceDerivTot.seq (sourceDeriv_inverseLadder (fun σ => True ∧ σ.1.1 < n)
      (fun _ _ => Iff.rfl) (fun _ h => h.2))
    refine SourceDerivTot.conseq ?_ (SourceDerivTot.unitary_pure (Store := Store n) (k := 1) _ _
      (φ := fun σ => True ∧ σ.1.1 < n)
      (fun σ => ladderState σ.2 (n - 1 - σ.1.1) 0) (fun σ => stageState σ.2 (n - (σ.1.1 + 1)))
      (fun _ _ => Function.injective_of_subsingleton _) ?_) ?_
    · exact fun _ h => ⟨h.1, le_rfl⟩
    · intro σ h
      have hk : σ.1.1 < n := h.2
      change (hadamardGate n (n - 1 - σ.1.1)).toOperator _ = _
      rw [← hadamardGate_stageState σ.2 (n - 1 - σ.1.1) (by lia),
        show n - (σ.1.1 + 1) = n - 1 - σ.1.1 by lia]
      exact hadamardGate_twice _ _
    · exact fun _ h => ⟨h, le_rfl⟩
  · intro z
    let L := fun σ : Store n => True ∧ σ.1.1 < n ∧ ((n - σ.1.1 : ℕ) : ℤ) = z
    have hi := counted_rungs L (fun _ _ => Iff.rfl) (fun _ h => h.2.1)
      (fun _ => Assertion.identity) (fun _ _ _ => rfl)
      (SourceDerivTot.unitary_identity _ _ _ (fun _ h => inverseRung_injective h.1.2.1 h.2))
    apply SourceDerivTot.seq hi
    refine SourceDerivTot.conseq ?_ (SourceDerivTot.unitary_identity (k := 1) _ _ L
      (fun _ _ => Function.injective_of_subsingleton _)) ?_
    · exact fun _ h => ⟨h.1, le_rfl⟩
    · exact fun _ h => ⟨h, le_rfl⟩
  · exact fun _ _ => ⟨trivial, le_of_eq (by simp only [J, Nat.sub_self, stageState_zero]; rfl)⟩

/-- The counted circuit decodes the word named by the classical store. -/
theorem sourceDeriv_decode : SourceDerivTot (.ofEffect (fourierAssertion n) fun _ => True)
    (inverseCircuit n) (.ofEffect (basisAssertion n) fun _ => True) :=
  .seq sourceDeriv_reversal sourceDeriv_inverseIteration

/-- A product of reversed suffix phases decodes to the basis factors of the stored word. -/
theorem sourceDeriv_decode_product :
    SourceDerivTot (.ofEffect (fun σ : Store n => Assertion.pure
      (product fun i => Qubit.phaseState (suffixAngle σ.2 i.rev)) σ) fun _ => True)
      (inverseCircuit n) (.ofEffect (fun σ => Assertion.pure
        (product fun i => UnitState.ofBasis (ZBasis 2) (σ.2 i)) σ) fun _ => True) := by
  have h := sourceDeriv_decode (n := n)
  rwa [show fourierAssertion n = _ from funext fourierAssertion_apply] at h

/-- Total-correctness derivation for the stored Fourier and computational basis assertions. -/
theorem derivTot_decode : DerivTot (fourierAssertion n) (inverseCircuit n) (basisAssertion n) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_decode (n := n)).toDerivTot

/-- Semantic total correctness of the inverse transform with a read-only input word. -/
theorem validTot_decode : validTot (fourierAssertion n) (inverseCircuit n) (basisAssertion n) := by
  exact derivTot_decode.sound

end

end QuantumProgram.FourierClassical
