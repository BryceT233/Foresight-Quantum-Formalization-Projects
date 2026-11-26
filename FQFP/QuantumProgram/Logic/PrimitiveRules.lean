/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for validity of the primitive command rules.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Assertion.lean
Qhl/Logic/Soundness.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Correctness
public import FQFP.CQM.Qudit.Measurement.Process

/-!
# Backward assertions for primitive quantum commands

Channel instructions include initialization when supplied with the evaluated initialization
channel. Measurement pulls the postcondition at each written store through its instrument branch.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Pull an effect through a trace-preserving channel using its Heisenberg dual. -/
noncomputable def channelEffect (Φ : QuantumChannel H H) (E : Set.Icc (0 : Operator H) 1) :
    Set.Icc (0 : Operator H) 1 :=
  Φ.pullbackEffect E

/-- Backward assertion for a store-dependent whole-memory channel. -/
noncomputable def Assertion.channelPre (A : Assertion Store H) (f : Store → QuantumChannel H H) :
    Assertion Store H := fun σ => channelEffect (f σ) (A σ)

/-- Pull the assertion through the evaluated unitary, with zero effect on a blocked register. -/
noncomputable def Assertion.unitaryPre (A : Assertion Store H) {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) : Assertion Store H :=
  open Classical in fun σ => if h : Function.Injective (r σ) then
    channelEffect (U σ h).toChannel (A σ) else ⟨0, le_rfl, (Assertion.identity σ).2.1⟩

/-- Pull outcome-dependent effects through an instrument and add their contributions. -/
noncomputable def instrumentEffect {m : ℕ} (I : Instrument H H (Fin m))
    (E : Fin m → Set.Icc (0 : Operator H) 1) : Set.Icc (0 : Operator H) 1 :=
  ⟨∑ i, (I.branchCPMap i).dual.toSuperoperator (E i),
    Finset.sum_nonneg fun i _ => (I.branchCPMap i).dual.map_nonneg (E i).2.1,
    (Finset.sum_le_sum fun i _ => (I.branchCPMap i).dual.monotone (E i).2.2).trans_eq
      I.toPOVM.sum_op⟩

/-- An outcome-independent postcondition pulls back through the nonselective channel. -/
@[simp] theorem instrumentEffect_const {m : ℕ} (I : Instrument H H (Fin m))
    (E : Set.Icc (0 : Operator H) 1) :
    instrumentEffect I (fun _ => E) = I.toChannel.pullbackEffect E := by
  apply Subtype.ext
  apply Operator.ext_trace
  intro X
  change ((∑ i, (I.branchCPMap i).dual.toSuperoperator E) * X).trace =
    (I.toChannel.toCPMap.dual.toSuperoperator E * X).trace
  simp only [Finset.sum_mul, Operator.trace, map_sum, CPMap.trace_dual]
  change _ = (E.val * (∑ i, I.branch i) X).trace
  simp only [LinearMap.sum_apply, Finset.mul_sum, Operator.trace, map_sum]
  rfl

/-- Born-sum precondition with the postcondition evaluated after classical write-back. -/
noncomputable def Assertion.measurePre (A : Assertion Store H) {k m : ℕ}
    (r : Store → Fin k → Cell) (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) : Assertion Store H :=
  open Classical in fun σ => if h : Function.Injective (r σ) then
    instrumentEffect (I σ h) (fun i => A (upd i σ)) else ⟨0, le_rfl, (Assertion.identity σ).2.1⟩

/-- Skipping a step preserves every assertion. -/
theorem validTot_skip (A : Assertion Store H) : validTot A (.skip : Command Store Cell H) A :=
  fun s => (Configuration.PostH_of_step_terminal (p := .skip) (s := s) (t := s) rfl
    (fun σ => A σ)).ge

/-- Assignment acts on the store argument of the postcondition. -/
theorem validTot_assign (f : Store → Store) (A : Assertion Store H) :
    validTot (A ∘ f) (.assign f : Command Store Cell H) A :=
  fun s => (Configuration.PostH_of_step_terminal (p := .assign f) (s := s)
    (t := { s with store := f s.store }) rfl (fun σ => A σ)).ge

/-- The channel dual computes the post-expectation of the single output. -/
theorem validTot_channel (f : Store → QuantumChannel H H) (A : Assertion Store H) :
    validTot (A.channelPre f) (.channel f : Command Store Cell H) A := by
  intro s
  rw [Configuration.PostH_of_step_terminal (p := .channel f) (s := s) (t := s.map (f s.store)) rfl]
  exact ENNReal.ofReal_le_ofReal (s.expectation_pullbackEffect (f s.store) (A s.store)).le

/-- The unitary backward assertion is totally valid, including at repeated register cells. -/
theorem validTot_unitary {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H) :
    validTot (A.unitaryPre r U) (.unitary r U) A := by
  intro s
  by_cases h : Function.Injective (r s.store)
  · have hstep : (Command.unitary r U).step s =
        [⟨none, s.map (U s.store h).toChannel⟩] := by
      simp [Command.step, h]
    rw [Configuration.PostH_of_step_terminal hstep]
    simp only [Assertion.unitaryPre, dite_eq_left h]
    exact ENNReal.ofReal_le_ofReal (s.expectation_pullbackEffect (U s.store h).toChannel _).le
  · simp [Assertion.unitaryPre, h, CQState.expectation_zero]

/-- The measurement precondition sums expectations at the updated branch stores. -/
theorem CQState.expectation_measurePre (s : CQState Store H) {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
    (A : Assertion Store H) : s.expectation (A.measurePre r I upd s.store) =
      ((measurementSuccessors r I upd s).map fun t => t.expectation (A t.store)).sum := by
  by_cases h : Function.Injective (r s.store)
  · simp only [Assertion.measurePre, dite_eq_left h, instrumentEffect, CQState.expectation,
      measurementSuccessors, List.map_ofFn, List.sum_ofFn, Finset.sum_mul, Operator.trace, map_sum,
      Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => congrArg Complex.re
      (((I s.store h).branchCPMap i).trace_dual s.op (A (upd i s.store)))
  · simp [Assertion.measurePre, measurementSuccessors, h, CQState.expectation_zero]

/-- Each instrument branch pairs with the effect at that branch's updated store. -/
theorem validTot_measure {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
    (A : Assertion Store H) : validTot (A.measurePre r I upd) (.measure r I upd) A := by
  intro s
  rw [Configuration.PostH_measure, s.expectation_measurePre]

end QuantumProgram
