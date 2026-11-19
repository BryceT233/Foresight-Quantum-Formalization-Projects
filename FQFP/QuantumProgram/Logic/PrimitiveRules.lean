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
Modified by Foresight Quantum in 2026
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

/-- A completely positive map is monotone in the Löwner order. -/
theorem _root_.Qudit.CPMap.monotone {K : Qudit} (F : CPMap H K) : Monotone F.toSuperoperator := by
  intro X Y h
  simpa only [map_sub, sub_nonneg] using LinearMap.nonneg_iff_isPositive.mpr
    (F.completelyPositive.isPositive (Y - X) (LinearMap.le_def.mp h))

/-- Pull an effect through a trace-preserving channel using its Heisenberg dual. -/
noncomputable def channelEffect (Φ : QuantumChannel H H) (E : Set.Icc (0 : Operator H) 1) :
    Set.Icc (0 : Operator H) 1 :=
  ⟨Φ.toCPMap.dual.toSuperoperator E,
    LinearMap.nonneg_iff_isPositive.mpr (Φ.toCPMap.dual.completelyPositive.isPositive _
      (LinearMap.nonneg_iff_isPositive.mp E.2.1)),
    (Φ.toCPMap.dual.monotone E.2.2).trans_eq
      (Φ.toCPMap.isTracePreserving_iff_dual_one.mp Φ.tracePreserving)⟩

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
    Finset.sum_nonneg fun i _ => LinearMap.nonneg_iff_isPositive.mpr
      ((I.branchCPMap i).dual.completelyPositive.isPositive _
        (LinearMap.nonneg_iff_isPositive.mp (E i).2.1)),
    (Finset.sum_le_sum fun i _ => (I.branchCPMap i).dual.monotone (E i).2.2).trans_eq
      I.toPOVM.sum_op⟩

/-- Born-sum precondition with the postcondition evaluated after classical write-back. -/
noncomputable def Assertion.measurePre (A : Assertion Store H) {k m : ℕ}
    (r : Store → Fin k → Cell) (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) : Assertion Store H :=
  open Classical in fun σ => if h : Function.Injective (r σ) then
    instrumentEffect (I σ h) (fun i => A (upd i σ)) else ⟨0, le_rfl, (Assertion.identity σ).2.1⟩

/-- Skipping a step preserves every assertion. -/
theorem validTot_skip (A : Assertion Store H) : validTot A (.skip : Command Store Cell H) A :=
  fun s => Configuration.ofReal_expectation_le_PostH_of_frontier
    (c := Configuration.mk (some (.skip : Command Store Cell H)) s) (n := 1) (s := s) rfl
    (fun σ => A σ)

/-- Assignment acts on the store argument of the postcondition. -/
theorem validTot_assign (f : Store → Store) (A : Assertion Store H) :
    validTot (A ∘ f) (.assign f : Command Store Cell H) A :=
  fun s => Configuration.ofReal_expectation_le_PostH_of_frontier
    (c := Configuration.mk (some (.assign f : Command Store Cell H)) s) (n := 1)
    (s := { s with store := f s.store }) rfl (fun σ => A σ)

/-- The channel dual computes the post-expectation of the single output. -/
theorem validTot_channel (f : Store → QuantumChannel H H) (A : Assertion Store H) :
    validTot (A.channelPre f) (.channel f : Command Store Cell H) A := by
  intro s
  exact (congrArg (fun z : ℂ => ENNReal.ofReal z.re)
    ((f s.store).toCPMap.trace_dual s.op (A s.store))).le.trans
    (Configuration.ofReal_expectation_le_PostH_of_frontier
      (c := Configuration.mk (some (.channel f : Command Store Cell H)) s) (n := 1)
      (s := s.map (f s.store)) rfl (fun σ => A σ))

/-- The unitary backward assertion is totally valid, including at repeated register cells. -/
theorem validTot_unitary {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (A : Assertion Store H) :
    validTot (A.unitaryPre r U) (.unitary r U) A := by
  intro s
  by_cases h : Function.Injective (r s.store)
  · have hf : (Configuration.mk (some (.unitary r U)) s).frontier 1 =
        [⟨none, s.map (U s.store h).toChannel⟩] := by
      simp [Configuration.frontier, Configuration.next, Command.step, h]
    simp only [Assertion.unitaryPre, dite_eq_left h]
    exact (congrArg (fun z : ℂ => ENNReal.ofReal z.re)
      ((U s.store h).toChannel.toCPMap.trace_dual s.op (A s.store))).le.trans
      (Configuration.ofReal_expectation_le_PostH_of_frontier hf (fun σ => A σ))
  · simp [Assertion.unitaryPre, h, CQState.expectation_zero]

/-- Each instrument branch pairs with the effect at that branch's updated store. -/
theorem validTot_measure {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
    (A : Assertion Store H) : validTot (A.measurePre r I upd) (.measure r I upd) A := by
  intro s
  by_cases h : Function.Injective (r s.store)
  · rw [Configuration.PostH_measure]
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    simp only [Assertion.measurePre, dite_eq_left h, instrumentEffect, CQState.expectation,
      measurementSuccessors, List.map_ofFn, List.sum_ofFn, Finset.sum_mul, Operator.trace, map_sum,
      Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => congrArg Complex.re
      (((I s.store h).branchCPMap i).trace_dual s.op (A (upd i s.store)))
  · simp [Assertion.measurePre, h, CQState.expectation_zero]

end QuantumProgram
