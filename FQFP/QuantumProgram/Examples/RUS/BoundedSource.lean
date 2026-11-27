/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the bounded Paetznick-Svore source derivations.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/BoundedRUSTriple.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Examples.RUS.Bounded
public import FQFP.QuantumProgram.Logic.RepeatUntilSuccess.Source

/-!
# Paetznick–Svore bounded RUS in the source proof system

The heralded-block source theorems apply to the seven-gate circuit with retry weight `1/4`.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.BoundedRepeatUntilSuccess

open PaetznickSvore (target heraldedBlock)

noncomputable section

/-- Observe the transformed data on success and the original data on exhaustion. -/
abbrev exitEffect := HeraldedRUS.exitEffect target

/-- Success records outcome zero and observes the transformed data. -/
abbrev sourceSuccessPost := HeraldedRUS.sourceSuccessPost target

/-- Fixed-cap source derivation, including immediate exhaustion at zero. -/
theorem boundedRusSourceDeriv (N : ℕ) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (pre ψ) fun _ => True) (program fun _ => N)
      (.ofEffect (exitEffect ψ) fun σ => guard (fun _ => N) σ = false) :=
  HeraldedRUS.boundedRusSourceDeriv heraldedBlock N ψ

/-- Fixed positive cap with an explicit classical success postcondition. -/
theorem boundedRusSuccessSourceDeriv (N : ℕ) (hN : 0 < N) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (fun σ => scale (successFloor N) (pre ψ σ)) fun _ => True)
      (program fun _ => N) (sourceSuccessPost ψ) := by
  simpa only [retryProb_eq] using
    HeraldedRUS.boundedRusSuccessSourceDeriv heraldedBlock N hN ψ

/-- A positive budget read from classical input, with success or exhaustion at exit. -/
theorem boundedRusClassicalSourceDeriv (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (pre ψ) fun σ => 1 ≤ σ.bound) (program id)
      (.ofEffect (exitEffect ψ) fun σ => σ.retry = false ∨ σ.bound ≤ σ.attempts) :=
  HeraldedRUS.boundedRusClassicalSourceDeriv heraldedBlock ψ

/-- The success coefficient uses the original read-only input budget. -/
theorem boundedRusClassicalSuccessSourceDeriv (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (fun σ => scale (successFloor σ.bound) (pre ψ σ))
      (fun σ => 1 ≤ σ.bound)) (program id) (sourceSuccessPost ψ) := by
  simpa only [retryProb_eq] using
    HeraldedRUS.boundedRusClassicalSuccessSourceDeriv heraldedBlock ψ

/-- The ordinary fixed-cap source proof implies the masked exit triple. -/
theorem boundedRusSourceValid (N : ℕ) (ψ : UnitState Qubit) :
    validTot (pre ψ) (program fun _ => N) ((exitEffect ψ).mandNot (guard fun _ => N)) :=
  HeraldedRUS.boundedRusSourceValid heraldedBlock N ψ

/-- The quantitative fixed-cap source proof implies the original success triple. -/
theorem boundedRusSuccessSourceValid (N : ℕ) (hN : 0 < N) (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor N) (pre ψ σ)) (program fun _ => N) (successPost ψ) := by
  simpa only [retryProb_eq] using
    HeraldedRUS.boundedRusSuccessSourceValid heraldedBlock N hN ψ

/-- Interpret the classical-input exit disjunction in the history semantics. -/
theorem boundedRusClassicalSourceValid (ψ : UnitState Qubit) :
    validTot ((pre ψ).mask fun σ => 1 ≤ σ.bound) (program id)
      ((exitEffect ψ).mask fun σ => σ.retry = false ∨ σ.bound ≤ σ.attempts) :=
  HeraldedRUS.boundedRusClassicalSourceValid heraldedBlock ψ

/-- The classical-input quantitative proof guarantees the success floor at the stored bound. -/
theorem boundedRusClassicalSuccessSourceValid (ψ : UnitState Qubit) :
    validTot (Assertion.mask (fun σ => scale (successFloor σ.bound) (pre ψ σ))
      (fun σ => 1 ≤ σ.bound)) (program id) (successPost ψ) := by
  simpa only [retryProb_eq] using
    HeraldedRUS.boundedRusClassicalSuccessSourceValid heraldedBlock ψ

end

end QuantumProgram.BoundedRepeatUntilSuccess
