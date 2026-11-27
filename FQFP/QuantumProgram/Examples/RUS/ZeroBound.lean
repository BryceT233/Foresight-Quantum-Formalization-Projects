/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the zero-budget execution and quantitative source triples.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/RUSZeroBound.lean
Qhl/Logic/Source/ConvexDerived.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Examples.RUS.BoundedSource

/-!
# Bounded RUS with no attempts

Arming the retry flag, clearing the counter and testing the false guard are the entire run.
The success invariant requires a positive budget at entry. At budget zero the quantitative
source precondition has zero effect, so empty Convex2 supplies the boundary case.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit
open scoped ENNReal

namespace QuantumProgram

open RepeatUntilSuccess (Memory)
open BoundedRepeatUntilSuccess (Store arm counter bound pre scale)

noncomputable section

namespace HeraldedRUS

/-- At zero budget the two assignments and false guard leave a single terminal state.
The input budget and the entire quantum operator are preserved. -/
theorem frontier_of_zero_budget (W : UnitaryProgram Memory) (cap : ℕ → ℕ) (s : CQState Store Memory)
    (h : cap s.store.bound = 0) :
    (Configuration.mk (some (program W cap)) s).frontier 3 =
      [⟨none, { s with store := { s.store with retry := true, attempts := 0 } }⟩] := by
  simp [program, Command.counted, Configuration.frontier, Configuration.next, Command.step,
    Configuration.seqWith, arm, counter, bound, h]

/-- Every terminal observation at zero budget is evaluated on the unchanged quantum operator
at the armed store. -/
theorem postH_of_zero_budget (W : UnitaryProgram Memory) (cap : ℕ → ℕ) (s : CQState Store Memory)
    (h : cap s.store.bound = 0) (A : Store → Operator Memory) :
    (Configuration.mk (some (program W cap)) s).PostH A =
      ENNReal.ofReal (s.expectation (A { s.store with retry := true, attempts := 0 })) := by
  let t := { s with store := counter.set (arm s.store) 0 }
  let b := fun σ => decide (σ.attempts < bound cap σ)
  let body := (attempt W).seq (.assign BoundedRepeatUntilSuccess.inc)
  let loop := Command.whileDo b body
  have h₁ := Configuration.PostH_singleton (p := program W cap) (s := s)
    (d := ⟨some (.counted counter (bound cap) (attempt W)), { s with store := arm s.store }⟩) rfl A
  have h₂ := Configuration.PostH_singleton (p := .counted counter (bound cap) (attempt W))
    (s := { s with store := arm s.store }) (d := ⟨some loop, t⟩) rfl A
  have hb : b t.store = false := by simp [b, t, arm, counter, bound, h]
  rw [h₁, h₂, Configuration.PostH_whileDo_of_false body hb]
  simp [t, counter, arm, CQState.expectation]

/-- The terminal probability of a classical success is zero on every input operator. -/
theorem successMass_of_zero_budget (W : UnitaryProgram Memory) (cap : ℕ → ℕ)
    (s : CQState Store Memory) (h : cap s.store.bound = 0) :
    (Configuration.mk (some (program W cap)) s).PostH
      (fun σ => ((Assertion.identity (H := Memory)).mask (fun τ => τ.retry = false) σ).val) =
      0 := by
  rw [postH_of_zero_budget W cap s h]
  simp [Assertion.mask, CQState.expectation]

/-- The source precondition keeps classical support true and scales the input data projector. -/
def successSourcePre (q : Set.Icc (0 : ℝ) 1) (N : ℕ) (ψ : UnitState Qubit) :
    CQAssertion Store Memory :=
  .ofEffect (fun σ => scale (successFloor q N) (pre ψ σ)) fun _ => True

/-- Interpreting the source precondition retains the full quantitative input effect. -/
theorem successSourcePre_toAssn (q : Set.Icc (0 : ℝ) 1) (N : ℕ) (ψ : UnitState Qubit) :
    (successSourcePre q N ψ).toAssn = fun σ => scale (successFloor q N) (pre ψ σ) :=
  funext fun _ => Assertion.mask_of_pos _ (φ := fun _ => True) trivial

/-- Interpreting classical success masks the target projector by outcome zero. -/
theorem sourceSuccessPost_toAssn (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    (sourceSuccessPost V ψ).toAssn = successPost V ψ := rfl

/-- Zero attempts give the zero pre-effect for every retry weight, including zero. -/
theorem successSourcePre_zero (q : Set.Icc (0 : ℝ) 1) (ψ : UnitState Qubit) :
    successSourcePre q 0 ψ = .ofEffect Assertion.zero (fun _ => True) := by
  unfold successSourcePre
  congr 1
  funext σ
  apply Subtype.ext
  simp [successFloor, scale, Assertion.zero]

/-- Empty Convex2 derives the success triple with its literal zero-budget source endpoints. -/
theorem successSourceDeriv_zero (W : UnitaryProgram Memory) (V : Qubit ⟶ Qubit) [IsUnitary V]
    (q : Set.Icc (0 : ℝ) 1) (ψ : UnitState Qubit) :
    SourceDerivTot (successSourcePre q 0 ψ) (program W fun _ => 0) (sourceSuccessPost V ψ) := by
  rw [successSourcePre_zero]
  exact .zeroPre _ _ _

/-- The same empty combination proves the zero-retry triple in the partial source calculus. -/
theorem successSourceDerivPar_zero (W : UnitaryProgram Memory) (V : Qubit ⟶ Qubit) [IsUnitary V]
    (q : Set.Icc (0 : ℝ) 1) (ψ : UnitState Qubit) :
    SourceDerivPar (successSourcePre q 0 ψ) (program W fun _ => 0) (sourceSuccessPost V ψ) := by
  rw [successSourcePre_zero]
  exact .zeroPre _ _ _

variable {W : UnitaryProgram Memory} {V : Qubit ⟶ Qubit} [IsUnitary V] {α β : ℂ}

/-- Empty Convex2 at zero and the ranked measurement proof at successors cover all budgets. -/
theorem successSourceDeriv_all (hB : HeraldedBlock W V α β) (N : ℕ) (ψ : UnitState Qubit) :
    SourceDerivTot (successSourcePre hB.retryProb N ψ) (program W fun _ => N)
      (sourceSuccessPost V ψ) := by
  cases N with
  | zero => exact successSourceDeriv_zero W V hB.retryProb ψ
  | succ n => exact boundedRusSuccessSourceDeriv hB (n + 1) (Nat.succ_pos n) ψ

/-- The original pair of source assertions is valid at every natural budget. -/
theorem successSourcePair_valid (hB : HeraldedBlock W V α β) (N : ℕ) (ψ : UnitState Qubit) :
    validTot (successSourcePre hB.retryProb N ψ).toAssn (program W fun _ => N)
      (sourceSuccessPost V ψ).toAssn :=
  (successSourceDeriv_all hB N ψ).sound

/-- Soundness gives the quantitative success triple at every natural retry bound. -/
theorem boundedRusSuccessSourceValid_all (hB : HeraldedBlock W V α β) (N : ℕ)
    (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor hB.retryProb N) (pre ψ σ)) (program W fun _ => N)
      (successPost V ψ) := by
  simpa only [successSourcePre_toAssn, sourceSuccessPost_toAssn] using
    successSourcePair_valid hB N ψ

end HeraldedRUS

namespace BoundedRepeatUntilSuccess

/-- For Paetznick–Svore the source derivation with coefficient `1 − (1/4)^N` includes zero. -/
theorem boundedRusSuccessSourceDeriv_all (N : ℕ) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (fun σ => scale (successFloor N) (pre ψ σ)) fun _ => True)
      (program fun _ => N) (sourceSuccessPost ψ) := by
  simpa only [HeraldedRUS.successSourcePre, retryProb_eq] using
    HeraldedRUS.successSourceDeriv_all PaetznickSvore.heraldedBlock N ψ

/-- The concrete quantitative source triple is valid for all budgets. -/
theorem boundedRusSuccessSourceValid_all (N : ℕ) (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor N) (pre ψ σ)) (program fun _ => N) (successPost ψ) := by
  simpa only [retryProb_eq] using
    HeraldedRUS.boundedRusSuccessSourceValid_all PaetznickSvore.heraldedBlock N ψ

end BoundedRepeatUntilSuccess

end

end QuantumProgram
