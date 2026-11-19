/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the bounded Paetznick-Svore program and its success probability.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/BoundedRUSTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.HeraldedRUS
public import FQFP.QuantumProgram.Examples.PaetznickSvore

/-!
# Bounded repeat until success

The measured ancilla controls early exit from a counted loop. The remaining budget is a
natural rank. On an armed input, one attempt applies the Paetznick–Svore target with
probability `3/4` and returns the original data for another attempt with probability `1/4`.
-/

@[expose] public section

open Qudit
open scoped ComplexOrder ENNReal

namespace QuantumProgram.BoundedRepeatUntilSuccess

open RepeatUntilSuccess (Memory outputMap)
open PaetznickSvore (target circuit heraldedBlock)

noncomputable section

/-- Reset the ancilla, execute the seven gates and measure the ancilla into the flag. -/
abbrev attempt := HeraldedRUS.attempt circuit

/-- Use a constant cap for a fixed budget, or `id` to read the budget from the input store. -/
abbrev program := HeraldedRUS.program circuit

/-- The cap is read-only throughout initialization, measurement and counter updates. -/
theorem preserves_bound (cap : ℕ → ℕ) : (program cap).PreservesParameters Store.bound :=
  HeraldedRUS.preserves_bound circuit cap

/-- The backward effect of a complete counted attempt. -/
abbrev bodyPre := HeraldedRUS.bodyPre circuit

/-- Sum the two heralded branches at their updated stores. -/
theorem bodyPre_op (A : Assertion Store Memory) (σ : Store) :
    (bodyPre A σ : Operator Memory) = Operator.oneTensorHom Qubit Qubit
      (∑ i, (PaetznickSvore.weight i : ℂ) • Superoperator.conjugate (outputMap target i).hom.adjoint
        (A (nextStore σ i))) := by
  simpa only [PaetznickSvore.weight, PaetznickSvore.successProb, PaetznickSvore.failProb] using
    HeraldedRUS.bodyPre_op heraldedBlock A σ

/-- The success effect observes ancilla zero and the transformed data. -/
abbrev successEffect := HeraldedRUS.successEffect target

/-- Only stores reporting a successful measurement contribute to this postcondition. -/
abbrev successPost := HeraldedRUS.successPost target

/-- The one-attempt retry probability of the Paetznick–Svore block. -/
def retryProbability : Set.Icc (0 : ℝ) 1 := ⟨1 / 4, by norm_num, by norm_num⟩

/-- The block witness supplies the concrete one-quarter retry weight. -/
theorem retryProb_eq : heraldedBlock.retryProb = retryProbability :=
  Subtype.ext PaetznickSvore.failProb

/-- The success probability guaranteed by the remaining attempts. -/
abbrev successFloor := HeraldedRUS.successFloor retryProbability

/-- The quantum part of the invariant before imposing a classical counter bound. -/
abbrev rewardEffect := HeraldedRUS.rewardEffect target

/-- At the retry branch the coefficient depends on the remaining attempts. On the success
branch the target state has already been obtained. The classical mask enforces the cap. -/
abbrev invariant := HeraldedRUS.invariant target

/-- A successful run returns the target. An exhausted run returns the input data with
exactly the cap spent. Neither exit can exceed the cap. -/
abbrev post := HeraldedRUS.post target

/-- Pulling back the invariant yields the reward at the previous remaining budget. -/
theorem pull_invariant (cap : ℕ → ℕ) (ψ : UnitState Qubit) (win : Set.Icc (0 : ℝ) 1)
    (retry : ℕ → Set.Icc (0 : ℝ) 1) (σ : Store) (hk : σ.attempts < cap σ.bound)
    (rec : ∀ n, (retry (n + 1)).val = 3 / 4 * win.val + 1 / 4 * (retry n).val) :
    (bodyPre (invariant cap ψ win retry) σ : Operator Memory) =
      (scale (retry (cap σ.bound - σ.attempts)) (pre ψ σ)).val :=
  HeraldedRUS.pull_invariant heraldedBlock cap ψ win retry σ hk (by
    simpa only [PaetznickSvore.successProb, PaetznickSvore.failProb] using rec)

/-- A single ranked derivation works for every pair of terminal rewards satisfying the
one-attempt recurrence. Both measurement outcomes increment the counter exactly once. -/
theorem rankedDeriv (cap : ℕ → ℕ) (ψ : UnitState Qubit) (win : Set.Icc (0 : ℝ) 1)
    (retry : ℕ → Set.Icc (0 : ℝ) 1)
    (rec : ∀ n, (retry (n + 1)).val = 3 / 4 * win.val + 1 / 4 * (retry n).val) :
    DerivTot (fun σ => scale (retry (cap σ.bound)) (pre ψ σ)) (program cap)
      ((invariant cap ψ win retry).mandNot (guard cap)) :=
  HeraldedRUS.rankedDeriv heraldedBlock cap ψ win retry (by
    simpa only [PaetznickSvore.successProb, PaetznickSvore.failProb] using rec)

/-- The total derivation of the bounded RUS triple, including the zero-budget case. -/
theorem boundedRusDeriv (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (pre ψ) (program cap) (post cap ψ) :=
  HeraldedRUS.boundedRusDeriv heraldedBlock cap ψ

/-- Soundness gives the total triple on all input density operators and all input stores. -/
theorem boundedRusValid (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    validTot (pre ψ) (program cap) (post cap ψ) :=
  HeraldedRUS.boundedRusValid heraldedBlock cap ψ

/-- One success plus a discounted retry gives the next success floor. -/
theorem successFloor_succ (n : ℕ) :
    (successFloor (n + 1)).val = 3 / 4 * 1 + 1 / 4 * (successFloor n).val := by
  simpa only [retryProb_eq, PaetznickSvore.successProb, PaetznickSvore.failProb] using
    HeraldedRUS.successFloor_succ heraldedBlock n

/-- Count only outputs carrying the target and a successful measurement. -/
theorem boundedRusSuccessDeriv (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (fun σ => scale (successFloor (cap σ.bound)) (pre ψ σ))
      (program cap) (successPost ψ) := by
  simpa only [retryProb_eq] using HeraldedRUS.boundedRusSuccessDeriv heraldedBlock cap ψ

/-- On any input the success post-expectation dominates the input data expectation
multiplied by `1 − (1/4)^N`, for a fixed or classically supplied cap. -/
theorem boundedRusSuccess (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor (cap σ.bound)) (pre ψ σ))
      (program cap) (successPost ψ) := by
  simpa only [retryProb_eq] using HeraldedRUS.boundedRusSuccess heraldedBlock cap ψ

/-- The all-failure coefficient after the remaining attempts. -/
abbrev failureWeight := HeraldedRUS.failureWeight retryProbability

/-- The complementary ranked derivation counts only exhausted runs retaining the input data. -/
theorem boundedRusFailureDeriv (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (fun σ => scale (failureWeight (cap σ.bound)) (pre ψ σ)) (program cap)
      ((pre ψ).mask fun σ => σ.retry = true ∧ σ.attempts = cap σ.bound) := by
  simpa only [retryProb_eq] using HeraldedRUS.boundedRusFailureDeriv heraldedBlock cap ψ

/-- On the intended input the classical outcome probabilities are exact. Success includes
all early exits. The remaining mass consists of runs that used the entire budget. -/
theorem outcomeProbabilities (cap : ℕ → ℕ) (σ : Store) (ρ : Density Qubit) (ψ : UnitState Qubit) :
    let c := Configuration.mk (some (program cap)) (inputState σ ρ ψ)
    let N := cap σ.bound
    let I : Assertion Store Memory := Assertion.identity
    c.PostH (fun τ => I.mask (fun s => s.retry = false) τ) =
        ENNReal.ofReal (1 - (1 / 4 : ℝ) ^ N) ∧
      c.PostH (fun τ => I.mask (fun s => s.retry = true ∧ s.attempts = cap s.bound) τ) =
        ENNReal.ofReal ((1 / 4 : ℝ) ^ N) := by
  simpa only [PaetznickSvore.failProb] using
    HeraldedRUS.outcomeProbabilities heraldedBlock cap σ ρ ψ

end

end QuantumProgram.BoundedRepeatUntilSuccess
