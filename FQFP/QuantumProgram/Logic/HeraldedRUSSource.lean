/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for source derivations for bounded repeat-until-success.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/HeraldedRUSSource.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.HeraldedRUS
public import FQFP.QuantumProgram.Logic.SourceRules

/-!
# Source derivations for bounded heralded repeat until success

The ordinary invariant and the identity rank test use all ancilla outcomes. The success
invariant keeps retrying only while budget remains. Its zero effect on an exhausted
failure permits the source measurement rule to omit that outcome from the success proof.
For both a fixed positive budget and a positive budget read from the store, the source
postcondition records outcome zero and the target state with success floor `1 − (‖β‖²)^N`.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram

open RepeatUntilSuccess (Memory measurement reset)

noncomputable section

namespace BoundedRepeatUntilSuccess

/-- A successful outcome or enough budget left to retry. -/
def canSucceed (cap : ℕ → ℕ) (σ : Store) : Prop :=
  σ.retry = false ∨ σ.attempts < cap σ.bound

/-- Initializing the classical success invariant is equivalent to having a first attempt. -/
theorem canSucceed_initial_iff (cap : ℕ → ℕ) (σ : Store) :
    canSucceed cap (counter.set (arm σ) 0) ↔ 0 < cap σ.bound := by
  simp [canSucceed, counter, arm]

/-- Before increment, the quantitative measurement selects zero unconditionally and one
only if there will be another attempt. -/
theorem canSucceed_nextStore (cap : ℕ → ℕ) (σ : Store) (i : Fin 2) :
    canSucceed cap (nextStore σ i) ↔ i = 0 ∨ σ.attempts + 1 < cap σ.bound := by
  fin_cases i <;> simp [canSucceed, nextStore, inc, record, counter]

end BoundedRepeatUntilSuccess

namespace HeraldedRUS

open BoundedRepeatUntilSuccess
open BoundedRepeatUntilSuccess renaming guard → loopGuard

variable (W : UnitaryProgram Memory)

/-- Pull a source assertion back through a counted attempt with selected measurement outcomes. -/
theorem bodySource {A B : Assertion Store Memory} {φ χ : Store → Prop}
    (keep : Store → Prop)
    (hc : ∀ σ, φ σ → ∀ i, keep (nextStore σ i) → χ (nextStore σ i))
    (hq : ∀ σ, φ σ → A σ ≤ bodyPre W (B.mask keep) σ) :
    SourceDerivTot (.ofEffect A φ) ((attempt W).seq (.assign inc)) (.ofEffect B χ) := by
  have hm := SourceDerivTot.measureSelected (fun _ : Store => fun _ : Fin 1 => (0 : Fin 2))
    (fun _ _ => measurement) record (B ∘ inc) (χ ∘ inc) (keep ∘ inc)
  refine .conseq ?_ (.seq (.seq (.channel (fun _ => reset) _ _)
    (.seq (.unitary (fun _ => id) (fun _ _ => W) _ _ (fun _ _ => Function.injective_id))
      hm)) (.assign inc B χ)) (fun _ h => ⟨h, le_rfl⟩)
  exact fun σ h => ⟨⟨Function.injective_of_subsingleton _, hc σ h⟩, hq σ h⟩

/-- The identity effect and every measurement outcome witness strict rank decrease. -/
theorem bodyRank (cap : ℕ → ℕ) (φ : Store → Prop) (z : ℤ) :
    SourceDerivTot (.ofEffect Assertion.identity fun σ =>
      φ σ ∧ loopGuard cap σ = true ∧ rank cap σ = z)
      ((attempt W).seq (.assign inc)) (.ofEffect Assertion.identity fun σ => rank cap σ < z) := by
  apply bodySource W (fun _ => True)
  · intro σ h i _
    exact (rank_nextStore_lt cap σ i).trans_eq h.2.2
  · intro σ _
    have h := bodyPre_congr W (A := Assertion.identity.mask fun _ : Store => True)
      (B := Assertion.identity (H := Memory)) (σ := σ)
      (fun i => Assertion.mask_of_pos _ (φ := fun _ => True) trivial)
    change (1 : Operator Memory) ≤ _
    rw [h, bodyPre_identity]

variable {W} {V : Qubit ⟶ Qubit} [IsUnitary V] {α β : ℂ}

private theorem rankedSource (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (reward : ℕ → Set.Icc (0 : ℝ) 1) (keep : Store → Prop) (input : ℕ → Prop)
    (init : ∀ σ : Store, input σ.bound → keep (counter.set (arm σ) 0))
    (zero : ∀ σ i, loopGuard cap σ = true → ¬ keep (nextStore σ i) →
      (rewardEffect V cap ψ 1 reward (nextStore σ i)).val = 0)
    (rec : ∀ n, (reward (n + 1)).val = ‖α‖ ^ 2 * 1 + ‖β‖ ^ 2 * (reward n).val) :
    SourceDerivTot (.ofEffect (fun σ => scale (reward (cap σ.bound)) (pre ψ σ))
      (fun σ => input σ.bound)) (program W cap)
      (.ofEffect (rewardEffect V cap ψ 1 reward) fun σ =>
        (σ.attempts ≤ cap σ.bound ∧ keep σ) ∧ loopGuard cap σ = false) := by
  let J := rewardEffect V cap ψ 1 reward
  let φ := fun σ : Store => σ.attempts ≤ cap σ.bound ∧ keep σ
  have hi : SourceDerivTot (.ofEffect J fun σ => φ σ ∧ loopGuard cap σ = true)
      ((attempt W).seq (.assign inc)) (.ofEffect J φ) := by
    apply bodySource W keep
    · exact fun σ h i hs => ⟨(guard_iff.mp h.2).2, hs⟩
    · intro σ h
      obtain ⟨hm, hk⟩ := guard_iff.mp h.2
      have eq : bodyPre W (J.mask keep) σ = bodyPre W (invariant V cap ψ 1 reward) σ := by
        apply bodyPre_congr
        intro i
        have hle : (nextStore σ i).attempts ≤ cap (nextStore σ i).bound := hk
        rw [invariant,
          Assertion.mask_of_pos _ (φ := fun τ : Store => τ.attempts ≤ cap τ.bound) hle]
        by_cases hs : keep (nextStore σ i)
        · exact J.mask_of_pos hs
        · apply Subtype.ext
          rw [J.mask_of_neg hs]
          exact (zero σ i h.2 hs).symm
      change (J σ).val ≤ _
      rw [eq, pull_invariant hB cap ψ 1 reward σ hk rec]
      simp [J, rewardEffect, hm]
  have loop := SourceDerivTot.whileLoop (rank cap)
    (fun σ (h : φ σ) => by have := h.1; unfold rank; lia) hi (bodyRank W cap φ)
  let clear := fun σ => counter.set σ 0
  refine .conseq ?_ (.seq (.assign arm (J ∘ clear) (φ ∘ clear))
    (.seq (.assign clear J φ) loop)) (fun _ h => ⟨h, le_rfl⟩)
  intro σ h
  exact ⟨⟨Nat.zero_le _, init σ h⟩, by
    simp [CQAssertion.ofEffect, J, rewardEffect, clear, arm, counter, pre]⟩

/-- Observe the transformed data on success and the original data on exhaustion. -/
def exitEffect (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) : Assertion Store Memory :=
  fun σ => if σ.retry then pre ψ σ else successEffect V ψ σ

/-- The success proof retains a classical outcome test in addition to the target projector. -/
def sourceSuccessPost (V : Qubit ⟶ Qubit) [IsUnitary V] (ψ : UnitState Qubit) :
    CQAssertion Store Memory :=
  .ofEffect (successEffect V ψ) fun σ => σ.retry = false

private theorem ordinarySource (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (input : ℕ → Prop) :
    SourceDerivTot (.ofEffect (pre ψ) fun σ => input σ.bound) (program W cap)
      (.ofEffect (exitEffect V ψ) fun σ => loopGuard cap σ = false) := by
  have h := rankedSource hB cap ψ (fun _ => 1) (fun _ => True) input
    (fun _ _ => trivial) (fun _ _ _ hn => (hn trivial).elim)
    (fun _ => by simpa using hB.prob_add.symm)
  simp only [scale_one] at h
  refine .conseq (fun _ hs => ⟨hs, le_rfl⟩) h ?_
  intro σ hs
  exact ⟨hs.2, by cases hm : σ.retry <;> simp [CQAssertion.ofEffect, rewardEffect,
    exitEffect, hm, scale_one]⟩

/-- An omitted outcome is an exhausted retry, whose success reward is zero. -/
theorem rewardEffect_eq_zero_of_not_canSucceed (V : Qubit ⟶ Qubit) [IsUnitary V]
    (q : Set.Icc (0 : ℝ) 1) (cap : ℕ → ℕ) (ψ : UnitState Qubit) {σ : Store}
    (hs : ¬ canSucceed cap σ) : (rewardEffect V cap ψ 1 (successFloor q) σ).val = 0 := by
  have hr : σ.retry = true := Bool.eq_true_of_not_eq_false fun h => hs (Or.inl h)
  have hz := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt (fun hk => hs (Or.inr hk)))
  simp [rewardEffect, hr, hz, successFloor, scale]

private theorem successSource (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (input : ℕ → Prop) (positive : ∀ n, input n → 0 < cap n) :
    SourceDerivTot (.ofEffect (fun σ => scale (successFloor hB.retryProb (cap σ.bound)) (pre ψ σ))
      (fun σ => input σ.bound)) (program W cap) (sourceSuccessPost V ψ) := by
  have h := rankedSource hB cap ψ (successFloor hB.retryProb) (canSucceed cap) input
    (fun σ hs => (canSucceed_initial_iff cap σ).2 (positive σ.bound hs))
    (fun _ _ _ => rewardEffect_eq_zero_of_not_canSucceed V hB.retryProb cap ψ)
    (successFloor_succ hB)
  refine .conseq (fun _ hs => ⟨hs, le_rfl⟩) h ?_
  intro σ hs
  have hm : σ.retry = false := by
    rcases hs.1.2 with hm | hk
    · exact hm
    · cases hm : σ.retry
      · rfl
      · exact Bool.noConfusion ((guard_iff.mpr ⟨hm, hk⟩).symm.trans hs.2)
  exact ⟨hm, by
    simp [CQAssertion.ofEffect, rewardEffect, sourceSuccessPost, hm, scale_one]⟩

/-- Fixed-cap source derivation, including immediate exhaustion at zero. -/
theorem boundedRusSourceDeriv (hB : HeraldedBlock W V α β) (N : ℕ) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (pre ψ) fun _ => True) (program W fun _ => N)
      (.ofEffect (exitEffect V ψ) fun σ => loopGuard (fun _ => N) σ = false) :=
  ordinarySource hB (fun _ => N) ψ (fun _ => True)

/-- Fixed positive cap with an explicit classical success postcondition. -/
theorem boundedRusSuccessSourceDeriv (hB : HeraldedBlock W V α β) (N : ℕ) (hN : 0 < N)
    (ψ : UnitState Qubit) :
    SourceDerivTot
      (.ofEffect (fun σ => scale (successFloor hB.retryProb N) (pre ψ σ)) fun _ => True)
      (program W fun _ => N) (sourceSuccessPost V ψ) :=
  successSource hB (fun _ => N) ψ (fun _ => True) (fun _ _ => hN)

/-- A positive budget read from classical input, with success or exhaustion at exit. -/
theorem boundedRusClassicalSourceDeriv (hB : HeraldedBlock W V α β) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (pre ψ) fun σ => 1 ≤ σ.bound) (program W id)
      (.ofEffect (exitEffect V ψ) fun σ => σ.retry = false ∨ σ.bound ≤ σ.attempts) := by
  refine .conseq (fun _ h => ⟨h, le_rfl⟩) (ordinarySource hB id ψ (1 ≤ ·)) ?_
  intro σ hs
  refine ⟨?_, le_rfl⟩
  cases hm : σ.retry
  · exact Or.inl hm
  · apply Or.inr
    change loopGuard id σ = false at hs
    simpa [loopGuard, bound, hm] using hs

/-- The success coefficient uses the original read-only input budget. -/
theorem boundedRusClassicalSuccessSourceDeriv (hB : HeraldedBlock W V α β) (ψ : UnitState Qubit) :
    SourceDerivTot (.ofEffect (fun σ => scale (successFloor hB.retryProb σ.bound) (pre ψ σ))
      (fun σ => 1 ≤ σ.bound)) (program W id) (sourceSuccessPost V ψ) :=
  successSource hB id ψ (1 ≤ ·) (fun _ h => h)

private theorem mask_true (A : Assertion Store Memory) : A.mask (fun _ => True) = A :=
  funext fun _ => A.mask_of_pos (φ := fun _ => True) trivial

/-- The ordinary fixed-cap source proof implies the masked exit triple. -/
theorem boundedRusSourceValid (hB : HeraldedBlock W V α β) (N : ℕ) (ψ : UnitState Qubit) :
    validTot (pre ψ) (program W fun _ => N) ((exitEffect V ψ).mandNot (loopGuard fun _ => N)) := by
  rw [← mask_true (pre ψ)]
  exact (boundedRusSourceDeriv hB N ψ).sound

/-- The quantitative fixed-cap source proof implies the original success triple. -/
theorem boundedRusSuccessSourceValid (hB : HeraldedBlock W V α β) (N : ℕ) (hN : 0 < N)
    (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor hB.retryProb N) (pre ψ σ))
      (program W fun _ => N) (successPost V ψ) := by
  rw [← mask_true (fun σ => scale (successFloor hB.retryProb N) (pre ψ σ))]
  exact (boundedRusSuccessSourceDeriv hB N hN ψ).sound

/-- Interpret the classical-input exit disjunction in the history semantics. -/
theorem boundedRusClassicalSourceValid (hB : HeraldedBlock W V α β) (ψ : UnitState Qubit) :
    validTot ((pre ψ).mask fun σ => 1 ≤ σ.bound) (program W id)
      ((exitEffect V ψ).mask fun σ => σ.retry = false ∨ σ.bound ≤ σ.attempts) :=
  (boundedRusClassicalSourceDeriv hB ψ).sound

/-- The classical-input quantitative proof guarantees the success floor at the stored bound. -/
theorem boundedRusClassicalSuccessSourceValid (hB : HeraldedBlock W V α β) (ψ : UnitState Qubit) :
    validTot (Assertion.mask (fun σ => scale (successFloor hB.retryProb σ.bound) (pre ψ σ))
      (fun σ => 1 ≤ σ.bound)) (program W id) (successPost V ψ) :=
  (boundedRusClassicalSuccessSourceDeriv hB ψ).sound

end HeraldedRUS

end

end QuantumProgram
