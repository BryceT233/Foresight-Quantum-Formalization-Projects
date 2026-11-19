/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for bounded repeat-until-success with a heralded gate.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/HeraldedRUS.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.CountedLoop
public import FQFP.QuantumProgram.HeraldedBlock

/-!
# Bounded repeat until a heralded gate succeeds

The measured ancilla controls early exit from a counted loop. If the zero branch applies
the target with amplitude `α` and the one branch preserves the data with amplitude `β`,
then after at most `N` attempts the success probability is at least `1 − (‖β‖²)^N`.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit
open scoped ComplexOrder ENNReal

namespace QuantumProgram

open RepeatUntilSuccess (Memory measurement reset outputMap)

noncomputable section

namespace BoundedRepeatUntilSuccess

/-- A read-only input, the last ancilla outcome (one means retry), and the attempts spent. -/
structure Store where
  /-- The caller's bound when the program uses a classical input. -/
  bound : ℕ
  /-- True initially and after outcome one. -/
  retry : Bool
  /-- Number of completed measurements. -/
  attempts : ℕ

/-- Writing the attempt counter preserves the measurement and the input bound. -/
def counter : CounterLens Store :=
  ⟨Store.attempts, fun σ k => { σ with attempts := k }, fun _ _ => rfl⟩

/-- Measurement writes only the retry bit. -/
def record (i : Fin 2) (σ : Store) : Store := { σ with retry := decide (i = 1) }

/-- Arm the loop, without inspecting the incoming flag or counter. -/
def arm (σ : Store) : Store := { σ with retry := true }

/-- A successful measurement makes the effective bound zero, so counting stops immediately. -/
def bound (cap : ℕ → ℕ) (σ : Store) : ℕ := if σ.retry then cap σ.bound else 0

/-- Allow another attempt exactly while armed and below the cap. -/
def guard (cap : ℕ → ℕ) (σ : Store) : Bool := decide (σ.attempts < bound cap σ)

/-- The counted guard reads the counter only while retrying. -/
theorem guard_iff {cap : ℕ → ℕ} {σ : Store} :
    guard cap σ = true ↔ σ.retry = true ∧ σ.attempts < cap σ.bound := by
  cases h : σ.retry <;> simp [guard, bound, h]

/-- Increment after every measurement, including the successful one. -/
abbrev inc (σ : Store) : Store := counter.set σ (σ.attempts + 1)

/-- Store after measuring the ancilla and counting that attempt. -/
abbrev nextStore (σ : Store) (i : Fin 2) := inc (record i σ)

/-- The source ranking expression is integer subtraction of the attempt counter from the cap. -/
def rank (cap : ℕ → ℕ) (σ : Store) : ℤ := (cap σ.bound : ℤ) - σ.attempts

/-- Each measured successor has spent one more attempt, for either ancilla outcome. -/
theorem rank_nextStore_lt (cap : ℕ → ℕ) (σ : Store) (i : Fin 2) :
    rank cap (nextStore σ i) < rank cap σ := by
  change (cap σ.bound : ℤ) - ↑(σ.attempts + 1) < (cap σ.bound : ℤ) - σ.attempts
  lia

/-- Scale a quantum effect by a probability. -/
def scale {H : Qudit} (p : Set.Icc (0 : ℝ) 1) (E : Set.Icc (0 : Operator H) 1) :
    Set.Icc (0 : Operator H) 1 :=
  ⟨(p.val : ℂ) • E.val, smul_nonneg (Complex.zero_le_real.mpr p.2.1) E.2.1,
    (smul_le_smul_of_nonneg_right (Complex.real_le_real.mpr p.2.2) E.2.1).trans
      (by simpa using E.2.2)⟩

/-- The input effect observes the original data and accepts every ancilla. -/
def pre (ψ : UnitState Qubit) : Assertion Store Memory :=
  fun _ => RepeatUntilSuccess.pre ψ (false, true)

/-- Both outcomes spend one unit of the remaining budget. -/
theorem remaining_succ (cap : ℕ → ℕ) (σ : Store) (hk : σ.attempts < cap σ.bound) :
    cap σ.bound - σ.attempts = (cap σ.bound - (σ.attempts + 1)) + 1 := by lia

/-- Unit reward retains the original effect. -/
theorem scale_one {H : Qudit} (E : Set.Icc (0 : Operator H) 1) :
    scale 1 E = E := Subtype.ext (by simp [scale])

/-- A normalized intended input with arbitrary ancilla density and arbitrary initial store. -/
def inputState (σ : Store) (ρ : Density Qubit) (ψ : UnitState Qubit) : CQState Store Memory :=
  let d := ρ.tensor (Density.pure ψ)
  ⟨σ, d.op, d.positive⟩

/-- The intended input realizes the entire coefficient of the scaled data projector. -/
theorem expectation_pre (σ : Store) (ρ : Density Qubit) (ψ : UnitState Qubit)
    (p : Set.Icc (0 : ℝ) 1) :
    (inputState σ ρ ψ).expectation (scale p (pre ψ σ)) = p.val := by
  have h : (inputState σ ρ ψ).expectation (pre ψ σ) = 1 :=
    RepeatUntilSuccess.expectation_pre_tensor (false, true) ρ ψ
  change (((p.val : ℂ) • (pre ψ σ).val) * _).trace.re = _
  rw [smul_mul_assoc, Operator.trace, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
  change p.val * (inputState σ ρ ψ).expectation (pre ψ σ) = p.val
  rw [h, mul_one]

end BoundedRepeatUntilSuccess

namespace HeraldedRUS

open BoundedRepeatUntilSuccess
open BoundedRepeatUntilSuccess renaming guard → loopGuard

variable (W : UnitaryProgram Memory) (V : Qubit ⟶ Qubit) [IsUnitary V] {α β : ℂ}

/-- Reset the ancilla, execute the heralded block and measure the ancilla into the flag. -/
def attempt : Command Store (Fin 2) Memory :=
  .seq (.channel fun _ => reset)
    (.seq (.unitary (fun _ => id) (fun _ _ => W))
      (.measure (fun _ (_ : Fin 1) => 0) (fun _ _ => measurement) record))

/-- Use a constant cap for a fixed budget, or `id` to read the budget from the input store. -/
def program (cap : ℕ → ℕ) : Command Store (Fin 2) Memory :=
  .seq (.assign arm) (.counted counter (bound cap) (attempt W))

/-- The cap is read-only throughout initialization, measurement and counter updates. -/
theorem preserves_bound (cap : ℕ → ℕ) : (program W cap).PreservesParameters Store.bound :=
  ⟨fun _ => rfl, fun _ => rfl, ⟨trivial, trivial, fun _ _ => rfl⟩, fun _ => rfl⟩

/-- The backward effect of a complete counted attempt. -/
def bodyPre (A : Assertion Store Memory) : Assertion Store Memory :=
  let M := Assertion.measurePre (A ∘ inc) (fun _ (_ : Fin 1) => (0 : Fin 2))
    (fun _ _ => measurement) record
  (M.unitaryPre (fun _ => id (α := Fin 2)) (fun _ _ => W)).channelPre fun _ => reset

private theorem bodyDeriv (A : Assertion Store Memory) :
    DerivTot (bodyPre W A) ((attempt W).seq (.assign inc)) A :=
  .seq (.seq (.channel _ _) (.seq (.unitary _ _ _) (.measure _ _ _ _))) (.assign _ A)

/-- Unfold a counted attempt into its three quantum effect transformers. -/
theorem bodyPre_apply (A : Assertion Store Memory) (σ : Store) :
    bodyPre W A σ = channelEffect reset (channelEffect W.toChannel
      (instrumentEffect measurement fun i => A (nextStore σ i))) := by
  have hr : Function.Injective (fun _ : Fin 1 => (0 : Fin 2)) :=
    Function.injective_of_subsingleton _
  simp only [bodyPre, Assertion.channelPre, Assertion.unitaryPre, Assertion.measurePre,
    Function.injective_id, hr, dite_true, Function.comp_apply]

/-- A full attempt preserves the identity effect because both channels and the
measurement preserve total mass. -/
theorem bodyPre_identity (σ : Store) : (bodyPre W Assertion.identity σ).val = 1 := by
  have unital (f : QuantumChannel Memory Memory) : f.toCPMap.dual.toSuperoperator 1 = 1 :=
    f.toCPMap.isTracePreserving_iff_dual_one.mp f.tracePreserving
  rw [bodyPre_apply]
  change reset.toCPMap.dual.toSuperoperator
    (W.toChannel.toCPMap.dual.toSuperoperator (∑ i, measurement.toPOVM.op i)) = 1
  rw [measurement.toPOVM.sum_op, unital, unital]

/-- The success effect observes ancilla zero and the transformed data. -/
def successEffect (ψ : UnitState Qubit) : Assertion Store Memory :=
  fun _ => RepeatUntilSuccess.post V ψ (true, false)

/-- Only stores reporting a successful measurement contribute to this postcondition. -/
def successPost (ψ : UnitState Qubit) : Assertion Store Memory :=
  (successEffect V ψ).mask fun σ => σ.retry = false

/-- The probability of at least one success within the remaining attempts. -/
def successFloor (q : Set.Icc (0 : ℝ) 1) (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - q.val ^ n, sub_nonneg.mpr (pow_le_one₀ q.2.1 q.2.2), sub_le_self _ (pow_nonneg q.2.1 _)⟩

/-- The probability of exhausting the remaining attempts without success. -/
def failureWeight (q : Set.Icc (0 : ℝ) 1) (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨q.val ^ n, pow_nonneg q.2.1 _, pow_le_one₀ q.2.1 q.2.2⟩

/-- The quantum part of the invariant before imposing a classical counter bound. -/
def rewardEffect (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (win : Set.Icc (0 : ℝ) 1) (retry : ℕ → Set.Icc (0 : ℝ) 1) : Assertion Store Memory :=
  fun σ => if σ.retry then scale (retry (cap σ.bound - σ.attempts)) (pre ψ σ)
    else scale win (successEffect V ψ σ)

/-- At the retry branch the coefficient depends on the remaining attempts. On the success
branch the target state has already been obtained. The classical mask enforces the cap. -/
def invariant (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (win : Set.Icc (0 : ℝ) 1) (retry : ℕ → Set.Icc (0 : ℝ) 1) : Assertion Store Memory :=
  (rewardEffect V cap ψ win retry).mask fun σ => σ.attempts ≤ cap σ.bound

/-- A successful run returns the target. An exhausted run returns the input data with
exactly the cap spent. Neither exit can exceed the cap. -/
def post (cap : ℕ → ℕ) (ψ : UnitState Qubit) : Assertion Store Memory :=
  Assertion.mask (fun σ => if σ.retry then pre ψ σ else successEffect V ψ σ)
    fun σ => σ.attempts ≤ cap σ.bound ∧ (σ.retry = true → σ.attempts = cap σ.bound)

variable {W V}

omit [IsUnitary V] in
/-- Sum the two heralded branches at their updated stores. -/
theorem bodyPre_op (hB : HeraldedBlock W V α β) (A : Assertion Store Memory) (σ : Store) :
    (bodyPre W A σ : Operator Memory) = Operator.oneTensorHom Qubit Qubit
      (∑ i, ((if i = 0 then ‖α‖ ^ 2 else ‖β‖ ^ 2 : ℝ) : ℂ) •
        Superoperator.conjugate (outputMap V i).hom.adjoint (A (nextStore σ i))) := by
  rw [bodyPre_apply]
  exact RepeatUntilSuccess.reset_measure_effect _ _ _ hB.branch_after_reset _

/-- The backward effect at a store depends only on the two measured successors. -/
theorem bodyPre_congr (W : UnitaryProgram Memory) {A B : Assertion Store Memory} {σ : Store}
    (h : ∀ i, A (nextStore σ i) = B (nextStore σ i)) : bodyPre W A σ = bodyPre W B σ := by
  simp only [bodyPre_apply, h]

/-- Pulling back the invariant yields the reward at the previous remaining budget. -/
theorem pull_invariant (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (win : Set.Icc (0 : ℝ) 1) (retry : ℕ → Set.Icc (0 : ℝ) 1) (σ : Store)
    (hk : σ.attempts < cap σ.bound)
    (rec : ∀ n, (retry (n + 1)).val = ‖α‖ ^ 2 * win.val + ‖β‖ ^ 2 * (retry n).val) :
    (bodyPre W (invariant V cap ψ win retry) σ : Operator Memory) =
      (scale (retry (cap σ.bound - σ.attempts)) (pre ψ σ)).val := by
  rw [bodyPre_op hB, Fin.sum_univ_two]
  simp only [invariant, rewardEffect, Assertion.mask, nextStore, inc, record, counter,
    show σ.attempts + 1 ≤ cap σ.bound from hk, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change Operator.oneTensorHom Qubit Qubit
    (((‖α‖ ^ 2 : ℝ) : ℂ) • Superoperator.conjugate (outputMap V 0).hom.adjoint
      ((win.val : ℂ) • (RepeatUntilSuccess.post V ψ (true, false)).val) +
     ((‖β‖ ^ 2 : ℝ) : ℂ) • Superoperator.conjugate (outputMap V 1).hom.adjoint
      (((retry (cap σ.bound - (σ.attempts + 1))).val : ℂ) •
        (RepeatUntilSuccess.pre ψ (false, true)).val)) = _
  rw [map_smul, map_smul, RepeatUntilSuccess.pull_success, RepeatUntilSuccess.pull_retry,
    smul_smul, smul_smul, ← add_smul, map_smul]
  have hn := remaining_succ cap σ hk
  have hc := congrArg Complex.ofReal (rec (cap σ.bound - (σ.attempts + 1)))
  simp only [Complex.ofReal_add, Complex.ofReal_mul] at hc
  exact congrArg (fun c : ℂ => c • (pre ψ σ).val) (hc.symm.trans (by rw [hn]))

/-- A single ranked derivation works for every pair of terminal rewards satisfying the
one-attempt recurrence. Both measurement outcomes increment the counter exactly once. -/
theorem rankedDeriv (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit)
    (win : Set.Icc (0 : ℝ) 1) (retry : ℕ → Set.Icc (0 : ℝ) 1)
    (rec : ∀ n, (retry (n + 1)).val = ‖α‖ ^ 2 * win.val + ‖β‖ ^ 2 * (retry n).val) :
    DerivTot (fun σ => scale (retry (cap σ.bound)) (pre ψ σ)) (program W cap)
      ((invariant V cap ψ win retry).mandNot (loopGuard cap)) := by
  let J := invariant V cap ψ win retry
  apply DerivTot.seq (B := J ∘ (fun σ => counter.set σ 0))
  · apply DerivTot.conseq _ (.assign arm _) le_rfl
    intro σ
    dsimp only [Function.comp_apply, invariant, J]
    simp [Assertion.mask, rewardEffect, arm, counter, pre]
  apply DerivTot.seq (.assign _ J)
  apply DerivTot.whileLoopSource (b := loopGuard cap) (rank cap) (fun σ hk => by dsimp [rank]; lia)
  · refine .conseq ?_ (bodyDeriv W J) le_rfl
    intro σ
    cases hg : loopGuard cap σ with
    | false =>
      change (J.mand (loopGuard cap) σ : Operator Memory) ≤ _
      rw [Assertion.mand_of_false _ hg]
      exact (bodyPre W _ σ).2.1
    | true =>
      obtain ⟨hm, hk⟩ := guard_iff.mp hg
      rw [Assertion.mand_of_true _ hg]
      change (invariant V cap ψ win retry σ : Operator Memory) ≤ _
      rw [pull_invariant hB cap ψ win retry σ hk rec]
      simp [invariant, rewardEffect, Assertion.mask, hk.le, hm]
  · intro z
    refine .conseq ?_ (bodyDeriv W _) le_rfl
    intro σ
    let atRank := fun τ : Store =>
      τ.attempts ≤ cap τ.bound ∧ loopGuard cap τ = true ∧ rank cap τ = z
    by_cases hs : atRank σ
    · rw [Assertion.mask_of_pos _ (φ := atRank) hs]
      have hd (i : Fin 2) : rank cap (nextStore σ i) < z :=
        (rank_nextStore_lt cap σ i).trans_eq hs.2.2
      have he := bodyPre_congr W (A := Assertion.identity.mask fun τ => rank cap τ < z)
        (B := Assertion.identity) (σ := σ) (fun i => Assertion.mask_of_pos _ (hd i))
      change (1 : Operator Memory) ≤ _
      rw [he, bodyPre_identity]
    · change (_ : Operator Memory) ≤ _
      rw [Assertion.mask_of_neg _ (φ := atRank) hs]
      exact (bodyPre W _ σ).2.1

/-- The total derivation of the bounded RUS triple, including the zero-budget case. -/
theorem boundedRusDeriv (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (pre ψ) (program W cap) (post V cap ψ) := by
  have h := rankedDeriv hB cap ψ 1 (fun _ => 1) (fun _ => by simpa using hB.prob_add.symm)
  simp only [scale_one] at h
  refine .conseq le_rfl h ?_
  intro σ
  cases hm : σ.retry <;> by_cases hk : σ.attempts ≤ cap σ.bound
  all_goals simp [Assertion.mandNot, Assertion.mask, invariant, rewardEffect, post, loopGuard,
    bound, hm, hk, scale_one, Nat.le_antisymm_iff]

/-- Soundness gives the total triple on all input density operators and all input stores. -/
theorem boundedRusValid (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    validTot (pre ψ) (program W cap) (post V cap ψ) := (boundedRusDeriv hB cap ψ).sound

/-- The success floor satisfies the one-attempt reward recurrence. -/
theorem successFloor_succ (hB : HeraldedBlock W V α β) (n : ℕ) :
    (successFloor hB.retryProb (n + 1)).val =
      ‖α‖ ^ 2 * 1 + ‖β‖ ^ 2 * (successFloor hB.retryProb n).val := by
  change 1 - (‖β‖ ^ 2) ^ (n + 1) = ‖α‖ ^ 2 * 1 + ‖β‖ ^ 2 * (1 - (‖β‖ ^ 2) ^ n)
  rw [pow_succ]
  linarith only [hB.prob_add, mul_comm ((‖β‖ ^ 2) ^ n) (‖β‖ ^ 2)]

/-- Count only outputs carrying the target and a successful measurement. -/
theorem boundedRusSuccessDeriv (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (fun σ => scale (successFloor hB.retryProb (cap σ.bound)) (pre ψ σ))
      (program W cap) (successPost V ψ) := by
  refine DerivTot.conseq le_rfl (rankedDeriv hB cap ψ 1 (successFloor hB.retryProb)
    (successFloor_succ hB)) ?_
  intro σ
  cases hm : σ.retry
  · by_cases hk : σ.attempts ≤ cap σ.bound
    · simp [invariant, rewardEffect, Assertion.mandNot, Assertion.mask, successPost, loopGuard,
        bound, hm, hk, scale_one]
    · change _ ≤ (successPost V ψ σ).val
      simpa [invariant, Assertion.mandNot, Assertion.mask, loopGuard, bound, hm, hk] using
        (successPost V ψ σ).2.1
  · by_cases hk : σ.attempts < cap σ.bound
    · simp [Assertion.mandNot, Assertion.mask, successPost, loopGuard, bound, hm, hk]
    · have hz := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)
      apply le_of_eq
      apply Subtype.ext
      by_cases he : σ.attempts ≤ cap σ.bound <;>
        simp [invariant, rewardEffect, Assertion.mandNot, Assertion.mask, successPost, loopGuard,
          bound, hm, hk, he, hz, successFloor, scale]

/-- On any input the success post-expectation dominates the input data expectation
multiplied by `1 − (‖β‖²)^N`, for a fixed or classically supplied cap. -/
theorem boundedRusSuccess (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    validTot (fun σ => scale (successFloor hB.retryProb (cap σ.bound)) (pre ψ σ))
      (program W cap) (successPost V ψ) := (boundedRusSuccessDeriv hB cap ψ).sound

/-- The complementary ranked derivation counts only exhausted runs retaining the input data. -/
theorem boundedRusFailureDeriv (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (ψ : UnitState Qubit) :
    DerivTot (fun σ => scale (failureWeight hB.retryProb (cap σ.bound)) (pre ψ σ)) (program W cap)
      ((pre ψ).mask fun σ => σ.retry = true ∧ σ.attempts = cap σ.bound) := by
  refine DerivTot.conseq le_rfl (rankedDeriv hB cap ψ 0 (failureWeight hB.retryProb) ?_) ?_
  · intro n
    change (‖β‖ ^ 2) ^ (n + 1) = ‖α‖ ^ 2 * 0 + ‖β‖ ^ 2 * (‖β‖ ^ 2) ^ n
    rw [pow_succ]
    ring
  intro σ
  apply le_of_eq
  apply Subtype.ext
  cases hm : σ.retry <;> rcases lt_trichotomy σ.attempts (cap σ.bound) with hk | hk | hk
  all_goals simp [invariant, rewardEffect, Assertion.mandNot, Assertion.mask, loopGuard, bound,
    Nat.le_of_lt, Nat.not_le_of_gt, ne_of_lt, ne_of_gt, failureWeight, scale, *]

/-- On the intended input the classical outcome probabilities are exact. Success includes
all early exits. The remaining mass consists of runs that used the entire budget. -/
theorem outcomeProbabilities (hB : HeraldedBlock W V α β) (cap : ℕ → ℕ) (σ : Store)
    (ρ : Density Qubit) (ψ : UnitState Qubit) :
    let c := Configuration.mk (some (program W cap)) (inputState σ ρ ψ)
    let N := cap σ.bound
    let I : Assertion Store Memory := Assertion.identity
    c.PostH (fun τ => I.mask (fun s => s.retry = false) τ) =
        ENNReal.ofReal (1 - (‖β‖ ^ 2) ^ N) ∧
      c.PostH (fun τ => I.mask (fun s => s.retry = true ∧ s.attempts = cap s.bound) τ) =
        ENNReal.ofReal ((‖β‖ ^ 2) ^ N) := by
  let c := Configuration.mk (some (program W cap)) (inputState σ ρ ψ)
  let N := cap σ.bound
  let I : Assertion Store Memory := Assertion.identity
  let won := fun s : Store => s.retry = false
  let spent := fun s : Store => s.retry = true ∧ s.attempts = cap s.bound
  let S := c.PostH (fun τ => I.mask won τ)
  let F := c.PostH (fun τ => I.mask spent τ)
  let a := ENNReal.ofReal (successFloor hB.retryProb N).val
  let b := ENNReal.ofReal (failureWeight hB.retryProb N).val
  change S = a ∧ F = b
  have hS : a ≤ S := by
    refine (congrArg ENNReal.ofReal
      (expectation_pre σ ρ ψ (successFloor hB.retryProb N)).symm).le.trans
      (validTot_conseq le_rfl (boundedRusSuccess hB cap ψ) ?_ (inputState σ ρ ψ))
    exact Assertion.mask_mono (fun τ => (successEffect V ψ τ).2.2) (fun _ h => h)
  have hF : b ≤ F := by
    refine (congrArg ENNReal.ofReal
      (expectation_pre σ ρ ψ (failureWeight hB.retryProb N)).symm).le.trans
      (validTot_conseq le_rfl (boundedRusFailureDeriv hB cap ψ).sound ?_ (inputState σ ρ ψ))
    exact Assertion.mask_mono (fun τ => (pre ψ τ).2.2) (fun _ h => h)
  have hsum : S + F ≤ 1 := by
    have hf : F ≤ c.PostH (fun τ => I.mask (fun s => ¬ won s) τ) := by
      apply c.PostH_mono
      exact Assertion.mask_mono (A := I) le_rfl (fun τ (h : spent τ) => by simp [won, h.1])
    refine (add_le_add le_rfl hf).trans ?_
    rw [show S = c.PostH (fun τ => I.mask won τ) by rfl, c.PostH_mask_split]
    apply (c.PostH_le_mass (fun τ => (I τ).2.2)).trans_eq
    suffices (inputState σ ρ ψ).mass = 1 by exact_mod_cast this
    apply NNReal.eq
    change (ρ.tensor (Density.pure ψ)).op.trace.re = 1
    rw [Density.trace_one, Complex.one_re]
  have hab : a + b = 1 := by
    dsimp only [a, b]
    rw [← ENNReal.ofReal_add (successFloor hB.retryProb N).2.1 (failureWeight hB.retryProb N).2.1]
    simp [successFloor, failureWeight]
  constructor
  · apply le_antisymm _ hS
    apply ENNReal.le_of_add_le_add_right (show b ≠ ⊤ from ENNReal.ofReal_ne_top)
    exact (add_le_add le_rfl hF).trans (hsum.trans_eq hab.symm)
  · apply le_antisymm _ hF
    apply ENNReal.le_of_add_le_add_left (show a ≠ ⊤ from ENNReal.ofReal_ne_top)
    exact (add_le_add hS le_rfl).trans (hsum.trans_eq hab.symm)

end HeraldedRUS

end

end QuantumProgram
