/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/WP.lean: whileRecWP, its monotonicity and wp_qWhile.
The least-upper-bound proof here uses FQFP's operational semantics.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026

Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FQFP.QuantumProgram.Semantics.Precondition.Weakest

/-!
# Finite unrollings of a loop's weakest precondition

`whileWpApprox b p B n` allows at most `n` guard tests. Each invocation of the body
has its full semantics, so it may itself branch or loop. The operational weakest
precondition is the least upper bound of these approximants in the pointwise Löwner order.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}
variable (b : Store → Bool) (p : Command Store Cell H) (B : Assertion Store H)

/-- One guard test with exit assertion `B` and a continuation for the next iteration. -/
noncomputable def whileWpStep : Assertion Store H →o Assertion Store H where
  toFun X σ := if b σ then wp p X σ else B σ
  monotone' := by
    intro X Y h σ
    cases hb : b σ <;> simp [hb, wp_mono p h σ]

/-- The total-correctness precondition with fuel for `n` guard tests. -/
noncomputable def whileWpApprox : ℕ → Assertion Store H
  | 0 => Assertion.zero
  | n + 1 => whileWpStep b p B (whileWpApprox n)

/-- Increasing the number of guard tests can only increase the accepted effect. -/
theorem monotone_whileWpApprox : Monotone (whileWpApprox b p B) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact Assertion.zero_le _
  | succ n ih => exact (whileWpStep b p B).monotone ih

/-- Every finite unrolling lies below the precondition of the whole loop. -/
theorem whileWpApprox_le_wp (n : ℕ) : whileWpApprox b p B n ≤ wp (.whileDo b p) B := by
  induction n with
  | zero => exact Assertion.zero_le _
  | succ n ih =>
    intro σ
    rw [wp_whileDo b p B σ]
    exact (whileWpStep b p B).monotone ih σ

/-- A run of fewer than `n` small steps can test the outer guard at most `n` times. -/
theorem postUpTo_le_expectation_whileWpApprox (n : ℕ) (s : CQState Store H) :
    (Configuration.mk (some (.whileDo b p)) s).postUpTo n (fun σ => B σ) ≤
      ENNReal.ofReal (s.expectation (whileWpApprox b p B n s.store)) := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    cases n with
    | zero => simp [Configuration.postUpTo]
    | succ n =>
      let c := Configuration.mk (some p) s
      let loop := Command.whileDo b p
      cases hb : b s.store with
      | false =>
        have h := (Configuration.mk (some loop) s).postUpTo_le_PostH (n + 1) B.isPositive
        rw [← expectation_wp, wp_whileDo b p B s.store] at h
        simpa [whileWpApprox, whileWpStep, hb] using h
      | true =>
        rw [Configuration.postUpTo_succ_singleton (next_whileDo_of_true p hb),
          Configuration.postUpTo_seqWith]
        simp only [whileWpApprox, whileWpStep, OrderHom.coe_mk, hb, ite_true, expectation_wp]
        rw [c.PostH_eq_tsum_terminalWeightAt (whileWpApprox b p B n).isPositive]
        refine (Finset.sum_le_sum fun j _ => c.terminalWeightAt_mono j fun t => ?_).trans
          (sum_le_tsum _)
        exact (ih (n - j) (by lia) t).trans (ENNReal.ofReal_le_ofReal (t.expectation_mono
          (monotone_whileWpApprox b p B (Nat.sub_le n j) t.store)))

/-- The expectations of the guard-bounded approximants converge to the terminal expectation. -/
theorem tendsto_expectation_whileWpApprox (s : CQState Store H) :
    Tendsto (fun n => ENNReal.ofReal (s.expectation (whileWpApprox b p B n s.store))) atTop
      (𝓝 ((Configuration.mk (some (.whileDo b p)) s).PostH (fun σ => B σ))) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (Configuration.tendsto_postUpTo _ B.isPositive) tendsto_const_nhds
    (fun n => postUpTo_le_expectation_whileWpApprox b p B n s)
  intro n
  rw [← expectation_wp]
  exact ENNReal.ofReal_le_ofReal (s.expectation_mono (whileWpApprox_le_wp b p B n s.store))

/-- The loop precondition is the least upper bound of its finite guard unrollings. -/
theorem isLUB_whileWpApprox : IsLUB (Set.range (whileWpApprox b p B)) (wp (.whileDo b p) B) := by
  refine ⟨Set.forall_mem_range.mpr (whileWpApprox_le_wp b p B), fun X hX => ?_⟩
  apply Assertion.le_iff_expectation.mpr
  intro s
  apply (ENNReal.ofReal_le_ofReal_iff (s.expectation_nonneg (X.isPositive _))).mp
  rw [expectation_wp]
  exact le_of_tendsto' (tendsto_expectation_whileWpApprox b p B s) fun n =>
    ENNReal.ofReal_le_ofReal (s.expectation_mono (hX (Set.mem_range_self n) s.store))

/-- The loop precondition is the least assertion closed under one guard test. -/
theorem isLeast_whileWpStep :
    IsLeast {X | whileWpStep b p B X ≤ X} (wp (.whileDo b p) B) := by
  refine ⟨fun σ => (wp_whileDo b p B σ).ge, fun X hX => (isLUB_whileWpApprox b p B).2 ?_⟩
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact Assertion.zero_le _
  | succ n ih => exact ((whileWpStep b p B).monotone ih).trans hX

/-- Once two successive unrollings agree at every store, the finite result is exact. -/
theorem wp_whileDo_eq_of_whileWpApprox_eq_succ {n : ℕ}
    (h : whileWpApprox b p B n = whileWpApprox b p B (n + 1)) :
    wp (.whileDo b p) B = whileWpApprox b p B n :=
  le_antisymm ((isLeast_whileWpStep b p B).2 h.ge) (whileWpApprox_le_wp b p B n)

end QuantumProgram
