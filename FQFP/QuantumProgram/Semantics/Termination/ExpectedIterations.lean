/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting/Loops.lean: expectedIterations_eq_geometric
and expectedIterations_eq_add_geometric, as well as trace_restrict_interp_of_wp_eq and
expectedIterations_eq_of_wp_eq for a fixed exit probability on guarded inputs.
The body-level bounds use FQFP's terminal histories.
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

public import FQFP.Analysis.SpecificLimits.Geometric
public import FQFP.QuantumProgram.Logic.Assertion.Convex
public import FQFP.QuantumProgram.Semantics.Termination.WhileLossless

/-!
# Geometric bounds and exact expected loop iterations

A one-step return bound on every guarded input propagates to all iterations because
terminal-history weights are monotone and homogeneous. The resulting geometric series
starts with the mass that actually enters the loop. The body may lose trace.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} {b : Store → Bool} {p : Command Store Cell H}

/-- On an input entering the body, the second entry has the guarded terminal trace of the body. -/
theorem whileActiveMass_one_of_guard (p : Command Store Cell H) {s : CQState Store H}
    (hb : b s.store = true) :
    whileActiveMass b p 1 s =
      (Configuration.mk (some p) s).PostH (fun σ => (Assertion.identity (H := H)).mand b σ) := by
  rw [← expectation_whileActivePre, whileActivePre, Assertion.mand_of_true _ hb, expectation_wp]
  rfl

/-- A contraction of the body's guarded output bounds the ratio at every iteration. -/
theorem LoopBodyContraction.whileActiveMass_succ_le {q : ℝ≥0}
    (hc : LoopBodyContraction b p Assertion.identity q) (n : ℕ) (s : CQState Store H) :
    whileActiveMass b p (n + 1) s ≤ q * whileActiveMass b p n s := by
  unfold whileActiveMass
  rw [whileEntryWeight_succ_shift, ← whileEntryWeight_const_mul]
  refine whileEntryWeight_mono b p (fun t ht => ?_) n s
  change whileActiveMass b p 1 t ≤ (q : ℝ≥0∞) * t.mass
  rw [whileActiveMass_one_of_guard p ht]
  simpa only [Assertion.identity, CQState.expectation_one, ENNReal.ofReal_coe_nnreal] using hc t ht

/-- A fixed return ratio for one body invocation gives the same ratio at every iteration. -/
theorem whileActiveMass_succ_eq_of_return {q : ℝ≥0∞}
    (h : ∀ t : CQState Store H, b t.store = true →
      (Configuration.mk (some p) t).PostH (fun σ => (Assertion.identity (H := H)).mand b σ) =
        q * t.mass) (n : ℕ) (s : CQState Store H) :
    whileActiveMass b p (n + 1) s = q * whileActiveMass b p n s := by
  unfold whileActiveMass
  rw [whileEntryWeight_succ_shift, ← whileEntryWeight_const_mul]
  exact congrFun (whileEntryWeight_congr b p
    (fun t ht => (whileActiveMass_one_of_guard p ht).trans (h t ht)) n) s

/-- Uniform contraction geometrically bounds the mass entering the `(n + 1)`st iteration. -/
theorem LoopBodyContraction.whileActiveMass_le {q : ℝ≥0}
    (hc : LoopBodyContraction b p Assertion.identity q) (n : ℕ) (s : CQState Store H) :
    whileActiveMass b p n s ≤ (q : ℝ≥0∞) ^ n * whileActiveMass b p 0 s :=
  ENNReal.le_pow_mul_of_succ_le (f := fun k => whileActiveMass b p k s)
    (fun k => hc.whileActiveMass_succ_le k s) n

/-- An upper bound on successive entry-mass ratios for one input bounds its expected count. -/
theorem expectedIterations_le_geometric {q : ℝ≥0∞} {s : CQState Store H}
    (h : ∀ n, whileActiveMass b p (n + 1) s ≤ q * whileActiveMass b p n s) :
    expectedIterations b p s ≤ whileActiveMass b p 0 s / (1 - q) :=
  ENNReal.tsum_le_mul_inv_of_succ_le h

/-- Uniform contraction bounds expected iterations by the initial entry mass divided
by the fraction guaranteed to leave the active loop. -/
theorem LoopBodyContraction.expectedIterations_le {q : ℝ≥0}
    (hc : LoopBodyContraction b p Assertion.identity q) (s : CQState Store H) :
    expectedIterations b p s ≤ whileActiveMass b p 0 s / (1 - (q : ℝ≥0∞)) :=
  expectedIterations_le_geometric fun n => hc.whileActiveMass_succ_le n s

/-- Strict contraction gives a finite expected count on every weighted input. -/
theorem LoopBodyContraction.expectedIterations_lt_top {q : ℝ≥0}
    (hc : LoopBodyContraction b p Assertion.identity q) (hq : q < 1) (s : CQState Store H) :
    expectedIterations b p s < ∞ := by
  apply (hc.expectedIterations_le s).trans_lt
  have hq' : (q : ℝ≥0∞) < 1 := by exact_mod_cast hq
  exact ENNReal.mul_lt_top ((whileActiveMass_le_mass b p 0 s).trans_lt ENNReal.coe_lt_top)
    (ENNReal.inv_lt_top.mpr (tsub_pos_iff_lt.mpr hq'))

/-- A fixed ratio of successive entry masses for one input gives its exact expected count. -/
theorem expectedIterations_eq_geometric {q : ℝ≥0∞} {s : CQState Store H}
    (h : ∀ n, whileActiveMass b p (n + 1) s = q * whileActiveMass b p n s) :
    expectedIterations b p s = whileActiveMass b p 0 s / (1 - q) :=
  ENNReal.tsum_eq_mul_inv_of_succ h

/-- When the first return is exceptional, sum the first entry and the subsequent geometric tail. -/
theorem expectedIterations_eq_add_geometric {q : ℝ≥0∞} {s : CQState Store H}
    (h : ∀ n, whileActiveMass b p (n + 1 + 1) s = q * whileActiveMass b p (n + 1) s) :
    expectedIterations b p s = whileActiveMass b p 0 s + whileActiveMass b p 1 s / (1 - q) := by
  rw [expectedIterations, tsum_eq_zero_add' CompleteLattice.summable]
  exact congrArg _ (ENNReal.tsum_eq_mul_inv_of_succ (f := fun n => whileActiveMass b p (n + 1) s) h)

/-- A body returning a fixed fraction of each guarded input gives an exact geometric count. -/
theorem expectedIterations_eq_of_return {q : ℝ≥0∞}
    (h : ∀ t : CQState Store H, b t.store = true →
      (Configuration.mk (some p) t).PostH (fun σ => (Assertion.identity (H := H)).mand b σ) =
        q * t.mass) (s : CQState Store H) :
    expectedIterations b p s = whileActiveMass b p 0 s / (1 - q) :=
  expectedIterations_eq_geometric fun n => whileActiveMass_succ_eq_of_return h n s

/-- Returning to the guard collects the terminating trace left after counting all exits. -/
theorem Configuration.PostH_mand_identity_eq_sub (c : Configuration Store Cell H)
    (b : Store → Bool) :
    c.PostH (fun σ => (Assertion.identity (H := H)).mand b σ) = c.terminatingMass -
      c.PostH (fun σ => (Assertion.identity (H := H)).mandNot b σ) := by
  apply ENNReal.eq_sub_of_add_eq' (c.terminatingMass_le.trans_lt ENNReal.coe_lt_top).ne
  simpa only [Assertion.mand, Assertion.mandNot, Bool.not_eq_true, Assertion.identity,
    c.PostH_one] using c.PostH_mask_split Assertion.identity (fun σ => b σ = true)

private theorem coe_one_sub_mul (e m : ℝ≥0) :
    ((1 - e : ℝ≥0) : ℝ≥0∞) * m = m - (e : ℝ≥0∞) * m := by
  rw [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.sub_mul fun _ _ => ENNReal.coe_ne_top, one_mul]

private theorem one_sub_coe_one_sub {e : ℝ≥0} (he : e ≤ 1) :
    1 - ((1 - e : ℝ≥0) : ℝ≥0∞) = e := by
  rw [← ENNReal.coe_one, ← ENNReal.coe_sub, tsub_tsub_cancel_of_le he]

/-- An exit-probability lower bound on guarded inputs bounds the fraction returning to the
guard, including when some mass is lost inside the body. -/
theorem LoopBodyContraction.of_exit_probability {e : ℝ≥0} {he : e ≤ 1}
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he).mand b) p
      (Assertion.identity.mandNot b)) : LoopBodyContraction b p Assertion.identity (1 - e) := by
  intro s hb
  let c := Configuration.mk (some p) s
  have h := hexit s
  rw [Assertion.mand_of_true _ hb, s.ofReal_expectation_scaled] at h
  simp only [Assertion.identity, CQState.expectation_one, ENNReal.ofReal_coe_nnreal] at h ⊢
  rw [c.PostH_mand_identity_eq_sub, coe_one_sub_mul]
  exact tsub_le_tsub c.terminatingMass_le h

/-- A total triple certifying exit probability at least `e` bounds the weighted count by
the initial entry mass divided by `e`. -/
theorem expectedIterations_le_of_exit_probability {e : ℝ≥0} {he : e ≤ 1}
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he).mand b) p
      (Assertion.identity.mandNot b)) (s : CQState Store H) :
    expectedIterations b p s ≤ whileActiveMass b p 0 s / e := by
  simpa only [one_sub_coe_one_sub he] using
    (LoopBodyContraction.of_exit_probability hexit).expectedIterations_le s

/-- A positive exit probability bounds the expected count by a finite rate times any upper
bound on the initial entry mass. -/
theorem expectedIterations_le_inv_mul_of_exit_probability {e : ℝ≥0} (he : 0 < e) {he₁ : e ≤ 1}
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he₁).mand b) p
      (Assertion.identity.mandNot b)) {s : CQState Store H} {m : ℝ≥0∞}
    (hm : whileActiveMass b p 0 s ≤ m) :
    expectedIterations b p s ≤ (↑(e⁻¹) : ℝ≥0∞) * m := by
  rw [ENNReal.coe_inv he.ne']
  refine (expectedIterations_le_of_exit_probability hexit s).trans ?_
  rw [div_eq_mul_inv, mul_comm (whileActiveMass b p 0 s)]
  exact mul_le_mul_right hm _

/-- For a body preserving trace on guarded inputs, an exact exit WP of `e` times the identity
gives the exact weighted iteration count. -/
theorem expectedIterations_eq_of_wp_exit {e : ℝ≥0} (he : e ≤ 1)
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (hexit : ∀ σ, b σ = true →
      wp p (Assertion.identity.mandNot b) σ = (Assertion.identity.scaled e he) σ)
    (s : CQState Store H) : expectedIterations b p s = whileActiveMass b p 0 s / e := by
  have hret (t : CQState Store H) (hb : b t.store = true) :
      (Configuration.mk (some p) t).PostH (fun σ => (Assertion.identity (H := H)).mand b σ) =
        ((1 - e : ℝ≥0) : ℝ≥0∞) * t.mass := by
    rw [Configuration.PostH_mand_identity_eq_sub, (validTot_mand_identity_iff b p).mp hbody t hb,
      ← expectation_wp p (Assertion.identity.mandNot b), hexit t.store hb,
      t.ofReal_expectation_scaled, coe_one_sub_mul]
    simp only [Assertion.identity, CQState.expectation_one, ENNReal.ofReal_coe_nnreal]
  simpa only [one_sub_coe_one_sub he] using expectedIterations_eq_of_return hret s

end QuantumProgram
