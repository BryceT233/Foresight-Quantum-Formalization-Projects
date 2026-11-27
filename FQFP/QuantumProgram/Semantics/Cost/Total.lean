/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting.lean: TotalExpectedCostLe.
QuantumComputation/QuantumHoareLogic/ResourceCounting/Loops.lean:
CostBound.qWhile_totalExpectedCostLe. The local retry rule uses a lower bound on the exit
probability and requires a body specification only on guarded inputs.
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

public import FQFP.QuantumProgram.Semantics.Cost.Bounds

/-!
# Almost-sure termination with a finite expected cost

A specification at a single input records both the terminating trace and a finite budget per unit
of input trace. In a sequence the continuation needs a specification only at actual handovers.
For a loop one can certify termination by bounding the iteration count, or by charging a
positive minimum price on each guarded input and bounding the total expected cost.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} {model : CostModel H} {p q : Command Store Cell H}
    {s : CQState Store H} {b : Store → Bool}

/-- The full input trace terminates, and the expected cost is at most the stated price per
unit of input trace. -/
@[mk_iff] structure TotalExpectedCostLe (model : CostModel H) (p : Command Store Cell H)
    (s : CQState Store H) (a : ℝ≥0) : Prop where
  /-- All input trace is returned on terminating histories. -/
  terminatingMass_eq : (Configuration.mk (some p) s).terminatingMass = s.mass
  /-- Costs incurred along all histories fit in the input's trace-scaled budget. -/
  expectedCost_le : expectedCost model p s ≤ (a : ℝ≥0∞) * s.mass

/-- Uniform total resource specifications are exactly losslessness and a uniform cost bound. -/
theorem forall_totalExpectedCostLe_iff {a : ℝ≥0} :
    (∀ t, TotalExpectedCostLe model p t a) ↔ Lossless p ∧ CostBound model p a :=
  ⟨fun h => ⟨fun t => (h t).terminatingMass_eq, fun t => (h t).expectedCost_le⟩,
    fun ⟨hl, hc⟩ t => ⟨hl t, hc t⟩⟩

/-- A positive minimum body price turns a finite expected cost on one input into a finite
expected number of entries on that input. -/
theorem expectedIterations_lt_top_of_expectedCost_lt_top {a : ℝ≥0∞} (ha : 0 < a)
    (hprice : ∀ t : CQState Store H, b t.store = true → a * t.mass ≤ expectedCost model p t)
    (hcost : expectedCost model (.whileDo b p) s < ∞) : expectedIterations b p s < ∞ :=
  ENNReal.lt_top_of_mul_ne_top_right ((mul_expectedIterations_le_expectedCost hprice s).trans_lt
    hcost).ne ha.ne'

/-- With a positive minimum price and a finite maximum price, finite expected cost and finite
expected iteration count are equivalent, including for bodies that may lose trace. -/
theorem expectedCost_whileDo_lt_top_iff {a d : ℝ≥0} (ha : 0 < a)
    (hmin : ∀ t : CQState Store H, b t.store = true → (a : ℝ≥0∞) * t.mass ≤ expectedCost model p t)
    (hmax : ∀ t : CQState Store H, b t.store = true →
      expectedCost model p t ≤ (d : ℝ≥0∞) * t.mass) :
    expectedCost model (.whileDo b p) s < ∞ ↔ expectedIterations b p s < ∞ :=
  ⟨expectedIterations_lt_top_of_expectedCost_lt_top (ENNReal.coe_pos.mpr ha) hmin,
    fun h => (expectedCost_whileDo_le hmax s).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top h)⟩

namespace TotalExpectedCostLe

/-- Any larger finite budget suffices for the same execution. -/
theorem mono {a d : ℝ≥0} (hp : TotalExpectedCostLe model p s a) (had : a ≤ d) :
    TotalExpectedCostLe model p s d :=
  ⟨hp.terminatingMass_eq, hp.expectedCost_le.trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr had) _)⟩

/-- Add the budgets for a sequence, checking the second command at each reachable handover. -/
theorem seq {a d : ℝ≥0} (hp : TotalExpectedCostLe model p s a)
    (hq : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n →
      TotalExpectedCostLe model q t d) : TotalExpectedCostLe model (p.seq q) s (a + d) := by
  have hmass := (Configuration.mk (some p) s).terminatingMass_seqWith_eq_of_mem_frontier q
    (fun n t ht => (hq n t ht).terminatingMass_eq)
  exact ⟨hmass.trans hp.terminatingMass_eq,
    expectedCost_seq_le_of_mem_frontier hp.expectedCost_le
      (fun n t ht => (hq n t ht).expectedCost_le)⟩

/-- A finite list of uniformly certified commands terminates within the sum of their budgets. -/
theorem forList {ι : Type*} (l : List ι) {body : ι → Command Store Cell H} {price : ι → ℝ≥0}
    (h : ∀ i ∈ l, ∀ t, TotalExpectedCostLe model (body i) t (price i)) :
    TotalExpectedCostLe model (.forList l body) s (l.map price).sum :=
  ⟨Lossless.forList l (fun i hi t => (h i hi t).terminatingMass_eq) s,
    CostBound.forList l (fun i hi t => (h i hi t).expectedCost_le) s⟩

/-- A conditional has a total resource specification exactly when its selected branch does. -/
theorem ite_iff (b : Store → Bool) (a : ℝ≥0) :
    TotalExpectedCostLe model (.ite b p q) s a ↔
      TotalExpectedCostLe model (if b s.store then p else q) s a := by
  simp only [totalExpectedCostLe_iff, Configuration.terminatingMass_ite, expectedCost_ite]

/-- A finite expected entry bound at the given input multiplies the price of a guarded body. -/
theorem whileDo_of_expectedIterations_le {a k : ℝ≥0}
    (hbody : ∀ t : CQState Store H, b t.store = true → TotalExpectedCostLe model p t a)
    (hk : expectedIterations b p s ≤ (k : ℝ≥0∞) * s.mass) :
    TotalExpectedCostLe model (.whileDo b p) s (a * k) := by
  have hl := (validTot_mand_identity_iff b p).mpr fun t ht => (hbody t ht).terminatingMass_eq
  exact ⟨terminatingMass_whileDo_eq_of_expectedIterations_ne_top hl
    (hk.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top)).ne,
    expectedCost_whileDo_le_of_expectedIterations_le (fun t ht => (hbody t ht).expectedCost_le) hk⟩

/-- A finite budget for the loop suffices when guarded bodies return their full trace
and incur a positive minimum charge per unit of entering trace. -/
theorem whileDo_of_cost_le {a : ℝ≥0∞} {d : ℝ≥0} (ha : 0 < a)
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (hprice : ∀ t : CQState Store H, b t.store = true → a * t.mass ≤ expectedCost model p t)
    (hcost : expectedCost model (.whileDo b p) s ≤ (d : ℝ≥0∞) * s.mass) :
    TotalExpectedCostLe model (.whileDo b p) s d := by
  refine ⟨terminatingMass_whileDo_eq_of_expectedIterations_ne_top hbody ?_, hcost⟩
  exact (expectedIterations_lt_top_of_expectedCost_lt_top ha hprice
    (hcost.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top))).ne

/-- A positive lower bound on exit probability yields both full termination and a finite
retry budget. The body specification is required only when the guard is true. -/
theorem whileDo_of_exit_probability {a e : ℝ≥0} (he : 0 < e) {he₁ : e ≤ 1}
    (hbody : ∀ t : CQState Store H, b t.store = true → TotalExpectedCostLe model p t a)
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he₁).mand b) p
      (Assertion.identity.mandNot b)) (s : CQState Store H) :
    TotalExpectedCostLe model (.whileDo b p) s (a / e) := by
  simpa only [div_eq_mul_inv] using whileDo_of_expectedIterations_le hbody
    (expectedIterations_le_inv_mul_of_exit_probability he hexit (whileActiveMass_le_mass b p 0 s))

end TotalExpectedCostLe

end QuantumProgram
