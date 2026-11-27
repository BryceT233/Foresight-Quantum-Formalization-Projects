/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting/CostBounds.lean: CostBound and its rules.
QuantumComputation/QuantumHoareLogic/ResourceCounting/Loops.lean: expectedCost_qWhile_le,
expectedCost_qWhile_eq_mul, CostBound.qWhile and CostBound.qWhile_of_wp_eq.
The retry bound uses a lower bound on exit probability and allows trace loss inside the body.
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

public import FQFP.QuantumProgram.Logic.Iteration.For
public import FQFP.QuantumProgram.Semantics.Cost.Basic
public import FQFP.QuantumProgram.Semantics.Termination.ExpectedIterations

/-!
# Compositional bounds on expected cost

Uniform bounds scale with the input trace. Sequential bounds add and a conditional takes
the larger branch bound. A bound per loop entry combines with the expected iteration count,
including when the body can lose mass.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} {model : CostModel H} {p q : Command Store Cell H}

/-- A uniform upper bound on the expected cost per unit of input trace. -/
def CostBound (model : CostModel H) (p : Command Store Cell H) (a : ℝ≥0) : Prop :=
  ∀ s : CQState Store H, expectedCost model p s ≤ (a : ℝ≥0∞) * s.mass

/-- Add the first command's budget on the given input and the continuation's budget on
each reachable handover. -/
theorem expectedCost_seq_le_of_mem_frontier {s : CQState Store H} {a d : ℝ≥0}
    (hp : expectedCost model p s ≤ (a : ℝ≥0∞) * s.mass)
    (hq : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n →
      expectedCost model q t ≤ (d : ℝ≥0∞) * t.mass) :
    expectedCost model (p.seq q) s ≤ ((a + d : ℝ≥0) : ℝ≥0∞) * s.mass := by
  rw [ENNReal.coe_add, add_mul]
  exact (expectedCost_seq_le_add_mul_terminatingMass model p s hq).trans
    (add_le_add hp (mul_le_mul_right (Configuration.terminatingMass_le _) _))

namespace CostBound

/-- Any larger price also bounds the command. -/
theorem mono {a d : ℝ≥0} (hp : CostBound model p a) (h : a ≤ d) : CostBound model p d :=
  fun s => (hp s).trans (mul_le_mul_left (ENNReal.coe_le_coe.mpr h) _)

/-- Skipping incurs zero cost. -/
theorem skip (model : CostModel H) : CostBound model (.skip : Command Store Cell H) 0 := by
  intro s
  simp [expectedCost]

/-- Every classical assignment has its model price. -/
theorem assign (model : CostModel H) (f : Store → Store) :
    CostBound model (.assign f : Command Store Cell H) model.assignmentCost := fun _ => le_rfl

/-- Bound each channel selected by the classical store. -/
theorem channel (f : Store → QuantumChannel H H) {a : ℝ≥0}
    (h : ∀ σ, (model.channelCost (f σ) : ℝ≥0) ≤ a) :
    CostBound model (.channel f : Command Store Cell H) a :=
  fun s => mul_le_mul_left (ENNReal.coe_le_coe.mpr (h s.store)) _

/-- Only executable register selections require a bound on the unitary price. -/
theorem unitary {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) {a : ℝ≥0}
    (h : ∀ σ hr, (model.unitaryCost (U σ hr) : ℝ≥0) ≤ a) :
    CostBound model (.unitary r U) a := by
  intro s
  unfold expectedCost
  split
  · exact mul_le_mul_left (ENNReal.coe_le_coe.mpr (h _ _)) _
  · exact zero_le

/-- Bound the full instrument price once on each valid register selection. -/
theorem measure {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m)) (upd : Fin m → Store → Store)
    {a : ℝ≥0} (h : ∀ σ hr, (model.measurementCost (I σ hr) : ℝ≥0) ≤ a) :
    CostBound model (.measure r I upd) a := by
  intro s
  unfold expectedCost
  split
  · exact mul_le_mul_left (ENNReal.coe_le_coe.mpr (h _ _)) _
  · exact zero_le

/-- Sequential bounds add because at most the input trace can reach the second command. -/
theorem seq {a d : ℝ≥0} (hp : CostBound model p a) (hq : CostBound model q d) :
    CostBound model (p.seq q) (a + d) :=
  fun s => expectedCost_seq_le_of_mem_frontier (hp s) (fun _ t _ => hq t)

/-- Sum the bounds for the executed list entries, counting repeated indices with multiplicity. -/
theorem forList {ι : Type*} (l : List ι) {body : ι → Command Store Cell H} {price : ι → ℝ≥0}
    (h : ∀ i ∈ l, CostBound model (body i) (price i)) :
    CostBound model (.forList l body) (l.map price).sum := by
  induction l with
  | nil => exact skip model
  | cons i l ih =>
    exact (h i List.mem_cons_self).seq (ih fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- A uniform per-entry price bounds a finite iteration by its length times that price. -/
theorem forList_const {ι : Type*} (l : List ι) {body : ι → Command Store Cell H} {a : ℝ≥0}
    (h : ∀ i ∈ l, CostBound model (body i) a) :
    CostBound model (.forList l body) (l.length * a) := by
  simpa [List.map_const', nsmul_eq_mul] using forList (price := fun _ => a) l h

/-- A conditional costs at most the larger of its two branch bounds. -/
theorem ite (b : Store → Bool) {a d : ℝ≥0} (hp : CostBound model p a) (hq : CostBound model q d) :
    CostBound model (.ite b p q) (max a d) := by
  intro s
  rw [expectedCost_ite]
  cases hb : b s.store with
  | false => simpa [hb] using hq.mono (le_max_right _ _) s
  | true => simpa [hb] using hp.mono (le_max_left _ _) s

end CostBound

variable (b : Store → Bool) (p : Command Store Cell H)

/-- A constant price times branch trace sums to that price times the mass entering the body. -/
theorem whileEntryWeight_const_mul_mass (a : ℝ≥0∞) (n : ℕ) (s : CQState Store H) :
    whileEntryWeight b p (fun t => a * t.mass) n s = a * whileActiveMass b p n s :=
  whileEntryWeight_const_mul b p a (fun t => t.mass) n s

variable {b p}

/-- A price bound on guarded inputs bounds total spending by price times expected entries. -/
theorem expectedCost_whileDo_le {a : ℝ≥0∞}
    (h : ∀ t : CQState Store H, b t.store = true → expectedCost model p t ≤ a * t.mass)
    (s : CQState Store H) :
    expectedCost model (.whileDo b p) s ≤ a * expectedIterations b p s := by
  rw [expectedIterations, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun n => (whileEntryWeight_mono b p h n s).trans_eq
    (whileEntryWeight_const_mul_mass b p a n s)

/-- A lower price per unit of entering trace also propagates through the entire loop. -/
theorem mul_expectedIterations_le_expectedCost {a : ℝ≥0∞}
    (h : ∀ t : CQState Store H, b t.store = true → a * t.mass ≤ expectedCost model p t)
    (s : CQState Store H) :
    a * expectedIterations b p s ≤ expectedCost model (.whileDo b p) s := by
  rw [expectedIterations, ← ENNReal.tsum_mul_left]
  exact tsum_le_tsum fun n => (whileEntryWeight_const_mul_mass b p a n s).symm.le.trans
    (whileEntryWeight_mono b p h n s)

/-- An exact body price on guarded inputs gives an exact expected loop cost. -/
theorem expectedCost_whileDo_eq_mul {a : ℝ≥0∞}
    (h : ∀ t : CQState Store H, b t.store = true → expectedCost model p t = a * t.mass)
    (s : CQState Store H) :
    expectedCost model (.whileDo b p) s = a * expectedIterations b p s := by
  rw [expectedCost_whileDo_eq_tsum, expectedIterations, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => (congrFun (whileEntryWeight_congr b p h n) s).trans
    (whileEntryWeight_const_mul_mass b p a n s)

/-- A per-entry price bound and an expected entry bound multiply to give a loop budget. -/
theorem expectedCost_whileDo_le_of_expectedIterations_le {a k : ℝ≥0}
    (hp : ∀ t : CQState Store H, b t.store = true → expectedCost model p t ≤ (a : ℝ≥0∞) * t.mass)
    {s : CQState Store H} {m : ℝ≥0∞} (hk : expectedIterations b p s ≤ (k : ℝ≥0∞) * m) :
    expectedCost model (.whileDo b p) s ≤ ((a * k : ℝ≥0) : ℝ≥0∞) * m := by
  rw [ENNReal.coe_mul, mul_assoc]
  exact (expectedCost_whileDo_le hp s).trans (mul_le_mul_right hk _)

/-- A uniform bound on the expected entry count turns a body cost bound into a loop bound. -/
theorem CostBound.whileDo {a k : ℝ≥0} (hp : CostBound model p a)
    (hk : ∀ t : CQState Store H, expectedIterations b p t ≤ (k : ℝ≥0∞) * t.mass) :
    CostBound model (.whileDo b p) (a * k) :=
  fun s => expectedCost_whileDo_le_of_expectedIterations_le (fun t _ => hp t) (hk s)

/-- With exit probability at least `e > 0`, charge `a / e` on the trace entering the loop. -/
theorem expectedCost_whileDo_le_of_exit_probability {a e : ℝ≥0}
    (hp : ∀ t : CQState Store H, b t.store = true → expectedCost model p t ≤ (a : ℝ≥0∞) * t.mass)
    (he : 0 < e) {he₁ : e ≤ 1}
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he₁).mand b) p
      (Assertion.identity.mandNot b)) (s : CQState Store H) :
    expectedCost model (.whileDo b p) s ≤ ((a / e : ℝ≥0) : ℝ≥0∞) * whileActiveMass b p 0 s := by
  simpa only [div_eq_mul_inv] using expectedCost_whileDo_le_of_expectedIterations_le hp
    (expectedIterations_le_inv_mul_of_exit_probability he hexit (s := s) le_rfl)

/-- A body costing at most `a` that exits with probability at least `e > 0` gives a uniform
loop cost bound of `a / e` per unit of input trace. -/
theorem CostBound.whileDo_of_exit_probability {a e : ℝ≥0} (hp : CostBound model p a)
    (he : 0 < e) {he₁ : e ≤ 1}
    (hexit : validTot (((Assertion.identity (H := H)).scaled e he₁).mand b) p
      (Assertion.identity.mandNot b)) : CostBound model (.whileDo b p) (a / e) := by
  simpa only [div_eq_mul_inv] using hp.whileDo (fun s =>
    expectedIterations_le_inv_mul_of_exit_probability he hexit (whileActiveMass_le_mass b p 0 s))

end QuantumProgram
