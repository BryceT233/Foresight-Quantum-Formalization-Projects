/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting.lean: CostModel and expectedCost.
QuantumComputation/QuantumHoareLogic/ResourceCounting/Loops.lean: expectedCost_qWhile_eq_tsum.
The local semantics sums continuation costs over terminal histories of each command.
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

public import FQFP.QuantumProgram.Semantics.Execution.While

/-!
# Expected resource costs of quantum commands

Primitive operations charge their price times the input trace. An invalid register blocks
the operation before it incurs a charge. Classical control and guard tests are free.
The cost of a sequence includes everything its first command spends, even on diverging runs.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

/-- Natural-number prices for executed primitives. The channel price also covers initialization
commands expressed as channels. Unspecified prices default to zero. -/
structure CostModel (H : Qudit) where
  /-- Price of a classical assignment. -/
  assignmentCost : ℕ := 0
  /-- Price of an evaluated whole-memory channel. -/
  channelCost : QuantumChannel H H → ℕ := fun _ => 0
  /-- Price of a unitary instruction on the selected register. -/
  unitaryCost : UnitaryProgram H → ℕ := fun _ => 0
  /-- Price of a measurement, charged once before branching on the outcome. -/
  measurementCost {m : ℕ} : Instrument H H (Fin m) → ℕ := fun _ => 0

/-- Count applications of unitary instructions along an execution. -/
def CostModel.unitaryCount (H : Qudit) : CostModel H where
  unitaryCost _ := 1

variable {Store Cell : Type*} {H : Qudit}

/-- Branch-weighted expected cost, including costs incurred before blocking or divergence. -/
noncomputable def expectedCost (model : CostModel H) : Command Store Cell H → CQState Store H → ℝ≥0∞
  | .skip, _ => 0
  | .assign _, s => model.assignmentCost * (s.mass : ℝ≥0∞)
  | .channel f, s => model.channelCost (f s.store) * (s.mass : ℝ≥0∞)
  | .unitary r U, s => open Classical in
      if h : Function.Injective (r s.store) then model.unitaryCost (U s.store h) * (s.mass : ℝ≥0∞)
      else 0
  | .measure r I _, s => open Classical in
      if h : Function.Injective (r s.store) then
        model.measurementCost (I s.store h) * (s.mass : ℝ≥0∞) else 0
  | .seq p q, s => expectedCost model p s + p.outputWeight (expectedCost model q) s
  | .ite b p q, s => if b s.store then expectedCost model p s else expectedCost model q s
  | .whileDo b p, s => ∑' n, whileEntryWeight b p (expectedCost model p) n s

variable (model : CostModel H) (b : Store → Bool) (p : Command Store Cell H) (s : CQState Store H)

/-- A sequence charges its first command and continues charging at each terminal occurrence. -/
theorem expectedCost_seq (q : Command Store Cell H) :
    expectedCost model (p.seq q) s = expectedCost model p s +
      p.outputWeight (expectedCost model q) s := rfl

/-- A continuation price bound at reachable handovers scales with the first command's
terminating trace. -/
theorem expectedCost_seq_le_add_mul_terminatingMass {q : Command Store Cell H} {a : ℝ≥0∞}
    (h : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n →
      expectedCost model q t ≤ a * t.mass) :
    expectedCost model (p.seq q) s ≤ expectedCost model p s +
      a * (Configuration.mk (some p) s).terminatingMass := by
  rw [expectedCost_seq, ← p.outputWeight_const_mul_mass]
  exact add_le_add le_rfl (p.outputWeight_le_of_mem_frontier h)

/-- An exact continuation price at reachable handovers is charged on the first command's
terminating trace. -/
theorem expectedCost_seq_eq_add_mul_terminatingMass {q : Command Store Cell H} {a : ℝ≥0∞}
    (h : ∀ n t, ⟨none, t⟩ ∈ (Configuration.mk (some p) s).frontier n →
      expectedCost model q t = a * t.mass) :
    expectedCost model (p.seq q) s = expectedCost model p s +
      a * (Configuration.mk (some p) s).terminatingMass := by
  rw [expectedCost_seq, ← p.outputWeight_const_mul_mass]
  exact congrArg (expectedCost model p s + ·) (p.outputWeight_congr_of_mem_frontier h)

/-- Regrouping a sequence preserves the expected cost, even when a command can lose trace. -/
theorem expectedCost_seq_assoc (q r : Command Store Cell H) :
    expectedCost model ((p.seq q).seq r) s = expectedCost model (p.seq (q.seq r)) s := by
  simp only [expectedCost_seq, Command.outputWeight_seq, add_assoc]
  exact congrArg (expectedCost model p s + ·) (p.outputWeight_add _ _ s).symm

/-- The guard has no cost, so a conditional charges only the selected branch. -/
theorem expectedCost_ite (q : Command Store Cell H) :
    expectedCost model (.ite b p q) s = expectedCost model (if b s.store then p else q) s := by
  cases hb : b s.store <;> simp [expectedCost, hb]

/-- Each visit contributes the cost of running the body on that visit's weighted input. -/
theorem expectedCost_whileDo_eq_tsum :
    expectedCost model (.whileDo b p) s = ∑' n, whileEntryWeight b p (expectedCost model p) n s :=
  rfl

/-- The unbounded loop cost is the supremum of the costs charged at its first `k` entries. -/
theorem expectedCost_whileDo_eq_iSup :
    expectedCost model (.whileDo b p) s =
      ⨆ k, ∑ n ∈ Finset.range k, whileEntryWeight b p (expectedCost model p) n s :=
  ENNReal.tsum_eq_iSup_nat

/-- Unrolling a loop charges the first body invocation and resumes at each of its exits. -/
theorem expectedCost_whileDo :
    expectedCost model (.whileDo b p) s = if b s.store then
      expectedCost model p s + p.outputWeight (expectedCost model (.whileDo b p)) s else 0 := by
  rw [expectedCost_whileDo_eq_tsum, tsum_eq_zero_add' CompleteLattice.summable]
  cases hb : b s.store <;> simp [whileEntryWeight, hb, expectedCost, Command.outputWeight_tsum]

end QuantumProgram
