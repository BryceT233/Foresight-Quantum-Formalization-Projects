/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting.lean: CostModel.ofOracle,
CostModel.ofEmbeddedOracle and its unitary price on register embeddings.
Here the prices compare qudit operators and the command semantics checks dynamic register addresses.
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

public import FQFP.QuantumProgram.Register.OrderedChannel
public import FQFP.QuantumProgram.Semantics.Cost.Comparison

/-!
# Counting queries to unitary oracles

An executed unitary instruction contributes its input trace when its whole-memory operator
matches a target. The targets for an embedded oracle are all its ordered register lifts in a
homogeneous qudit memory. Coincident lifts count once even if several placements realize them.
-/

@[expose] public section

open CategoryTheory Qudit
open scoped ENNReal

namespace QuantumProgram

variable {H S : Qudit} {Store Cell : Type*}

namespace CostModel

open Classical in
/-- Charge one for a unitary instruction whose denotation belongs to the target set. -/
noncomputable def countUnitaries (targets : Set (Operator H)) : CostModel H where
  unitaryCost U := if U.toOperator ∈ targets then 1 else 0

/-- Enlarging the target set increases the counting model pointwise. -/
theorem countUnitaries_mono {A B : Set (Operator H)} (h : A ⊆ B) :
    countUnitaries A ≤ countUnitaries B := by
  refine ⟨le_rfl, le_rfl, fun U => ?_, fun _ => le_rfl⟩
  by_cases hU : U.toOperator ∈ A
  · simp [countUnitaries, hU, h hU]
  · simp [countUnitaries, hU]

/-- Counting selected instructions charges at most the price of counting every unitary. -/
theorem countUnitaries_le_unitaryCount (A : Set (Operator H)) :
    countUnitaries A ≤ unitaryCount H := by
  refine ⟨le_rfl, le_rfl, fun U => ?_, fun _ => le_rfl⟩
  by_cases hU : U.toOperator ∈ A <;> simp [countUnitaries, unitaryCount, hU]

/-- Count uses of a fixed whole-memory oracle by equality of its denoted operator. -/
noncomputable def ofOracle (oracle : UnitaryProgram H) : CostModel H :=
  countUnitaries {oracle.toOperator}

/-- A gate with the oracle's operator costs one, including when it has different syntax. -/
theorem ofOracle_unitaryCost (oracle U : UnitaryProgram H) :
    (ofOracle oracle).unitaryCost U = open Classical in
      if U.toOperator = oracle.toOperator then 1 else 0 := by
  classical
  simp [ofOracle, countUnitaries]

/-- Count an oracle at any ordered selection of `k` distinct sites in `n` copies of `S`. -/
noncomputable def ofEmbeddedOracle (S : Qudit) {k : ℕ} (n : ℕ)
    (oracle : UnitaryProgram (tensorMemory (fun _ : Fin k => S))) :
    CostModel (tensorMemory (fun _ : Fin n => S)) :=
  countUnitaries (Set.range fun r : Fin k ↪ Fin n =>
    orderedLift (fun _ => S) r oracle.toOperator)

/-- Every valid placement realizes one of the target operators. -/
theorem ofEmbeddedOracle_unitaryCost_liftGate {n k : ℕ}
    (oracle : UnitaryProgram (tensorMemory (fun _ : Fin k => S))) (r : Fin k ↪ Fin n) :
    (ofEmbeddedOracle S n oracle).unitaryCost
      (.liftGate (orderedLift (fun _ => S) r) oracle.denoteEnd) = 1 := by
  classical
  exact ite_eq_left (Set.mem_range.mpr ⟨r, rfl⟩)

end CostModel

/-- A dynamically addressed instruction contributes its trace exactly when it can execute
and the evaluated whole-memory operator belongs to the selected set. -/
theorem expectedCost_countUnitaries_unitary (targets : Set (Operator H)) {k : ℕ}
    (cells : Store → Fin k → Cell) (U : ∀ σ, Function.Injective (cells σ) → UnitaryProgram H)
    (s : CQState Store H) : expectedCost (.countUnitaries targets) (.unitary cells U) s =
      open Classical in
        if ∃ hi : Function.Injective (cells s.store), (U s.store hi).toOperator ∈ targets then
          (s.mass : ℝ≥0∞) else 0 := by
  classical
  by_cases hi : Function.Injective (cells s.store)
  · by_cases hU : (U s.store hi).toOperator ∈ targets <;>
      simp [expectedCost, CostModel.countUnitaries, hi, hU]
  · simp [expectedCost, hi]

/-- A statically placed instruction is tested against the targets after register lifting. -/
theorem expectedCost_countUnitaries_unitaryOnRegister {n k : ℕ} (D : Fin n → Qudit)
    (targets : Set (Operator (tensorMemory D))) (r : Fin k ↪ Fin n)
    (U : UnitaryProgram (tensorMemory (D ∘ r))) (s : CQState Store (tensorMemory D)) :
    expectedCost (.countUnitaries targets) (.unitaryOnRegister D r U.denoteEnd) s =
      open Classical in if orderedLift D r U.toOperator ∈ targets then (s.mass : ℝ≥0∞) else 0 := by
  classical
  rw [Command.unitaryOnRegister, Command.unitaryOn, expectedCost_countUnitaries_unitary]
  by_cases h : orderedLift D r U.toOperator ∈ targets
  · exact (ite_eq_left ⟨r.injective, h⟩).trans (ite_eq_left h).symm
  · exact (ite_eq_right fun ⟨_, hh⟩ => h hh).trans (ite_eq_right h).symm

/-- On a list of statically placed gates, count exactly those whose lifted operators match.
The gate width, site types and placement can all vary from one list entry to the next. -/
theorem expectedCost_countUnitaries_forList {ι : Type*} {n : ℕ} (D : Fin n → Qudit)
    (targets : Set (Operator (tensorMemory D))) (l : List ι) {width : ι → ℕ}
    (r : ∀ i, Fin (width i) ↪ Fin n) (U : ∀ i, UnitaryProgram (tensorMemory (D ∘ r i)))
    (s : CQState Store (tensorMemory D)) :
    expectedCost (.countUnitaries targets)
      (.forList l fun i => .unitaryOnRegister D (r i) (U i).denoteEnd) s = open Classical in
        (l.countP fun i => decide (orderedLift D (r i) (U i).toOperator ∈ targets)) *
          (s.mass : ℝ≥0∞) := by
  classical
  let selected (i : ι) := orderedLift D (r i) (U i).toOperator ∈ targets
  let price (i : ι) : ℝ≥0∞ := if selected i then 1 else 0
  rw [expectedCost_forList_eq_sum (price := price)]
  · apply congrArg (· * (s.mass : ℝ≥0∞))
    change (l.map price).sum = (l.countP fun i => decide (selected i) : ℕ)
    induction l with
    | nil => simp
    | cons i l ih =>
      by_cases hi : selected i <;> simp [ih, price, hi, add_comm]
  · intro i _
    exact Lossless.unitary _ (fun _ => (r i).injective)
  · intro i _ t
    rw [expectedCost_countUnitaries_unitaryOnRegister]
    change (if selected i then (t.mass : ℝ≥0∞) else 0) = price i * t.mass
    by_cases hi : selected i <;> simp [price, hi]

variable {n k : ℕ} (oracle : UnitaryProgram (tensorMemory (fun _ : Fin k => S)))

/-- Dynamic placements of this oracle charge the input trace if the addresses are distinct. -/
theorem expectedCost_ofEmbeddedOracle_unitaryOn (cells : Store → Fin k → Fin n)
    (s : CQState Store (tensorMemory (fun _ : Fin n => S))) :
    expectedCost (.ofEmbeddedOracle S n oracle)
      (.unitaryOn (fun _ => S) cells (fun _ _ => oracle.denoteEnd)) s = open Classical in
        if Function.Injective (cells s.store) then (s.mass : ℝ≥0∞) else 0 := by
  classical
  by_cases hi : Function.Injective (cells s.store) <;>
    simp [Command.unitaryOn, expectedCost, hi, CostModel.ofEmbeddedOracle_unitaryCost_liftGate]

/-- A finite sequence of valid, possibly store-dependent placements makes one oracle call per
list occurrence, including repeated placements. -/
theorem expectedCost_forList_ofEmbeddedOracle {ι : Type*} (l : List ι)
    (cells : ι → Store → Fin k → Fin n) (hr : ∀ i ∈ l, ∀ σ, Function.Injective (cells i σ))
    (s : CQState Store (tensorMemory (fun _ : Fin n => S))) :
    expectedCost (.ofEmbeddedOracle S n oracle)
      (.forList l fun i => .unitaryOn (fun _ => S) (cells i) (fun _ _ => oracle.denoteEnd)) s =
        (l.length : ℝ≥0∞) * s.mass := by
  classical
  simpa only [mul_one] using expectedCost_forList_eq_length_mul
    (.ofEmbeddedOracle S n oracle) l
    (fun i => .unitaryOn (fun _ => S) (cells i) (fun _ _ => oracle.denoteEnd)) 1
    (fun i hi => Lossless.unitary _ (hr i hi))
    (fun i hi t => by simp [expectedCost_ofEmbeddedOracle_unitaryOn, hr i hi]) s

end QuantumProgram
