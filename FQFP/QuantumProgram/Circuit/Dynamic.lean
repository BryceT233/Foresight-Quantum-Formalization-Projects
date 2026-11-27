/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.Cost.Bounds
public import FQFP.QuantumProgram.Semantics.Frame.Register

/-!
# Finite dynamic circuits on ordered registers

The native gate alphabet determines each instruction's ordered operands. The syntax retains
these operands and gate identities through measurement and classical branching. Compilation
interprets each gate as a local unitary program and each measurement label as an instrument
with a classical store update. Static queries only inspect the labels and operands.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- Instruments on an ordered selection of sites, indexed by their number of outcomes. -/
abbrev RegisterInstrument {n : ℕ} (D : Fin n → Qudit) {k : ℕ} (r : Fin k ↪ Fin n) (m : ℕ) :=
  Instrument (tensorMemory (D ∘ r)) (tensorMemory (D ∘ r)) (Fin m)

/-- The local instrument and classical writeback specified by a measurement label.
Circuits with freely chosen updates can also use this structure directly as their label type. -/
structure RegisterReadout (Store : Type*) {n : ℕ} (D : Fin n → Qudit) {k : ℕ}
    (r : Fin k ↪ Fin n) (m : ℕ) where
  /-- Instrument acting on the selected sites. -/
  instrument : RegisterInstrument D r m
  /-- Record the observed outcome in the classical store. -/
  update : Fin m → Store → Store

/-- A loop-free circuit with named gates, local measurements and classical control. -/
inductive DynamicCircuit (Store : Type*) {n : ℕ}
    (Measurement : {k : ℕ} → (Fin k ↪ Fin n) → ℕ → Type*) {Gate : Type*}
    (operands : Gate → (k : ℕ) × (Fin k ↪ Fin n)) where
  /-- The empty circuit. -/
  | skip
  /-- One instruction from the native gate alphabet. -/
  | gate (g : Gate)
  /-- Measure the selected sites and write the outcome into the store. -/
  | measure {k m : ℕ} (r : Fin k ↪ Fin n) (label : Measurement r m)
  /-- Run the circuits in sequence. -/
  | seq (first second : DynamicCircuit Store (@Measurement) operands)
  /-- Select a circuit by testing the classical store. -/
  | ite (guard : Store → Bool) (yes no : DynamicCircuit Store (@Measurement) operands)

namespace DynamicCircuit

variable {Store Gate : Type*} {n : ℕ} {Measurement : {k : ℕ} → (Fin k ↪ Fin n) → ℕ → Type*}
  {operands : Gate → (k : ℕ) × (Fin k ↪ Fin n)}

/-- Execute a list of native gates in order. -/
def ofList (gs : List Gate) : DynamicCircuit Store Measurement operands :=
  gs.foldr (fun g rest => .seq (.gate g) rest) .skip

/-- All wires mentioned by the circuit, including both arms of each conditional. -/
def support : DynamicCircuit Store Measurement operands → Finset (Fin n)
  | .skip => ∅
  | .gate g => Finset.univ.map (operands g).2
  | .measure r _ => Finset.univ.map r
  | .seq p q | .ite _ p q => p.support ∪ q.support

/-- A wire appears in a straight-line circuit exactly when an instruction mentions it. -/
theorem mem_support_ofList (gs : List Gate) (i : Fin n) :
    i ∈ (ofList (Store := Store) (Measurement := Measurement) (operands := operands) gs).support ↔
      ∃ g ∈ gs, i ∈ Set.range (operands g).2 := by
  induction gs with
  | nil => simp [ofList, support]
  | cons g gs ih =>
    change i ∈ Finset.univ.map (operands g).2 ∪ (ofList gs).support ↔ _
    simp [ih, Set.mem_range, eq_comm]

/-- A static upper bound on the number of selected native gates along any one execution. -/
def gateCountBound (select : Gate → Bool) : DynamicCircuit Store Measurement operands → ℕ
  | .skip | .measure .. => 0
  | .gate g => if select g then 1 else 0
  | .seq p q => p.gateCountBound select + q.gateCountBound select
  | .ite _ p q => max (p.gateCountBound select) (q.gateCountBound select)

/-- On a straight-line gate list the bound counts exactly the selected instructions. -/
theorem gateCountBound_ofList (gs : List Gate) (select : Gate → Bool) :
    (ofList (Store := Store) (Measurement := Measurement) (operands := operands) gs).gateCountBound
      select = gs.countP select := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [ofList, List.foldr_cons, gateCountBound, List.countP_cons] at *
    cases select g <;> simp [*, Nat.add_comm]

variable {D : Fin n → Qudit}
  (localGate : (g : Gate) → UnitaryProgram (tensorMemory (D ∘ (operands g).2)))
  (localMeasure : ∀ {k m} (r : Fin k ↪ Fin n), Measurement r m → RegisterReadout Store D r m)

/-- Compile each native gate as one local unitary instruction on its declared operands. -/
noncomputable def compile :
    DynamicCircuit Store Measurement operands → Command Store (Fin n) (tensorMemory D)
  | .skip => .skip
  | .gate g => .unitaryOnRegister D (operands g).2 (localGate g).denoteEnd
  | .measure r label =>
      let readout := localMeasure r label
      .measureOnRegister D r readout.instrument readout.update
  | .seq p q => .seq (compile p) (compile q)
  | .ite b p q => .ite b (compile p) (compile q)

/-- The compiled command obeys the static count whenever its primitive prices do. -/
theorem costBound_compile (c : DynamicCircuit Store Measurement operands)
    (select : Gate → Bool) (model : CostModel (tensorMemory D))
    (hg : ∀ g, model.unitaryCost (.liftGate (orderedLift D (operands g).2) (localGate g).denoteEnd)
      ≤ (if select g then 1 else 0))
    (hm : ∀ {m} (I : Instrument (tensorMemory D) (tensorMemory D) (Fin m)),
      model.measurementCost I = 0) :
    CostBound model (c.compile localGate localMeasure) (c.gateCountBound select) := by
  induction c with
  | skip => simpa only [compile, gateCountBound, Nat.cast_zero] using CostBound.skip model
  | gate g =>
    apply CostBound.unitary
    intro σ hi
    exact_mod_cast hg g
  | measure r label =>
    apply CostBound.measure
    intro σ hi
    simp [hm, gateCountBound]
  | seq p q hp hq => simpa only [compile, gateCountBound, Nat.cast_add] using hp.seq hq
  | ite b p q hp hq => simpa only [compile, gateCountBound, Nat.cast_max] using hp.ite b hq

/-- Compiling a circuit preserves any register disjoint from its syntactic support. -/
theorem avoidsRegister_compile (c : DynamicCircuit Store Measurement operands)
    (R : Finset (Fin n))
    (hd : Disjoint c.support R) :
    (c.compile localGate localMeasure).AvoidsRegister D (fun _ => ↑R) := by
  induction c with
  | skip => exact .skip
  | gate g =>
    apply Command.AvoidsRegister.unitary
    exact fun _ _ j => Finset.disjoint_left.mp hd (Finset.mem_map_of_mem _ (Finset.mem_univ j))
  | measure r label =>
    apply Command.AvoidsRegister.measure
    exact fun _ _ j => Finset.disjoint_left.mp hd (Finset.mem_map_of_mem _ (Finset.mem_univ j))
  | seq p q hp hq =>
    exact .seq (hp (Finset.disjoint_union_left.mp hd).1) (hq (Finset.disjoint_union_left.mp hd).2)
  | ite b p q hp hq =>
    exact .ite b (hp (Finset.disjoint_union_left.mp hd).1) (hq (Finset.disjoint_union_left.mp hd).2)

end DynamicCircuit

end QuantumProgram
