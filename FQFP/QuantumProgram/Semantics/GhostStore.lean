/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for execution and correctness over a store with a read-only component.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/GhostStore.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.StoreLens
public import FQFP.QuantumProgram.Semantics.Correctness

/-!
# Execution with a read-only classical parameter

Transport through `StoreLens.fst` carries the initial parameter through every occurrence
of the execution tree. A postcondition can still depend on this parameter at termination.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {S R Cell : Type*} {H : Qudit}

/-- Extend a weighted state by a classical ghost value. -/
def CQState.withGhost (s : CQState S H) (z : R) : CQState (S × R) H :=
  ⟨(s.store, z), s.op, s.positive⟩

/-- Extend a configuration, transporting its remaining command to the product store. -/
def Configuration.withGhost (c : Configuration S Cell H) (z : R) : Configuration (S × R) Cell H :=
  ⟨c.control.map (Command.mapStore StoreLens.fst), c.state.withGhost z⟩

/-- A step transports every successor, including repeated measurement outcomes, in order. -/
theorem Command.step_mapStore_fst (p : Command S Cell H) (s : CQState S H) (z : R) :
    (p.mapStore StoreLens.fst).step (s.withGhost z) = (p.step s).map (·.withGhost z) := by
  induction p with
  | skip | assign | channel => rfl
  | unitary r U =>
    by_cases hr : Function.Injective (r s.store) <;>
      simp [mapStore, step, StoreLens.fst, CQState.withGhost, Configuration.withGhost, hr,
        CQState.map]
  | measure r I upd =>
    by_cases hr : Function.Injective (r s.store) <;>
      simp [mapStore, step, measurementSuccessors, StoreLens.fst, CQState.withGhost,
        Configuration.withGhost, hr, List.map_ofFn, Function.comp_def, measurementBranch]
  | seq p q ih _ =>
    simp only [mapStore, step, ih, List.map_map]
    apply List.map_congr_left
    rintro ⟨_ | p', s'⟩ _ <;> rfl
  | ite b p q _ _ =>
    cases hb : b s.store <;>
      simp [mapStore, step, StoreLens.fst, CQState.withGhost, Configuration.withGhost, hb]
  | whileDo b p _ =>
    cases hb : b s.store <;>
      simp [mapStore, step, StoreLens.fst, CQState.withGhost, Configuration.withGhost, hb]

namespace Configuration

variable (c : Configuration S Cell H) (z : R)

/-- Adding a ghost commutes with enumerating immediate successors. -/
theorem next_withGhost : (c.withGhost z).next = c.next.map (·.withGhost z) := by
  obtain ⟨_ | p, s⟩ := c
  · rfl
  · exact p.step_mapStore_fst s z

/-- The same ghost is present at every occurrence on the depth-`n` frontier. -/
theorem frontier_withGhost (n : ℕ) :
    (c.withGhost z).frontier n = (c.frontier n).map (·.withGhost z) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [frontier, ih, List.flatMap_map, List.map_flatMap, next_withGhost]

private theorem isNone_withGhost : (c.withGhost z).control.isNone = c.control.isNone := by
  obtain ⟨_ | p, s⟩ := c <;> rfl

/-- The ghost preserves the mass terminating at each depth. -/
theorem terminalMassAt_withGhost (n : ℕ) :
    (c.withGhost z).terminalMassAt n = c.terminalMassAt n := by
  simp only [terminalMassAt, frontier_withGhost, List.filter_map, List.map_map, Function.comp_def,
    isNone_withGhost]
  rfl

/-- At a fixed depth, evaluate the terminal observable on the initial ghost slice. -/
theorem postAt_withGhost (n : ℕ) (A : S × R → Operator H) :
    (c.withGhost z).postAt n A = c.postAt n (fun σ => A (σ, z)) := by
  simp only [postAt_eq_sum_frontier, frontier_withGhost, List.filter_map, List.map_map,
    Function.comp_def, isNone_withGhost]
  rfl

/-- Terminal post-expectation is evaluated on the same ghost slice at every depth. -/
theorem PostH_withGhost (A : S × R → Operator H) :
    (c.withGhost z).PostH A = c.PostH (fun σ => A (σ, z)) := by
  simp only [PostH, postAt_withGhost]

/-- Total terminating mass is invariant under a read-only store extension. -/
theorem terminatingMass_withGhost : (c.withGhost z).terminatingMass = c.terminatingMass := by
  simp only [terminatingMass, terminalMassAt_withGhost]

/-- The remaining mass is also invariant for commands that block or diverge. -/
theorem nonterminatingMass_withGhost :
    (c.withGhost z).nonterminatingMass = c.nonterminatingMass := by
  simp only [nonterminatingMass, terminatingMass_withGhost]
  rfl

end Configuration

/-- A total triple on the product store holds exactly when it holds for every fixed parameter. -/
theorem validTot_mapStore_fst_iff (A B : Assertion (S × R) H) (p : Command S Cell H) :
    validTot A (p.mapStore StoreLens.fst) B ↔
      ∀ z, validTot (fun σ => A (σ, z)) p (fun σ => B (σ, z)) := by
  have slice (s : CQState S H) (z : R) :=
    (Configuration.mk (some p) s).PostH_withGhost z (fun σ => (B σ : Operator H))
  constructor
  · intro h z s
    exact (h (s.withGhost z)).trans_eq (slice s z)
  · rintro h ⟨⟨σ, z⟩, ρ, hρ⟩
    exact (h z ⟨σ, ρ, hρ⟩).trans_eq (slice ⟨σ, ρ, hρ⟩ z).symm

/-- Partial correctness on a product store is equivalent to partial correctness on all slices. -/
theorem validPar_mapStore_fst_iff (A B : Assertion (S × R) H) (p : Command S Cell H) :
    validPar A (p.mapStore StoreLens.fst) B ↔
      ∀ z, validPar (fun σ => A (σ, z)) p (fun σ => B (σ, z)) := by
  have slice (s : CQState S H) (z : R) := congrArg₂ (· + ·)
    ((Configuration.mk (some p) s).PostH_withGhost z (fun σ => (B σ : Operator H)))
    ((Configuration.mk (some p) s).nonterminatingMass_withGhost z)
  constructor
  · intro h z s
    exact (h (s.withGhost z)).trans_eq (slice s z)
  · rintro h ⟨⟨σ, z⟩, ρ, hρ⟩
    exact (h z ⟨σ, ρ, hρ⟩).trans_eq (slice ⟨σ, ρ, hρ⟩ z).symm

end QuantumProgram
