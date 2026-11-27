/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the terminal operator at a given store and depth.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/Denotation.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Execution.Mass
public import FQFP.QuantumProgram.Semantics.Execution.History

/-!
# Finite-depth output by classical store

The operator assigned to a final store sums the positive operators of all matching terminal
occurrences, as in `Qhl/History/Denotation.lean`. Terminal histories can also be used to
compute the trace at each depth.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.Configuration

variable {Store Cell : Type*} {H : Qudit} (c : Configuration Store Cell H)

/-- Terminal mass can be summed directly over proof-relevant histories. -/
theorem terminalMassAt_eq_sum_terminalHistories (n : ℕ) :
    c.terminalMassAt n = ((c.terminalHistories n).map (fun p => p.1.state.mass)).sum := by
  rw [terminalMassAt, ← terminalHistories_map_fst, List.map_map]
  rfl

variable [DecidableEq Store]

/-- Sum all terminal output operators with store `σ` at exactly depth `n`. -/
noncomputable def terminalOpAt (n : ℕ) (σ : Store) : Operator H :=
  (((c.frontier n).filter (fun d => d.control.isNone && decide (d.state.store = σ))).map
    (·.state.op)).sum

/-- Each exact-depth output at a given classical store is positive. -/
theorem isPositive_terminalOpAt (n : ℕ) (σ : Store) : (c.terminalOpAt n σ).IsPositive := by
  unfold terminalOpAt
  induction (c.frontier n).filter (fun d => d.control.isNone && decide (d.state.store = σ)) with
  | nil => exact LinearMap.isPositive_zero
  | cons d _ ih => exact d.state.positive.add ih

/-- Sum the outputs at a classical store over all depths strictly below the horizon. -/
noncomputable def terminalOpUpTo (N : ℕ) (σ : Store) : Operator H :=
  ∑ n ∈ Finset.range N, c.terminalOpAt n σ

/-- The accumulated quantum output at each classical store is positive. -/
theorem isPositive_terminalOpUpTo (N : ℕ) (σ : Store) : (c.terminalOpUpTo N σ).IsPositive :=
  LinearMap.isPositive_sum _ fun n _ => c.isPositive_terminalOpAt n σ

end QuantumProgram.Configuration
