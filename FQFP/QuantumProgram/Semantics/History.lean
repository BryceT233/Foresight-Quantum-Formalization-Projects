/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for occurrence-indexed histories and frontiers.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/Occurrence.lean
Qhl/History/Frontier.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.ControlFlow
import Mathlib.Data.List.FinRange

/-!
# Occurrence-indexed execution histories

The branch index distinguishes two measurement outcomes even when both have the same
successor configuration. Forgetting the path recovers the ordered small-step frontier,
as in `Qhl/History/Occurrence.lean` and `Qhl/History/Frontier.lean`.
-/

@[expose] public section

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- A path of a specified length from a root, recording the chosen occurrence at every step. -/
inductive History (root : Configuration Store Cell H) : ℕ → Configuration Store Cell H → Type _
  /-- The empty history ends at its root. -/
  | nil : History root 0 root
  /-- Extend a history with one of the successor occurrences. -/
  | step {n c} (path : History root n c) (i : Fin c.next.length) :
      History root (n + 1) c.next[i.val]

/-- The visited configurations, from the root through the endpoint. -/
noncomputable def History.trace {root : Configuration Store Cell H} :
    {n : ℕ} → {c : Configuration Store Cell H} →
      History root n c → List (Configuration Store Cell H)
  | _, _, .nil => [root]
  | _, _, .step (c := c) path i => path.trace ++ [c.next[i.val]]

/-- A history with `n` transitions visits `n + 1` configurations. -/
theorem History.length_trace {root c : Configuration Store Cell H} {n : ℕ}
    (path : History root n c) : path.trace.length = n + 1 := by
  induction path <;> simp [trace, *]

/-- All histories of a given length, paired with their endpoints in execution order. -/
noncomputable def Configuration.historyFrontier (root : Configuration Store Cell H) :
    (n : ℕ) → List (Σ c, History root n c)
  | 0 => [⟨root, .nil⟩]
  | n + 1 => (root.historyFrontier n).flatMap fun ⟨c, path⟩ =>
      (List.finRange c.next.length).map fun i => ⟨_, path.step i⟩

/-- Forgetting each history gives the plain frontier with all occurrences in order. -/
theorem Configuration.historyFrontier_map_fst (root : Configuration Store Cell H) (n : ℕ) :
    (root.historyFrontier n).map Sigma.fst = root.frontier n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [historyFrontier, frontier, ← ih, List.map_flatMap, List.flatMap_map]
    apply List.flatMap_congr
    rintro ⟨c, path⟩ _
    exact (List.map_map ..).trans (List.map_get_finRange c.next)

/-- The histories that terminate at exactly this depth. -/
noncomputable def Configuration.terminalHistories (root : Configuration Store Cell H) (n : ℕ) :
    List (Σ c, History root n c) := (root.historyFrontier n).filter (·.1.control.isNone)

/-- The endpoints of terminal histories are the terminal part of the exact-depth frontier. -/
theorem Configuration.terminalHistories_map_fst (root : Configuration Store Cell H) (n : ℕ) :
    (root.terminalHistories n).map Sigma.fst = (root.frontier n).filter (·.control.isNone) := by
  rw [terminalHistories, ← historyFrontier_map_fst, List.filter_map]
  rfl

end QuantumProgram
