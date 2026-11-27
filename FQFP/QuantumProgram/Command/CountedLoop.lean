/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the counter lens and the reset, guard and increment of a counted loop.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/CountedWhile.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.Basic

/-!
# Exact execution of a counted loop

`Qhl/Logic/CountedWhile.lean` resets a classical counter, tests it against a bound read
from the store, and increments it after executing the body. For a body that terminates in
one transition with a unique successor, an iteration takes exactly three small steps.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- A natural-valued classical coordinate with read-after-write. -/
structure CounterLens (Store : Type*) where
  /-- Read the counter. -/
  get : Store → ℕ
  /-- Write the counter. -/
  set : Store → ℕ → Store
  /-- Reading the assigned counter yields the assigned value. -/
  get_set (σ : Store) (k : ℕ) : get (set σ k) = k

/-- Use the whole classical store as the counter. -/
def CounterLens.nat : CounterLens ℕ := ⟨id, fun _ k => k, fun _ _ => rfl⟩

variable {Store Cell : Type*} {H : Qudit}

/-- Reset the counter to zero and iterate the body, incrementing after each execution. -/
def Command.counted (c : CounterLens Store) (bound : Store → ℕ) (body : Command Store Cell H) :
    Command Store Cell H :=
  (.assign (fun σ => c.set σ 0) : Command Store Cell H).seq
    (.whileDo (fun σ => decide (c.get σ < bound σ))
      (body.seq (.assign fun σ => c.set σ (c.get σ + 1))))

/-- A single-successor body realizes its indicated state sequence and exits at its bound.
The depth includes the initial assignment and the final false guard test. -/
theorem Command.frontier_counted (c : CounterLens Store) (bound : Store → ℕ)
    (body : Command Store Cell H) (input : CQState Store H) (N : ℕ)
    (s : (k : ℕ) → k ≤ N → CQState Store H)
    (hinit : { input with store := c.set input.store 0 } = s 0 (Nat.zero_le N))
    (hget : ∀ k hk, c.get (s k hk).store = k)
    (hbound : ∀ k hk, bound (s k hk).store = N)
    (hbody : ∀ k (hk : k < N), ∃ t, body.step (s k hk.le) = [⟨none, t⟩] ∧
      { t with store := c.set t.store (c.get t.store + 1) } = s (k + 1) hk) :
    (Configuration.mk (some (counted c bound body)) input).frontier (3 * N + 2) =
      [⟨none, s N le_rfl⟩] := by
  let guard := fun σ => decide (c.get σ < bound σ)
  let inc := fun σ => c.set σ (c.get σ + 1)
  let loop := Command.whileDo guard (body.seq (.assign inc))
  let root := Configuration.mk (some (counted c bound body)) input
  have prefixRun (k : ℕ) (hk : k ≤ N) :
      root.frontier (3 * k + 1) = [⟨some loop, s k hk⟩] := by
    induction k with
    | zero =>
      change [Configuration.mk (some loop) { input with store := c.set input.store 0 }] = _
      rw [hinit]
    | succ k ih =>
      obtain ⟨t, ht, hinc⟩ := hbody k hk
      rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by lia,
        Configuration.frontier_add_of_singleton (ih (by lia))]
      have hg : guard (s k (by lia)).store = true := by
        simp [guard, hget, hbound, show k < N from hk]
      simp [Configuration.frontier, Configuration.next, loop, Command.step, hg,
        Configuration.seqWith, ht, inc, hinc]
  rw [show 3 * N + 2 = (3 * N + 1) + 1 by lia,
    Configuration.frontier_add_of_singleton (prefixRun N le_rfl)]
  simp [Configuration.frontier, Configuration.next, loop, Command.step, guard, hget, hbound]

end QuantumProgram
