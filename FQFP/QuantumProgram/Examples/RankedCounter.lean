/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/SourceRuleIntegration.lean (countLoopDeriv and countLoopValid)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Iteration.LoopGhost

/-!
# Incrementing to a bound with a read-only rank witness

The integer ghost records the difference between the bound and the counter before each increment.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.RankedCounter

variable {Cell : Type*} {H : Qudit}

/-- Increment the counter while it is below the bound. -/
def loop (N : ℕ) : Command ℕ Cell H := .whileDo (fun k => decide (k < N)) (.assign Nat.succ)

/-- From any counter at most `N`, the ghost rank rule derives exit exactly at `N`. -/
theorem sourceDeriv_loop (N : ℕ) :
    SourceDerivTot (.ofEffect Assertion.identity (· ≤ N)) (loop (Cell := Cell) (H := H) N)
      (.ofEffect Assertion.identity (· = N)) := by
  let t := fun k : ℕ => (N : ℤ) - k
  let b := fun k : ℕ => decide (k < N)
  let p : Command ℕ Cell H := .assign Nat.succ
  have inv : SourceDerivTot (.ofEffect Assertion.identity fun k => k ≤ N ∧ b k = true)
      p (.ofEffect Assertion.identity (· ≤ N)) := by
    apply SourceDerivTot.conseq _ (.assign Nat.succ Assertion.identity (· ≤ N))
      (fun _ h => ⟨h, le_rfl⟩)
    exact fun _ h => ⟨Nat.succ_le_of_lt (of_decide_eq_true h.2), le_rfl⟩
  have rank : SourceDerivTot (rankGhostPre (· ≤ N) b t) (p.mapStore StoreLens.fst)
      (rankGhostPost t) := by
    let f := fun v : ℕ × ℤ => (v.1 + 1, v.2)
    apply SourceDerivTot.conseq _ (.assign f Assertion.identity (fun v => t v.1 < v.2))
      (fun _ h => ⟨h, le_rfl⟩)
    intro v hv
    have he : (N : ℤ) - v.1 = v.2 := hv.2.2
    exact ⟨show (N : ℤ) - (v.1 + 1 : ℕ) < v.2 by lia, le_rfl⟩
  have d := SourceDerivTot.whileLoopGhost (A := SourceEffect.total Assertion.identity) t
    (fun k (hk : k ≤ N) => show 0 ≤ (N : ℤ) - k by lia)
    (by simpa only [SourceEffect.total_under] using inv) rank
  rw [SourceEffect.total_under, SourceEffect.total_under] at d
  apply SourceDerivTot.conseq (fun _ h => ⟨h, le_rfl⟩) d
  exact fun k h => ⟨Nat.le_antisymm h.1 (Nat.le_of_not_gt (of_decide_eq_false h.2)), le_rfl⟩

/-- All input mass starting below or at the bound terminates with the counter equal to it. -/
theorem validTot_loop (N : ℕ) :
    validTot (Assertion.identity.mask (· ≤ N)) (loop (Cell := Cell) (H := H) N)
      (Assertion.identity.mask (· = N)) :=
  (sourceDeriv_loop N).sound

end QuantumProgram.RankedCounter
