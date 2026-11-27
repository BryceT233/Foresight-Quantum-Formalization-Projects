/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.Execution.Seq

/-!
# Weights of entries into a while loop

Each entry is reached after a sequence of terminating body executions and a true guard test.
The weight can measure the entering trace or the cost of running the body from that state.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} (b : Store → Bool) (p : Command Store Cell H)

/-- Sum a weight over the histories entering the body for the `(n + 1)`st time.
The weight is evaluated on the subnormalized state carried by each such history. -/
noncomputable def whileEntryWeight (w : CQState Store H → ℝ≥0∞) : ℕ → CQState Store H → ℝ≥0∞
  | 0, s => if b s.store then w s else 0
  | n + 1, s => if b s.store then p.outputWeight (whileEntryWeight w n) s else 0

/-- Comparing weights on guarded inputs suffices to compare them at every entry depth. -/
theorem whileEntryWeight_mono {v w : CQState Store H → ℝ≥0∞}
    (h : ∀ t, b t.store = true → v t ≤ w t) (n : ℕ) :
    whileEntryWeight b p v n ≤ whileEntryWeight b p w n := by
  induction n with
  | zero =>
    intro s
    cases hb : b s.store <;> simp [whileEntryWeight, hb, h]
  | succ n ih =>
    intro s
    cases hb : b s.store <;> simp [whileEntryWeight, hb, p.outputWeight_mono ih s]

/-- Equal weights on guarded inputs give the same sum at every entry depth. -/
theorem whileEntryWeight_congr {v w : CQState Store H → ℝ≥0∞}
    (h : ∀ t, b t.store = true → v t = w t) (n : ℕ) :
    whileEntryWeight b p v n = whileEntryWeight b p w n :=
  le_antisymm (whileEntryWeight_mono b p (fun t ht => (h t ht).le) n)
    (whileEntryWeight_mono b p (fun t ht => (h t ht).ge) n)

/-- A constant factor in the weight factors out of the sum of entries. -/
theorem whileEntryWeight_const_mul (a : ℝ≥0∞) (w : CQState Store H → ℝ≥0∞)
    (n : ℕ) (s : CQState Store H) :
    whileEntryWeight b p (fun t => a * w t) n s = a * whileEntryWeight b p w n s := by
  induction n generalizing s with
  | zero => cases hb : b s.store <;> simp [whileEntryWeight, hb]
  | succ n ih =>
    cases hb : b s.store <;>
      simp [whileEntryWeight, hb, funext ih, p.outputWeight_const_mul]

/-- Counting one more body execution is equivalent to using the second-entry weight at the end. -/
theorem whileEntryWeight_succ_shift (w : CQState Store H → ℝ≥0∞) (n : ℕ) :
    whileEntryWeight b p w (n + 1) = whileEntryWeight b p (whileEntryWeight b p w 1) n := by
  induction n with
  | zero =>
    funext s
    cases hb : b s.store <;> simp [whileEntryWeight, hb]
  | succ n ih =>
    funext s
    rw [whileEntryWeight, whileEntryWeight, ih]

end QuantumProgram
