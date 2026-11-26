/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.IsingChain.Instruction

/-!
# Native gate counts for the open transverse-field Ising chain

With `e` edges the register has `e + 1` sites. Each slice executes the transverse fields
in site order and then the Ising couplings in edge order. Its instruction list supplies
both the unitary program and the resource count.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Qudit

namespace QuantumProgram

noncomputable section

namespace IsingChain

variable {e : ℕ}

/-- Count native CNOT instructions, including both parity gates on every edge. -/
def cnotCount (gs : List (Gate e)) : ℕ := gs.countP fun g => match g with
  | .cnot _ => true
  | _ => false

/-- Counts add when two instruction lists are concatenated. -/
theorem cnotCount_append (xs ys : List (Gate e)) :
    cnotCount (xs ++ ys) = cnotCount xs + cnotCount ys := List.countP_append

private theorem count_flatten (gs : List (List (Gate e))) :
    cnotCount gs.flatten = (gs.map cnotCount).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simpa [cnotCount, List.countP_append] using congrArg (cnotCount g + ·) ih

/-- A transverse-field layer emits no CNOTs. -/
theorem cnotCount_fieldGates (h : Fin (e + 1) → ℝ) (δ : ℝ) :
    cnotCount (fieldGates h δ) = 0 := by simp [fieldGates, cnotCount]

/-- Every edge contributes a compute and an uncompute CNOT. -/
theorem cnotCount_interactionGates (J : Fin e → ℝ) (δ : ℝ) :
    cnotCount (interactionGates J δ) = 2 * e := by
  unfold interactionGates
  rw [count_flatten, List.map_ofFn, List.sum_ofFn]
  simp [cnotCount, edgeGates, Nat.mul_comm]

/-- Repeating a physical gate list multiplies its CNOT count by the repetition count. -/
theorem cnotCount_replicate (n : ℕ) (gs : List (Gate e)) :
    cnotCount (List.replicate n gs).flatten = n * cnotCount gs := by
  simp [count_flatten, List.sum_replicate]

/-- The native circuit on `e + 1` sites emits exactly `2 * r * e` CNOTs. -/
theorem cnotCount_circuit (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) :
    cnotCount (circuit h J t r) = 2 * r * e := by
  simp [circuit, slice, cnotCount_replicate, cnotCount_append, cnotCount_fieldGates,
    cnotCount_interactionGates, Nat.mul_left_comm, Nat.mul_assoc]

end IsingChain

end

end QuantumProgram
