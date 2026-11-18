/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.TensorPower
public import FQFP.QuantumProgram.TransverseFieldIsing

/-!
# Physical gates of the open transverse-field Ising chain

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

/-- One native rotation or a nearest-neighbor CNOT directed from left to right. -/
inductive Gate (e : ℕ) where
  /-- Rotate a site about the X axis. -/
  | rx (site : Fin (e + 1)) (angle : ℝ)
  /-- Rotate a site about the Z axis. -/
  | rz (site : Fin (e + 1)) (angle : ℝ)
  /-- Add the left endpoint bit to the right endpoint modulo two. -/
  | cnot (edge : Fin e)

/-- Interpret an instruction using the single-site and adjacent-pair operator embeddings. -/
def Gate.program : Gate e → UnitaryProgram (tensorPower Qubit e)
  | .rx i θ => .liftGate (siteOp Qubit e i) (QuantumProgram.rx θ)
  | .rz i θ => .liftGate (siteOp Qubit e i) (QuantumProgram.rz θ)
  | .cnot j => .liftGate (adjacentOp Qubit e j) controlledNot

/-- Emit the compute-rotate-uncompute implementation of an edge rotation. -/
def edgeGates (j : Fin e) (θ : ℝ) : List (Gate e) :=
  [.cnot j, .rz j.succ θ, .cnot j]

/-- All transverse-field rotations in site order. -/
def fieldGates (h : Fin (e + 1) → ℝ) (δ : ℝ) : List (Gate e) :=
  List.ofFn (fun i => .rx i (2 * h i * δ))

/-- All parity rotations in edge order. -/
def interactionGates (J : Fin e → ℝ) (δ : ℝ) : List (Gate e) :=
  (List.ofFn (fun j => edgeGates j (2 * J j * δ))).flatten

/-- One Lie–Trotter slice, with signed coefficients and the physical half-angle convention. -/
def slice (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (δ : ℝ) : List (Gate e) :=
  fieldGates h δ ++ interactionGates J δ

/-- The physical instructions for `r` equal steps over time `t`. -/
def circuit (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) : List (Gate e) :=
  (List.replicate r (slice h J (t / r))).flatten

/-- Execute a physical instruction list in order. -/
def program (gs : List (Gate e)) : UnitaryProgram (tensorPower Qubit e) :=
  .sequence (gs.map Gate.program)

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

/-- Two sites and one edge give the existing five-gate Ising slice. -/
theorem toOperator_slice_pair (a b J δ : ℝ) :
    (program (slice ![a, b] ![J] δ)).toOperator =
      (TransverseFieldIsing.step a b J δ).toOperator := by
  simp only [slice, fieldGates, interactionGates, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil,
    List.append_nil, List.cons_append, List.nil_append, edgeGates, program,
    TransverseFieldIsing.step, List.map_cons, List.map_nil, UnitaryProgram.toOperator_sequence]
  rfl

end IsingChain

end

end QuantumProgram
