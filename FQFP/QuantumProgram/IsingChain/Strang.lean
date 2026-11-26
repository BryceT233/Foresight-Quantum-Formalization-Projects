/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.IsingChain.Evolution

/-!
# Fused Strang circuits for the open Ising chain

The choice of outer layer determines which half steps fuse between slices.
All counts refer to the native instruction list, including zero-angle rotations.
-/

@[expose] public section

open Qudit NormedSpace

namespace QuantumProgram.IsingChain

noncomputable section

variable {e : ℕ}

/-- The two commuting-term layers of the transverse-field Hamiltonian. -/
inductive Layer where
  /-- All single-site X fields. -/
  | field
  /-- All nearest-neighbor ZZ interactions. -/
  | interaction
  deriving DecidableEq

/-- The complementary layer in a two-layer splitting. -/
def Layer.other : Layer → Layer
  | .field => .interaction
  | .interaction => .field

/-- Native instructions for a layer of the specified duration. -/
def Layer.gates (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) : ℝ → List (Gate e) :=
  match L with
  | .field => fieldGates h
  | .interaction => interactionGates J

/-- The signed Hamiltonian of one layer. -/
def Layer.hamiltonian (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    Operator (tensorPower Qubit e) :=
  match L with
  | .field => fieldHamiltonian h
  | .interaction => interactionHamiltonian J

/-- Exact exponential evolution under a single layer. -/
def Layer.evolution (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (s : ℝ) :
    Operator (tensorPower Qubit e) :=
  exp (((-Complex.I) * (s : ℂ)) • L.hamiltonian h J)

/-- The gate interpretation realizes the exponential for either layer. -/
theorem Layer.toOperator_gates (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (s : ℝ) :
    (program (L.gates h J s)).toOperator = L.evolution h J s := by
  cases L
  · exact toOperator_fieldGates ..
  · exact toOperator_interactionGates ..

private theorem evolution_half_mul (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (s : ℝ) :
    L.evolution h J (s / 2) * L.evolution h J (s / 2) = L.evolution h J s := by
  let : NormedAlgebra ℚ (Operator (tensorPower Qubit e)) := .restrictScalars ℚ ℂ _
  unfold Layer.evolution
  rw [← exp_add_of_commute (Commute.refl _), ← add_smul]
  congr 2
  push_cast
  ring

/-- A symmetric step with the named layer in the two outer half steps. -/
def strangStep (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (s : ℝ) :
    Operator (tensorPower Qubit e) :=
  L.evolution h J (s / 2) * L.other.evolution h J s * L.evolution h J (s / 2)

/-- Emit two endpoint half layers, fusing every internal pair of half layers into one full layer. -/
def strangCircuit (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) (r : ℕ) :
    List (Gate e) :=
  match r with
  | 0 => []
  | k + 1 =>
    let s := t / (k + 1 : ℕ)
    let half := L.gates h J (s / 2)
    let inner := L.other.gates h J s
    half ++ (List.replicate k (inner ++ L.gates h J s)).flatten ++ inner ++ half

private theorem fused_pow {M : Type*} [Monoid M] (x y : M) (k : ℕ) :
    x * (y * ((x * x * y) ^ k * x)) = (x * y * x) ^ (k + 1) := by
  induction k with
  | zero => simp [mul_assoc]
  | succ k ih => rw [pow_succ _ (k + 1), ← ih, pow_succ _ k]; simp only [mul_assoc]

/-- For any signed time, the fused native circuit implements the power of the symmetric step. -/
theorem toOperator_strangCircuit (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ)
    (t : ℝ) (r : ℕ) :
    (program (strangCircuit L h J t r)).toOperator = strangStep L h J (t / r) ^ r := by
  cases r with
  | zero => simp [strangCircuit, program, UnitaryProgram.toOperator_sequence]
  | succ k =>
    simp only [strangCircuit, toOperator_append, toOperator_replicate, Layer.toOperator_gates,
      strangStep]
    rw [← evolution_half_mul L h J (t / (k + 1 : ℕ))]
    exact fused_pow ..

/-- CNOTs emitted by a positive number of fused steps on a chain with `e` edges. -/
theorem cnotCount_strangCircuit (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ)
    (t : ℝ) {r : ℕ} (hr : 0 < r) :
    cnotCount (strangCircuit L h J t r) =
      2 * e * (match L with | .field => r | .interaction => r + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  cases L <;> simp [strangCircuit, Layer.gates, Layer.other, cnotCount_append, cnotCount_replicate,
    cnotCount_fieldGates, cnotCount_interactionGates] <;> ring

/-- Count all native single-qubit rotations in the same list as the CNOTs. -/
def rotationCount (gs : List (Gate e)) : ℕ := gs.length - cnotCount gs

/-- On two qubits the two fused templates use respectively `3r+2` and `3r+1` rotations. -/
theorem rotationCount_strangCircuit_pair (L : Layer) (a b J t : ℝ) {r : ℕ} (hr : 0 < r) :
    rotationCount (strangCircuit L ![a, b] ![J] t r) =
      3 * r + (match L with | .field => 2 | .interaction => 1) := by
  unfold rotationCount
  rw [cnotCount_strangCircuit _ _ _ _ hr]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  cases L <;>
    simp [strangCircuit, Layer.gates, Layer.other, fieldGates, interactionGates, List.ofFn_succ,
      edgeGates, List.length_flatten, List.sum_replicate] <;> lia

end

end QuantumProgram.IsingChain
