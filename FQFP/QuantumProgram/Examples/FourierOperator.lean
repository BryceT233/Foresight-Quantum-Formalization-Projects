/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for identification of the counted circuit with the Fourier operator.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/Fourier.lean
Qhl/Examples/QFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierAmplitude

/-!
# The Fourier circuit as a linear operator

Unrolling the two counters gives a unitary program built from the gates of the counted
circuit. Agreement on the computational basis identifies its exact linear operator with
the normalized positive-exponent DFT, hence determines the output of every superposition.
-/

@[expose] public section

open CategoryTheory Qudit Complex

namespace QuantumProgram.FourierIteration

noncomputable section

variable (n : ℕ)

/-- The normalized DFT matrix in big-endian computational coordinates, with output row `y`. -/
def qftMatrix : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun y x => ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
    exp (2 * (Real.pi : ℂ) * binaryValue x * binaryValue y / 2 ^ n * I)

/-- The Fourier operator specified by its DFT kernel in the register's computational basis. -/
def qftOp : Operator (Memory n) :=
  let B := (registerBasis (ZBasis 2) n).toBasis
  (qftMatrix n).toLin B B

/-- On the empty register the single DFT coefficient is one. -/
theorem qftOp_zero : qftOp 0 = 1 := by
  have h : qftMatrix 0 = 1 := by
    ext y x
    simp [qftMatrix, binaryValue, Matrix.one_apply, Subsingleton.elim y x]
  rw [qftOp, h, Matrix.toLin_one]
  rfl

section

variable [NeZero n]

/-- The Hadamard of stage `k` followed by its controlled-phase ladder. -/
def stageProgram (k : ℕ) : UnitaryProgram (Memory n) :=
  (hadamardGate n k).seq (.gatePrefix (rungGate n k) (n - 1 - k))

/-- All Fourier stages followed by all mirror swaps, in the counted program's execution order. -/
def circuitProgram : UnitaryProgram (Memory n) :=
  (.gatePrefix (stageProgram n) n : UnitaryProgram (Memory n)).seq
    (.gatePrefix (mirrorGate n) (n / 2))

/-- The amplitude operator obtained by composing the actual circuit gates. -/
def qftCirOp : Operator (Memory n) := (circuitProgram n).toOperator

variable {n} (x : Fin n → Fin 2)

/-- A whole stage advances the stage vector by one, including the last empty ladder. -/
theorem stageProgram_apply (k : ℕ) (hk : k < n) :
    (stageProgram n k).toOperator (stageState x k).val = (stageState x (k + 1)).val := by
  change (UnitaryProgram.gatePrefix (rungGate n k) _).toOperator
    ((hadamardGate n k).toOperator (stageState x k).val) = _
  rw [hadamardGate_stageState x k hk, UnitaryProgram.toOperator_gatePrefix_apply _
    (n - 1 - k) (fun t => (ladderState x k t).val) (rungGate_ladderState x k),
    ladderState_full x k hk]

/-- The composite of all mirror gates reverses the factors of any product vector. -/
theorem mirrorPrefix_product (v : Fin n → UnitState Qubit) :
    (UnitaryProgram.gatePrefix (mirrorGate n) (n / 2)).toOperator (product v).val =
      (product (v ∘ Fin.rev)).val := by
  have hr := UnitaryProgram.toOperator_gatePrefix_apply (mirrorGate n) (n / 2)
    (fun k => (product (reversalFactors v k)).val) (fun _ => mirrorGate_product v)
  rw [reversalFactors_zero, reversalFactors_full] at hr
  exact hr

/-- The coherent circuit sends each basis ket to its Fourier vector with the specified phase. -/
theorem qftCirOp_basis : qftCirOp n (registerBasis (ZBasis 2) n x) = (fourierState x).val := by
  have hs := UnitaryProgram.toOperator_gatePrefix_apply (stageProgram n) n
    (fun k => (stageState x k).val) (stageProgram_apply x)
  rw [stageState_zero, stageState_full] at hs
  rw [registerBasis_apply]
  change (UnitaryProgram.gatePrefix (mirrorGate n) _).toOperator
    ((UnitaryProgram.gatePrefix (stageProgram n) n).toOperator _) = _
  rw [hs]
  exact mirrorPrefix_product _

/-- The mathematical DFT sends a computational basis vector to the same Fourier profile. -/
theorem qftOp_basis : qftOp n (registerBasis (ZBasis 2) n x) = (fourierState x).val := by
  let B := registerBasis (ZBasis 2) n
  change (qftMatrix n).toLin B.toBasis B.toBasis (B.toBasis x) = _
  rw [Matrix.toLin_self]
  convert B.sum_repr (fourierState x).val using 1
  apply Finset.sum_congr rfl
  intro y _
  rw [B.repr_apply_apply, fourierState_amplitude]
  rfl

variable (n)

/-- The operator of the verified gate sequence equals the normalized discrete Fourier transform. -/
theorem qftCirOp_eq_qftOp : qftCirOp n = qftOp n :=
  (registerBasis (ZBasis 2) n).toBasis.ext fun x => (qftCirOp_basis x).trans (qftOp_basis x).symm

/-- The circuit realizes the DFT on an arbitrary vector in the register. -/
theorem qftCirOp_apply_eq (ψ : (Memory n).state) : qftCirOp n ψ = qftOp n ψ :=
  LinearMap.congr_fun (qftCirOp_eq_qftOp n) ψ

/-- Each output amplitude is the DFT-weighted sum of all input amplitudes. -/
theorem qftCirOp_amplitude (ψ : (Memory n).state) (y : Fin n → Fin 2) :
    inner ℂ (registerBasis (ZBasis 2) n y) (qftCirOp n ψ) =
      ∑ x, qftMatrix n y x * inner ℂ (registerBasis (ZBasis 2) n x) ψ := by
  let B := registerBasis (ZBasis 2) n
  have h := congrFun (Matrix.repr_toLin B.toBasis B.toBasis (qftMatrix n) ψ) y
  rw [qftCirOp_eq_qftOp]
  simpa only [Matrix.mulVec, dotProduct, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, qftOp, B] using h

end

/-- The DFT as a qudit gate, acting on the whole register. -/
def qftGate : Memory n ⟶ Memory n := ofHom (qftOp n)

/-- The normalized DFT is unitary on the full tensor register. -/
instance : DaggerCategory.IsUnitary (qftGate n) := by
  unfold qftGate
  cases n with
  | zero =>
    rw [qftOp_zero]
    exact inferInstanceAs (DaggerCategory.IsUnitary (𝟙 (Memory 0)))
  | succ n =>
    rw [← qftCirOp_eq_qftOp]
    exact (circuitProgram (n + 1)).isUnitary_denoteHom

end

end QuantumProgram.FourierIteration
