/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the Fourier circuit and operator on the uniform state.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Examples/QFTUniform.lean
Qhl/Register/FourierUniform.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierOperator

/-!
# The counted Fourier circuit on the uniform superposition

At stage entry precisely the completed prefix has been changed from plus to zero.
The Hadamard extends this prefix by one and its zero control disables the entire
phase ladder. The final mirror swaps preserve the all-zero state.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit

namespace QuantumProgram.FourierIteration

noncomputable section

local notation "zeroBit" => UnitState.ofBasis (ZBasis 2) 0
local notation "plusBit" => UnitState.map Qubit.H.asHom zeroBit

/-- The all-zero computational basis state of the register. -/
def zeroState (n : ℕ) : UnitState (Memory n) := product fun _ => zeroBit

/-- The equal-amplitude superposition of all computational basis words. -/
def uniformState (n : ℕ) : UnitState (Memory n) := product fun _ => plusBit

/-- The local factors after `k` stages on a uniform input. -/
def zeroPrefix (n k : ℕ) (i : Fin n) : UnitState Qubit :=
  if i.val < k then zeroBit else plusBit

/-- At entry to the stage loop every factor is plus. -/
theorem zeroPrefix_zero (n : ℕ) : zeroPrefix n 0 = fun _ => plusBit := by
  funext i
  simp [zeroPrefix]

/-- At exit from the stage loop every factor is zero. -/
theorem zeroPrefix_full (n : ℕ) : zeroPrefix n n = fun _ => zeroBit := by
  funext i
  simp [zeroPrefix]

private theorem hadamard_plus : UnitState.map Qubit.H.asHom plusBit = zeroBit := by
  apply Subtype.ext
  have hh := hom_adjoint_apply_of_isIsometry Qubit.H.asHom (zeroBit).val
  have hs : Qubit.H.asHom.hom.adjoint = Qubit.H.asHom.hom :=
    (isSelfAdjoint_hom Qubit.isSelfAdjoint_H).star_eq
  rw [hs] at hh
  exact hh

/-- Every basis word has the same positive real amplitude on the uniform input. -/
theorem uniformState_amplitude {n : ℕ} (x : Fin n → Fin 2) :
    inner ℂ (registerBasis (ZBasis 2) n x) (uniformState n).val = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  rw [uniformState, product, inner_registerBasis_productState]
  change (∏ i, inner ℂ (ZBasis 2 (x i)) hadamardZero) = _
  simp [inner_ZBasis_hadamardZero]

/-- The normalized DFT matrix is symmetric in the input and output words. -/
theorem qftMatrix_transpose (n : ℕ) : (qftMatrix n).transpose = qftMatrix n := by
  ext y x
  simp only [Matrix.transpose_apply, qftMatrix, mul_right_comm _ (binaryValue y : ℂ)
    (binaryValue x : ℂ)]

private theorem toLin_zeroState_of_uniform_column {n : ℕ}
    (M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (h : ∀ y, M y (fun _ => 0) = ((Real.sqrt 2 : ℂ)⁻¹) ^ n) :
    let B := (registerBasis (ZBasis 2) n).toBasis
    M.toLin B B (zeroState n).val = (uniformState n).val := by
  let B := registerBasis (ZBasis 2) n
  have hz : B.toBasis (fun _ => 0) = (zeroState n).val := registerBasis_apply _ _
  change M.toLin B.toBasis B.toBasis (zeroState n).val = _
  rw [← hz, Matrix.toLin_self]
  convert B.sum_repr (uniformState n).val using 1
  apply Finset.sum_congr rfl
  intro y _
  rw [B.repr_apply_apply, uniformState_amplitude, h]
  rfl

/-- The zero column of the mathematical DFT is the uniform superposition. -/
theorem qftOp_zeroState (n : ℕ) : qftOp n (zeroState n).val = (uniformState n).val :=
  toLin_zeroState_of_uniform_column _ (fun _ => by simp [qftMatrix, binaryValue])

/-- The mathematical DFT sends the uniform superposition to the all-zero ket at every width. -/
theorem qftOp_uniformState (n : ℕ) : qftOp n (uniformState n).val = (zeroState n).val := by
  let B := registerBasis (ZBasis 2) n
  have back : (qftOp n).adjoint (zeroState n).val = (uniformState n).val := by
    change ((qftMatrix n).toLin B.toBasis B.toBasis).adjoint _ = _
    rw [← Matrix.toLin_conjTranspose B B]
    exact toLin_zeroState_of_uniform_column _ (fun _ => by simp [qftMatrix, binaryValue])
  rw [← back]
  exact LinearMap.congr_fun (congrArg Qudit.Hom.hom (IsUnitary.dagger_comp_eq_id (qftGate n))) _

variable {n : ℕ} [NeZero n]

/-- On an all-zero input word the suffix-phase profile is the uniform product state. -/
theorem fourierState_zero : fourierState (fun _ : Fin n => 0) = uniformState n := by
  apply Subtype.ext
  rw [← qftOp_basis, registerBasis_apply]
  exact qftOp_zeroState n

private theorem hadamard_zeroPrefix (k : ℕ) (hk : k < n) :
    (hadamardGate n k).toOperator (product (zeroPrefix n k)).val =
      (product (zeroPrefix n (k + 1))).val := by
  change ((Register.site (fun _ => Qubit) (control n k)).liftEnd Qubit.H).asHom _ = _
  rw [Register.liftEnd_site_productState]
  apply congrArg (fun w => (product w).val)
  have hc : (control n k).val = k := Nat.mod_eq_of_lt hk
  funext i
  by_cases hi : i = control n k
  · subst i
    simp [zeroPrefix, hc, hadamard_plus]
  · have hne : i.val ≠ k := fun h => hi (Fin.ext (h.trans hc.symm))
    simp only [Function.update_of_ne hi, zeroPrefix, show i.val < k + 1 ↔ i.val < k by lia]

/-- With its control already zero, the counted ladder preserves the whole prefix state. -/
theorem sourceDeriv_ladder_uniform (P : Store → Prop) (hP : ∀ σ t, P (rungCounter.set σ t) ↔ P σ) :
    let A := fun σ : Store => Assertion.pure (product (zeroPrefix n (σ.1 + 1))) σ
    SourceDerivTot (.ofEffect A P) (ladder n) (.ofEffect A P) := by
  let v := fun k => product (zeroPrefix n (k + 1))
  have d := count_rungs P hP (fun k _ => Assertion.pure (v k) ()) (by
    apply SourceDerivTot.unitary_pure (Store := Store) (k := 2) _ _
      (fun σ => v σ.1) (fun σ => v σ.1) (fun _ h => rung_injective h.2)
    intro σ h
    have ht := h.2
    have hc : (control n σ.1).val = σ.1 := Nat.mod_eq_of_lt (by lia)
    exact FourierLadder.phaseGate_productState_of_control_zero _ _ (control_lt_target ht) _ _
      (by simp [zeroPrefix, hc]))
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ h => ⟨h.1, le_rfl⟩)

/-- The counted stages send plus to zero on every wire and exit at the register width. -/
theorem sourceDeriv_iteration_uniform :
    SourceDerivTot (.ofEffect (Assertion.pure (uniformState n)) fun _ => True) (iteration n)
      (.ofEffect (Assertion.pure (zeroState n)) fun σ => σ.1 = n) := by
  let v := fun k => product (zeroPrefix n k)
  have step : SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ.1) σ) fun σ => σ.1 < n)
      ((hadamard n).seq (ladder n))
      (.ofEffect (fun σ => Assertion.pure (v (σ.1 + 1)) σ) fun σ => σ.1 < n) := by
    apply SourceDerivTot.seq _ (sourceDeriv_ladder_uniform (fun σ => σ.1 < n) (fun _ _ => Iff.rfl))
    exact SourceDerivTot.unitary_pure (Store := Store) _ _ (fun σ => v σ.1)
      (fun σ => v (σ.1 + 1)) (fun _ _ => Function.injective_of_subsingleton _)
      (fun σ h => hadamard_zeroPrefix σ.1 h)
  simpa only [v, zeroPrefix_zero, zeroPrefix_full, uniformState, zeroState] using
    sourceDeriv_iteration_of_stage v step

/-- Source derivation of the uniform-to-zero triple by composing the two counted loops. -/
theorem sourceDeriv_circuit_uniform :
    SourceDerivTot (.ofEffect (Assertion.pure (uniformState n)) fun _ => True) (circuit n)
      (.ofEffect (Assertion.pure (zeroState n)) fun _ => True) := by
  apply SourceDerivTot.seq sourceDeriv_iteration_uniform
  refine .conseq ?_ (sourceDeriv_reversal (fun _ : Fin n => zeroBit)) ?_
  · exact fun _ _ => ⟨trivial, le_rfl⟩
  · exact fun _ _ => ⟨trivial, le_rfl⟩

/-- The uniform-to-zero total correctness triple in the ordinary proof system. -/
theorem derivTot_circuit_uniform :
    DerivTot (Assertion.pure (uniformState n)) (circuit n) (Assertion.pure (zeroState n)) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using
    (sourceDeriv_circuit_uniform (n := n)).toDerivTot

/-- Total correctness of the original Fourier circuit on the uniform input, in every store. -/
theorem validTot_circuit_uniform :
    validTot (Assertion.pure (uniformState n)) (circuit n) (Assertion.pure (zeroState n)) :=
  (derivTot_circuit_uniform (n := n)).sound

end

end QuantumProgram.FourierIteration
