/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for controlled unitaries and phase kickback.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Gate/Phase.lean
Qhl/Gate/ControlledU.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.CQM.Qudit.Measurement.Basic
public import FQFP.CQM.Qudit.State.Pure.Qubit

/-!
# Coherent control and phase kickback

The first factor is the control qubit. A target eigenvector deposits its eigenphase
on the control, including for powers of the target operator. For a phase gate on a
computational basis target this is one rung of the Fourier transform's phase ladder.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Complex
open scoped TensorProduct

namespace Qudit.Qubit

noncomputable section

variable {H : Qudit}

/-- The equatorial unit vector obtained by shifting the phase of the plus state. -/
def phaseState (φ : ℝ) : UnitState Qubit :=
  UnitState.map (phaseShift φ).asHom (UnitState.map Qubit.H.asHom (UnitState.ofBasis (ZBasis 2) 0))

/-- The two basis amplitudes of the phase state. -/
theorem phaseState_val (φ : ℝ) :
    (phaseState φ).val =
      ((√2)⁻¹ : ℂ) • (ZBasis 2 0 + exp (φ * I) • ZBasis 2 1) := by
  change (phaseShift φ).asHom.hom (Qubit.H.asHom.hom (ZBasis 2 0)) = _
  rw [hadamard_zero_apply, map_smul, map_add]
  simp [phaseShift_basis]

/-- Hadamard on a basis bit initializes the Fourier phase at zero or a half turn. -/
theorem hadamard_basis_phaseState (b : Fin 2) :
    UnitState.map Qubit.H.asHom (UnitState.ofBasis (ZBasis 2) b) =
      phaseState (if b = 0 then 0 else Real.pi) := by
  apply Subtype.ext
  rw [phaseState_val]
  change Qubit.H.asHom (ZBasis 2 b) = _
  fin_cases b
  · simp [hadamard_zero_apply]
  · rw [Qubit.H, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
    simp [smul_add]

/-- Successive phase shifts add their angles on the equator. -/
theorem phaseShift_phaseState (θ φ : ℝ) :
    (phaseShift θ).asHom (phaseState φ).val = (phaseState (φ + θ)).val := by
  rw [phaseState_val, phaseState_val]
  change (phaseShift θ).asHom.hom (_ • _) = _
  rw [map_smul, map_add, map_smul]
  simp [phaseShift_basis, add_mul, exp_add, smul_smul]

/-- On a target eigenvector the gate acts by its eigenphase on any control vector. -/
theorem controlledOp_tmul_eigen (T : Operator H) {w : H.state} {θ : ℝ}
    (hw : T w = exp (θ * I) • w) (u : Qubit.state) :
    controlledOp T (u ⊗ₜ[ℂ] w) = (phaseShift θ).asHom u ⊗ₜ[ℂ] w := by
  let insert := (TensorProduct.mk ℂ Qubit.state H.state).flip w
  have h : controlledOp T ∘ₗ insert = insert ∘ₗ (phaseShift θ).asHom.hom := by
    apply (ZBasis 2).toBasis.ext
    intro i
    change controlledOp T (ZBasis 2 i ⊗ₜ[ℂ] w) = (phaseShift θ).asHom (ZBasis 2 i) ⊗ₜ[ℂ] w
    rw [controlledOp_basis, phaseShift_basis]
    split <;> simp [hw, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  exact LinearMap.congr_fun h u

/-- The controlled `m`-th power adds `m * θ` to a phase state and fixes the target eigenvector. -/
theorem controlledOp_pow_phaseState (T : Operator H) {w : H.state} {θ : ℝ}
    (hw : T w = exp (θ * I) • w) (m : ℕ) (φ : ℝ) :
    controlledOp (T ^ m) ((phaseState φ).val ⊗ₜ[ℂ] w) =
      (phaseState (φ + m * θ)).val ⊗ₜ[ℂ] w := by
  have hp : (T ^ m) w = exp (((m : ℝ) * θ : ℝ) * I) • w := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, mul_apply_eq_comp, hw, map_smul, ih, smul_smul, ← exp_add]
      push_cast
      ring_nf
  rw [controlledOp_tmul_eigen _ hp, phaseShift_phaseState]

/-- A basis target of a controlled phase adds the angle exactly when its bit is one. -/
theorem controlledPhase_phaseState (θ φ : ℝ) (b : Fin 2) :
    (controlled (phaseShift θ).asHom) ((phaseState φ).val ⊗ₜ[ℂ] ZBasis 2 b) =
      (phaseState (φ + if b = 0 then 0 else θ)).val ⊗ₜ[ℂ] ZBasis 2 b := by
  have h : (phaseShift θ).asHom.hom (ZBasis 2 b) =
      exp (((if b = 0 then 0 else θ : ℝ) : ℂ) * I) • ZBasis 2 b := by
    by_cases hb : b = 0 <;> simpa [hb] using phaseShift_basis θ b
  exact (controlledOp_tmul_eigen _ h _).trans (congrArg (· ⊗ₜ[ℂ] ZBasis 2 b)
    (phaseShift_phaseState _ φ))

end

end Qudit.Qubit
