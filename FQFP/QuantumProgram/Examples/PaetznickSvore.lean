/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.HeraldedBlock
public import FQFP.QuantumProgram.Examples.BellPreparation

/-!
# The Paetznick–Svore two-T heralded gate

Figure 8 of Paetznick and Svore applies H, T, CNOT, H, CNOT, T, H with the ancilla
as control. Measuring zero implements the target gate, while measuring one preserves
the data. The amplitudes include the phases of both branches.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory Qudit Complex
open scoped TensorProduct ComplexConjugate

namespace QuantumProgram.PaetznickSvore

open RepeatUntilSuccess

noncomputable section

/-- The phase of the T gate. -/
abbrev phase : ℂ := exp (((Real.pi / 4 : ℝ) : ℂ) * I)

/-- The ancilla T gate. -/
def tGate : Qubit ⟶ Qubit := (Qubit.phaseShift (Real.pi / 4)).asHom

instance : IsUnitary tGate := by
  rw [tGate, Qubit.phaseShift, isUnitary_matrixToEnd_iff_fin_two]
  simp [-Complex.ofReal_div, norm_exp_ofReal_mul_I]

/-- The seven gates of the repeated circuit, in execution order. -/
def circuit : UnitaryProgram Memory :=
  let h := UnitaryProgram.gateHom (.left .whole) Qubit.H.asHom
  let t := UnitaryProgram.gateHom (.left .whole) tGate
  let cx := UnitaryProgram.gateHom .whole controlledNot
  .sequence [h, t, cx, h, cx, t, h]

/-- The successful data transformation is `(1 + i√2 X)/√3`. -/
def target : Qubit ⟶ Qubit :=
  (matrixToEnd (((Real.sqrt 3 : ℂ)⁻¹) •
    !![1, I * (Real.sqrt 2 : ℂ); I * (Real.sqrt 2 : ℂ), 1])).asHom

instance : IsUnitary target := by
  rw [target, isUnitary_matrixToEnd_iff_fin_two]
  norm_num [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, ← mul_assoc, map_mul]
  ring

/-- Success amplitude of the block on the reset ancilla. -/
def successAmplitude : ℂ := (Real.sqrt 3 : ℂ) / 2 * conj phase

/-- Retry amplitude of the block on the reset ancilla. -/
def retryAmplitude : ℂ := phase / 2

/-- One attempt succeeds with probability three quarters. -/
theorem successProb : ‖successAmplitude‖ ^ 2 = 3 / 4 := by
  norm_num [successAmplitude, norm_mul, norm_div, mul_pow, div_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_exp_ofReal_mul_I]

/-- One attempt leaves the input data intact with probability one quarter. -/
theorem failProb : ‖retryAmplitude‖ ^ 2 = 1 / 4 := by
  rw [retryAmplitude, norm_div, norm_exp_ofReal_mul_I]
  norm_num [retryAmplitude, norm_div, phase]

private theorem phase_eq : phase = bellFactor * (1 + I) := by
  rw [phase, exp_ofReal_mul_I, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast
  rw [bellFactor, Complex.ofReal_inv]
  field_simp
  have h : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by norm_cast; norm_num
  linear_combination (1 + I) * h

private theorem h_basis (j : Fin 2) :
    Qubit.H.asHom (ZBasis 2 j) = bellFactor •
      (ZBasis 2 0 + (if j = 0 then 1 else -1 : ℂ) • ZBasis 2 1) := by
  rw [Qubit.H, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  fin_cases j <;> simp [bellFactor, smul_add]

private theorem t_basis (j : Fin 2) :
    tGate (ZBasis 2 j) = (if j = 0 then 1 else phase : ℂ) • ZBasis 2 j := by
  rw [tGate, Qubit.phaseShift, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  fin_cases j <;> simp [phase]

private theorem target_basis (j : Fin 2) :
    target (ZBasis 2 j) = (Real.sqrt 3 : ℂ)⁻¹ •
      (ZBasis 2 j + (I * (Real.sqrt 2 : ℂ)) • ZBasis 2 (1 + j)) := by
  rw [target, matrixToEnd_apply_basis (n := 2), Fin.sum_univ_two]
  fin_cases j <;> simp [smul_add, smul_smul, add_comm]

/-- Measuring the reset ancilla selects the target on zero and the identity on one. -/
theorem decomp (x : Qubit.state) :
    circuit.denoteHom ((RepeatUntilSuccess.insert 0).hom x) =
      successAmplitude • (ZBasis 2 0 ⊗ₜ[ℂ] target.hom x) +
        retryAmplitude • (ZBasis 2 1 ⊗ₜ[ℂ] x) := by
  suffices hm : circuit.denoteHom.hom ∘ₗ (RepeatUntilSuccess.insert 0).hom =
      successAmplitude • (outputMap target 0).hom +
        retryAmplitude • (RepeatUntilSuccess.insert 1).hom from
    LinearMap.congr_fun hm x
  apply (ZBasis 2).toBasis.ext
  intro j
  simp only [circuit, UnitaryProgram.sequence, UnitaryProgram.denoteHom, Register.liftHom,
    hom_comp, LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
  have ins (i : Fin 2) (v : Qubit.state) :
      (RepeatUntilSuccess.insert i).hom v = ZBasis 2 i ⊗ₜ[ℂ] v := rfl
  have out (v : Qubit.state) :
      (outputMap target 0).hom v = ZBasis 2 0 ⊗ₜ[ℂ] target.hom v := rfl
  simp only [LinearMap.add_apply, LinearMap.smul_apply, ins, out]
  have flip : (1 : Fin 2) + (1 + j) = j := by rw [← add_assoc]; exact zero_add j
  simp only [whiskerRight_apply, h_basis, t_basis, target_basis, controlledNot_basis,
    TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, map_smul, map_add, zero_add, flip, show (1 : Fin 2) ≠ 0 by decide,
    ↓reduceIte, one_smul]
  simp only [successAmplitude, retryAmplitude, phase_eq, map_mul, conj_bellFactor, map_add,
    map_one, conj_I]
  have hs : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by norm_cast; positivity)
  have ht : bellFactor * (Real.sqrt 2 : ℂ) = 1 := by
    rw [bellFactor, Complex.ofReal_inv, inv_mul_cancel₀ (by norm_cast; positivity)]
  have hh := bellFactor_mul_self
  have hi := I_sq
  match_scalars <;> grind only

/-- The seven-gate circuit satisfies the coherent heralded-block specification. -/
theorem heraldedBlock : HeraldedBlock circuit target successAmplitude retryAmplitude := ⟨decomp⟩

/-- The Born weight of each measured ancilla outcome. -/
def weight (i : Fin 2) : ℝ := if i = 0 then 3 / 4 else 1 / 4

/-- Each measured branch of the actual circuit on an arbitrary input operator. -/
theorem branch_after_reset (i : Fin 2) (A : Operator Memory) :
    measurement.branch i (circuit.toChannel.toSuperoperator (reset.toSuperoperator A)) =
      (weight i : ℂ) • Superoperator.conjugate (outputMap target i).hom
        (Operator.partialTraceLeft A) := by
  simpa only [weight, successProb, failProb] using heraldedBlock.branch_after_reset i A

end

end QuantumProgram.PaetznickSvore
