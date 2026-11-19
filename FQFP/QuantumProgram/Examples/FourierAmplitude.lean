/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for Fourier state amplitudes and the basis-input circuit triple.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Register/Fourier.lean
Qhl/Examples/QFTTriple.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.FourierCircuit

/-!
# Computational basis amplitudes of the Fourier circuit

The output factors of the counted Fourier circuit give the normalized, positive-exponent
discrete Fourier transform in big-endian order. The integer prefix discarded by each
suffix angle contributes only whole turns to its phase.
-/

@[expose] public section

open Qudit Complex

namespace QuantumProgram.FourierIteration

noncomputable section

/-- Big-endian integer represented by a computational basis word. -/
def binaryValue {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  ∑ i, (x i).val * 2 ^ (n - 1 - i.val)

private def prefixValue (f : ℕ → Fin 2) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 * prefixValue f m + (f m).val

private theorem prefixValue_eq (f : ℕ → Fin 2) (m : ℕ) :
    prefixValue f m = binaryValue (fun i : Fin m => f i.val) := by
  induction m with
  | zero => simp [prefixValue, binaryValue]
  | succ m ih =>
    rw [prefixValue, ih, binaryValue, binaryValue, Fin.sum_univ_castSucc, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_castSucc, Nat.add_sub_cancel]
      rw [show m - i.val = (m - 1 - i.val) + 1 by have := i.isLt; lia, pow_succ]
      ring
    · simp

private theorem prefixValue_add (f : ℕ → Fin 2) (k m : ℕ) :
    prefixValue f (k + m) = prefixValue f k * 2 ^ m + prefixValue (fun t => f (k + t)) m := by
  induction m with
  | zero => simp [prefixValue]
  | succ m ih => rw [Nat.add_succ, prefixValue, ih, prefixValue, pow_succ]; ring

private theorem basisAngle_prefix (f : ℕ → Fin 2) (m : ℕ) :
    FourierLadder.basisAngle (fun i : Fin m => f i.val) =
      2 * Real.pi * prefixValue f m / 2 ^ m := by
  unfold FourierLadder.basisAngle
  rw [Fin.sum_univ_eq_sum_range (fun j => if f j = 0 then 0 else 2 * Real.pi / 2 ^ (j + 1))]
  induction m with
  | zero => simp [prefixValue]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, prefixValue, pow_succ]
    generalize f m = b
    fin_cases b <;> simp <;> ring

variable {n : ℕ} [NeZero n] (x : Fin n → Fin 2)

private theorem exp_suffixAngle (i : Fin n) :
    exp ((suffixAngle x i : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * binaryValue x / 2 ^ (n - i.val) * I) := by
  let f := fun t => x (Fin.ofNat n t)
  let k := i.val
  let m := n - 1 - i.val + 1
  have hlen : k + m = n := by dsimp [k, m]; have := i.isLt; lia
  have hval : prefixValue f n = binaryValue x := by
    rw [prefixValue_eq]
    congr 1
    funext j
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt j.isLt))
  have hsplit := prefixValue_add f k m
  rw [hlen, hval] at hsplit
  have hm : n - i.val = m := by dsimp [m]; have := i.isLt; lia
  change exp ((FourierLadder.basisAngle (fun t : Fin m => f (k + t.val)) : ℂ) * I) = _
  rw [basisAngle_prefix (fun t => f (k + t)) m, hm, hsplit]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * (prefixValue f k * 2 ^ m + prefixValue (fun t => f (k + t)) m) /
      2 ^ m * I = prefixValue f k * (2 * Real.pi * I) +
      2 * Real.pi * prefixValue (fun t => f (k + t)) m / 2 ^ m * I by field_simp,
    exp_add, exp_nat_mul_two_pi_mul_I, one_mul]

/-- The normalized Fourier output, expressed in the register's tensor factors. -/
def fourierState : UnitState (Memory n) :=
  product fun i => Qubit.phaseState (suffixAngle x i.rev)

private theorem phase_coordinate (θ : ℝ) (b : Fin 2) :
    inner ℂ (ZBasis 2 b) (Qubit.phaseState θ).val =
      ((Real.sqrt 2 : ℂ)⁻¹) * exp ((θ : ℂ) * I) ^ b.val := by
  rw [Qubit.phaseState_val]
  fin_cases b <;> simp [inner_smul_right, inner_add_right]

/-- Every output coordinate is the normalized DFT kernel at the two big-endian word values. -/
theorem fourierState_amplitude (y : Fin n → Fin 2) :
    inner ℂ (registerBasis (ZBasis 2) n y) (fourierState x).val =
      ((Real.sqrt 2 : ℂ)⁻¹) ^ n *
        exp (2 * (Real.pi : ℂ) * binaryValue x * binaryValue y / 2 ^ n * I) := by
  rw [fourierState, product, inner_registerBasis_productState]
  simp_rw [phase_coordinate, exp_suffixAngle, ← exp_nat_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← exp_sum]
  congr 2
  generalize binaryValue x = a
  unfold binaryValue
  push_cast
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hp : (2 : ℂ) ^ n = 2 ^ (n - i.rev.val) * 2 ^ (n - 1 - i.val) := by
    rw [← pow_add]
    congr 1
    have := i.isLt
    simp only [Fin.val_rev]
    lia
  rw [hp]
  field_simp

/-- Source total correctness with the normalized DFT state as the postcondition. -/
theorem sourceDeriv_fourierState :
    SourceDerivTot (.ofEffect (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2)
      (x i))) fun _ => True) (circuit n) (.ofEffect (Assertion.pure (fourierState x))
        fun _ => True) :=
  .conseq (fun _ h => ⟨h, le_rfl⟩) (sourceDeriv_circuit x) (fun _ _ => ⟨trivial, le_rfl⟩)

/-- The counted circuit derives the Fourier triple on every computational basis input. -/
theorem derivTot_fourierState :
    DerivTot (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) (circuit n)
      (Assertion.pure (fourierState x)) := by
  simpa only [CQAssertion.toAssn_ofEffect_true] using (sourceDeriv_fourierState x).toDerivTot

/-- The Fourier triple holds for every initial classical store. -/
theorem validTot_fourierState :
    validTot (Assertion.pure (product fun i => UnitState.ofBasis (ZBasis 2) (x i))) (circuit n)
      (Assertion.pure (fourierState x)) :=
  (derivTot_fourierState x).sound

end

end QuantumProgram.FourierIteration
