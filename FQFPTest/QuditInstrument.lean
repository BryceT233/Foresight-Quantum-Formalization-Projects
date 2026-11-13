/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Measurement.Luders
import FQFP.CQM.Qudit.Teleportation.Instrument

/-!
# Instrument clients

Nonprojective two-result measurement, impossible outcomes, repeated projective measurements,
hidden Kraus alternatives, classical readout and adaptive mixed-state teleportation.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Qudit
open scoped ComplexOrder BigOperators

noncomputable section

local notation "ρ₀" => Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))

private def coin : POVM Qubit (Fin 2) where
  op _ := (1 / 2 : ℂ) • 1
  positive _ := LinearMap.isPositive_one.smul_of_nonneg
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  sum_op := by simp only [Fin.sum_univ_two, ← add_smul]; norm_num

-- Both coin effects are full-rank and are not projections.
example (i : Fin 2) : coin.op i * coin.op i ≠ coin.op i := by
  intro h
  have ht := congrArg (fun A : Operator Qubit => A.trace) h
  norm_num [coin, smul_mul_assoc, mul_smul_comm, smul_smul, Operator.trace,
    LinearMap.trace_one] at ht

private lemma coin_probability (ρ : Density Qubit) (i : Fin 2) :
    coin.luders.probability ρ i = 1 / 2 := by
  rw [POVM.probability_luders]
  simp [POVM.probability, coin, Density.expectation, Density.expectationComplex,
    Operator.trace, ρ.trace_one]

private lemma coin_sqrt (i : Fin 2) :
    (coin.op i).sqrt = ((Real.sqrt (1 / 2) : ℝ) : ℂ) • 1 := by
  apply Operator.sqrt_unique
  · simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num [coin]
  · exact LinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast Real.sqrt_nonneg (1 / 2))

-- This nonprojective Lüders measurement leaves the state unchanged after conditioning.
example (ρ : Density Qubit) (i : Fin 2) (hp : 0 < coin.luders.probability ρ i) :
    coin.luders.conditional ρ i hp = ρ := by
  apply Density.ext
  rw [Instrument.op_conditional, coin_probability, POVM.luders_branch_apply, coin_sqrt]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  have hs : ((Real.sqrt (1 / 2) : ℝ) : ℂ) * ((Real.sqrt (1 / 2) : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [← mul_assoc, mul_assoc _ _ _, hs]
  norm_num

-- An impossible basis result is represented by the zero operator.
example : (POVM.computational 2).luders.branch 1 (ρ₀).op = 0 := by
  apply Instrument.branch_eq_zero_of_probability_eq_zero
  simp [POVM.probability_luders, POVM.computational, POVM.probability_ofBasis_pure]

-- Repeating a basis measurement returns the same result with certainty.
example {H : Qudit} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H) (i j : ι)
    (hp : 0 < (POVM.ofBasis b).luders.probability ρ i) :
    (POVM.ofBasis b).luders.probability ((POVM.ofBasis b).luders.conditional ρ i hp) j =
      if i = j then 1 else 0 := by
  rw [POVM.conditional_luders_ofBasis, POVM.probability_luders]
  simp [POVM.probability_ofBasis_pure, UnitState.ofBasis, b.inner_eq_ite, apply_ite, eq_comm]

-- Grouping two hidden Kraus alternatives into each observed result is supported.
private def grouped : Instrument Qubit Qubit (Fin 2) :=
  Instrument.ofKraus (fun (_ : Fin 2) (_ : Fin 2) =>
    (1 / 2 : ℂ) • (LinearMap.id : Operator Qubit)) (by
    simp only [map_smulₛₗ, map_div₀, map_one, map_ofNat, LinearMap.adjoint_id,
      LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, smul_smul,
      Fin.sum_univ_two, ← add_smul]
    norm_num
    rfl)

example (ρ : Density Qubit) (i : Fin 2) : grouped.probability ρ i = 1 / 2 := by
  unfold Instrument.probability grouped Instrument.ofKraus
  rw [Superoperator.kraus_apply]
  norm_num [Operator.trace, LinearMap.smul_comp, LinearMap.comp_smul,
    map_smulₛₗ, two_mul, ρ.trace_one]

-- Recording a result is observable as the same probability, and reading its block gives its branch.
example (ρ : Density Qubit) (i : Fin 2) :
    (POVM.computational 2).probability
      ((coin.luders.record (ZBasis 2)).map ρ).partialTraceLeft i = 1 / 2 := by
  rw [Instrument.partialTraceLeft_record]
  exact (coin.luders.probability_outcomeState (ZBasis 2) ρ i).trans (coin_probability ρ i)

example (ρ : Density Qubit) (i : Fin 2) :
    (Instrument.read Qubit (ZBasis 2)).branch i ((coin.luders.record (ZBasis 2)).map ρ).op =
      coin.luders.branch i ρ.op := coin.luders.read_record (ZBasis 2) ρ.op i

-- The instrument contract includes rectangular quantum outputs and a separate classical carrier.
example (I : Instrument Qubit (std 3) (Fin 2)) (ρ : Density Qubit) :
    ((I.record (ZBasis 2)).map ρ).partialTraceRight = I.toChannel.map ρ :=
  I.partialTraceRight_record (ZBasis 2) ρ

-- Every Bell result is possible and its conditional corrected state is the mixed input itself.
example (ρ : Density Qubit) (i : Fin 4) :
    teleportationInstrument.conditional ρ i
      (by rw [probability_teleportationInstrument]; norm_num) = ρ :=
  conditional_teleportationInstrument ρ i _

-- The actual recorded, classically controlled protocol transmits the quantum input.
example (ρ : Density Qubit) :
    (((QuantumChannel.controlled (ZBasis 4)
      (fun i => QuantumChannel.ofIsometry (corrections i))).comp
        (teleportationMeasurement.record (ZBasis 4))).map ρ).partialTraceRight = ρ := by
  rw [← teleportationInstrument_record, partialTraceRight_teleportationInstrument_record]

-- Empty outcome sets are allowed on a zero-dimensional input; no density is invented there.
example : Instrument (std 0) Qubit (Fin 0) :=
  Instrument.ofOperators (fun i : Fin 0 => Fin.elim0 i) (Subsingleton.elim _ _)

end
