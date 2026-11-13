/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Measurement.POVM
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Finite POVM clients

Mixed inputs, pure-state compatibility, Bell marginals, nonprojective measurements,
zero effects, and empty outcome/zero-dimensional boundaries.
-/

open CategoryTheory Qudit
open scoped ComplexOrder BigOperators

noncomputable section

local notation "ρ₀" => Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))
local notation "ρ₁" => Density.pure (UnitState.ofBasis (ZBasis 2) (1 : Fin 2))

-- Arbitrary mixed states give normalized probabilities in any finite dimension.
example (n : ℕ) (ρ : Density (std n)) :
    ∑ i, (POVM.computational n).probability ρ i = 1 :=
  POVM.sum_probability_computational n ρ

-- A basis eigenstate is detected with certainty, and an orthogonal state is excluded.
example : (POVM.computational 2).probability ρ₀ 0 = 1 := by
  simp [POVM.computational, POVM.probability_ofBasis_pure]

example : (POVM.computational 2).probability ρ₁ 0 = 0 := by
  simp [POVM.computational, POVM.probability_ofBasis_pure]

-- Classical mixing gives its actual mixing weight, not just a normalized total.
example (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (POVM.computational 2).probability (Density.mix p hp₀ hp₁ ρ₀ ρ₁) 0 = p := by
  rw [POVM.probability_mix]
  simp [POVM.computational, POVM.probability_ofBasis_pure]

-- The existing Hadamard measurement agrees with the mixed-state interface.
example (i : Fin 2) :
    (POVM.computational 2).probability
      (Density.pure ⟨hadamardZero,
        (state.normalized_iff_norm_eq_one _).mpr hadamard_zero_unit⟩) i = 1 / 2 := by
  have h := POVM.probability_ofBasis_pure_eq_scalar (ZBasis 2)
    ⟨hadamardZero, (state.normalized_iff_norm_eq_one _).mpr hadamard_zero_unit⟩ i
  rw [hadamard_zero_probability] at h
  simpa [POVM.computational] using congrArg Complex.re h

-- Every basis measurement on a Bell marginal is uniform.
example (b : OrthonormalBasis (Fin 2) ℂ Qubit.state) (i : Fin 2) :
    (POVM.ofBasis b).probability bellDensity.partialTraceRight i = 1 / 2 := by
  rw [POVM.probability_ofBasis, bellDensity_partialTraceRight_op]
  simp [inner_smul_right]

-- Three full-rank effects on a qubit: outcome count is independent of dimension,
-- and POVM effects need not be projections or rank one.
private def uniformThree : POVM Qubit (Fin 3) where
  op _ := (1 / 3 : ℂ) • 1
  positive _ := LinearMap.isPositive_one.smul_of_nonneg
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  sum_op := by
    simp only [Fin.sum_univ_three, ← add_smul]
    norm_num

example (ρ : Density Qubit) (i : Fin 3) : uniformThree.probability ρ i = 1 / 3 := by
  simp [POVM.probability, uniformThree, Density.expectation, Density.expectationComplex,
    Operator.trace, ρ.trace_one]

example : uniformThree.op 0 * uniformThree.op 0 ≠ uniformThree.op 0 := by
  intro h
  have htr := congrArg Operator.trace h
  norm_num [uniformThree, smul_mul_smul, Operator.trace, LinearMap.trace_one, Qubit] at htr

-- A zero-probability outcome is allowed: positivity was not strengthened to definiteness.
private def zeroOutcome : POVM Qubit (Fin 2) where
  op i := if i = 0 then 0 else 1
  positive i := by split_ifs <;> simp
  sum_op := by simp [Fin.sum_univ_two]

example (ρ : Density Qubit) : zeroOutcome.probability ρ 0 = 0 := by
  simp [POVM.probability, zeroOutcome, Density.expectation, Density.expectationComplex]

-- Empty outcomes cannot carry total probability one when an input density exists.
example {H : Qudit} (ρ : Density H) : IsEmpty (POVM H (Fin 0)) := by
  refine ⟨fun M => ?_⟩
  have h := M.sum_probability ρ
  simp at h

-- Zero-dimensional computation still has its empty POVM, but it has no density input.
example : POVM (std 0) (Fin 0) := POVM.computational 0

example : IsEmpty (Density (std 0)) := inferInstance

-- The older amplitude-effect counterexample is preserved.
example :
    (∑ i : Fin 2, MonoidalCategory.probability
      (ketArrow (ZBasis 2 0)) (counterexampleEffect i)) ≠ 1 :=
  counterexample_probability_sum_ne_one

end
