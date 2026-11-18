/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.IsingChain.StrangSelection

/-!
# Two-qubit Ising gate budgets at unit time

Both sites have unit field and the operator tolerance is one hundredth. The results below
compare the existing first-order circuit and both fused second-order circuits using their
certified step counts.
-/

public section

namespace QuantumProgram.IsingChain

local notation "fields" => (![1, 1] : Fin 2 → ℝ)
local notation "tol" => (1 / 100 : ℝ)

private theorem strangSteps_eq_succ (L : Layer) (J : ℝ) (k : ℕ)
    (hlo : (k : ℝ) ^ 2 < strangConstant L fields ![J] / tol)
    (hhi : strangConstant L fields ![J] / tol ≤ (k + 1 : ℝ) ^ 2) :
    strangSteps L fields ![J] 1 tol = k + 1 := by
  simp only [strangSteps, abs_one, one_pow, one_mul]
  have hc : ⌈Real.sqrt (strangConstant L fields ![J] / tol)⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    simpa using And.intro (Real.lt_sqrt_of_sq_lt hlo)
      (Real.sqrt_le_iff.mpr ⟨by positivity, hhi⟩)
  rw [hc, max_eq_right (by lia)]

private theorem constants_unit_fields (J : ℝ) :
    strangConstant .field fields ![J] = 2 * |J| ^ 2 / 3 + 2 * |J| / 3 ∧
    strangConstant .interaction fields ![J] = 4 * |J| / 3 + |J| ^ 2 / 3 := by
  constructor <;> simp [strangConstant, Layer.weight, Layer.other, couplingBound, Fin.sum_univ_two]
    <;> ring_nf <;> rw [sq_abs]

/-- Certified first-order and both second-order step counts at coupling 1. -/
theorem stepCounts_coupling_unit :
    steps fields ![1] 1 tol = 200 ∧
    strangSteps .field fields ![1] 1 tol = 12 ∧
    strangSteps .interaction fields ![1] 1 tol = 13 := by
  refine ⟨by norm_num [steps, couplingBound], ?_, ?_⟩
  · apply strangSteps_eq_succ .field 1 11 <;> rw [(constants_unit_fields _).1] <;> norm_num
  · apply strangSteps_eq_succ .interaction 1 12 <;> rw [(constants_unit_fields _).2] <;> norm_num

/-- At coupling 1 the field-outer circuit wins the certified CNOT comparison. -/
theorem cnotCounts_coupling_unit :
    cnotCount (circuit fields ![1] 1 (steps fields ![1] 1 tol)) = 400 ∧
    cnotCount (strangCandidate .field fields ![1] 1 tol) = 24 ∧
    cnotCount (strangCandidate .interaction fields ![1] 1 tol) = 28 ∧
    selectedLayer fields ![1] 1 tol = .field := by
  obtain ⟨h₁, h₂, h₃⟩ := stepCounts_coupling_unit
  simp only [selectedLayer, strangCandidate, cnotCount_circuit, cnotCount_strangCircuit,
    strangSteps_pos]
  rw [h₁, h₂, h₃]
  decide

/-- Certified first-order and both second-order step counts at coupling 8. -/
theorem stepCounts_coupling_eight :
    steps fields ![8] 1 tol = 1600 ∧
    strangSteps .field fields ![8] 1 tol = 70 ∧
    strangSteps .interaction fields ![8] 1 tol = 57 := by
  refine ⟨by norm_num [steps, couplingBound], ?_, ?_⟩
  · apply strangSteps_eq_succ .field 8 69 <;> rw [(constants_unit_fields _).1] <;> norm_num
  · apply strangSteps_eq_succ .interaction 8 56 <;> rw [(constants_unit_fields _).2] <;> norm_num

/-- At coupling 8 the interaction-outer circuit wins the certified CNOT comparison. -/
theorem cnotCounts_coupling_eight :
    cnotCount (circuit fields ![8] 1 (steps fields ![8] 1 tol)) = 3200 ∧
    cnotCount (strangCandidate .field fields ![8] 1 tol) = 140 ∧
    cnotCount (strangCandidate .interaction fields ![8] 1 tol) = 116 ∧
    selectedLayer fields ![8] 1 tol = .interaction := by
  obtain ⟨h₁, h₂, h₃⟩ := stepCounts_coupling_eight
  simp only [selectedLayer, strangCandidate, cnotCount_circuit, cnotCount_strangCircuit,
    strangSteps_pos]
  rw [h₁, h₂, h₃]
  decide

end QuantumProgram.IsingChain
