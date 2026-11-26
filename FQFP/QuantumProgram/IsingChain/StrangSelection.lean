/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.IsingChain.StrangError

/-!
# Choosing the cheaper certified Ising splitting

Each orientation receives its own step count from the same tolerance. The selector compares
the CNOT counts of the two emitted instruction lists and breaks ties in favor of the field.
-/

@[expose] public section

open Qudit NormedSpace

namespace QuantumProgram.IsingChain

noncomputable section

variable {e : ℕ}

/-- Positive number of steps prescribed by the second-order coefficient bound. -/
def strangSteps (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t ε : ℝ) : ℕ :=
  max 1 ⌈Real.sqrt (|t| ^ 3 * strangConstant L h J / ε)⌉₊

/-- The certified template always emits at least one step. -/
theorem strangSteps_pos (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t ε : ℝ) :
    0 < strangSteps L h J t ε := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)

/-- Physical circuit for a given outer layer and tolerance. -/
def strangCandidate (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t ε : ℝ) : List (Gate e) :=
  strangCircuit L h J t (strangSteps L h J t ε)

/-- Either candidate realizes the target up to the requested positive tolerance. -/
theorem strangCandidate_error_le (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(program (strangCandidate L h J t ε)).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤ ε := by
  let r := strangSteps L h J t ε
  have hr : 0 < (r : ℝ) := Nat.cast_pos.mpr (strangSteps_pos ..)
  apply (strangCircuit_error_le L h J t (strangSteps_pos L h J t ε)).trans
  have hceil : Real.sqrt (|t| ^ 3 * strangConstant L h J / ε) ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    (((div_le_iff₀ hε).mp (Real.sqrt_le_iff.mp hceil).2).trans_eq (mul_comm ..))

/-- Select the outer layer by the CNOT costs of the two certified candidates. -/
def selectedLayer (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t ε : ℝ) : Layer :=
  if cnotCount (strangCandidate .field h J t ε) ≤ cnotCount (strangCandidate .interaction h J t ε)
  then .field else .interaction

/-- The selected list meets the operator tolerance and attains the smaller certified CNOT cost. -/
theorem selectedCircuit_spec (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    let gs := strangCandidate (selectedLayer h J t ε) h J t ε
    ‖(program gs).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤ ε ∧
      cnotCount gs = min (cnotCount (strangCandidate .field h J t ε))
        (cnotCount (strangCandidate .interaction h J t ε)) := by
  refine ⟨strangCandidate_error_le _ h J t hε, ?_⟩
  unfold selectedLayer
  split <;> rename_i hc
  · exact (min_eq_left hc).symm
  · exact (min_eq_right (le_of_not_ge hc)).symm

/-- Every finite POVM outcome on any input density state has probability error at most `ε`. -/
theorem selectedCircuit_probability_error_le {ι : Type*} [Fintype ι]
    (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (M : POVM (tensorPower Qubit e) ι) (ρ : Density (tensorPower Qubit e)) (i : ι) :
    let gs := strangCandidate (selectedLayer h J t ε) h J t ε
    |M.probability (ρ.map (program gs).denoteHom) i -
      M.probability (ρ.map (exactEvolution h J t).denoteHom) i| ≤ ε := by
  apply M.abs_probability_map_sub_le
  change ‖(program _).toOperator - (exactEvolution h J t).toOperator‖ ≤ _
  rw [toOperator_exactEvolution]
  exact (selectedCircuit_spec h J t hε).1

/-- The operational post-expectation of each outcome in the selected native command
approximates its probability under the exact evolution on an arbitrary input density. -/
theorem abs_postH_selectedCircuit_sub_probability_le {Store ι : Type*} [Fintype ι]
    (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε)
    (M : POVM (tensorPower Qubit e) ι) (ρ : Density (tensorPower Qubit e)) (i : ι) (σ : Store) :
    let gs := strangCandidate (selectedLayer h J t ε) h J t ε
    let c := Configuration.mk (some (command gs)) ⟨σ, ρ.op, ρ.positive⟩
    |(c.PostH (fun _ => M.op i)).toReal - M.probability (ρ.map (exactEvolution h J t).denoteHom) i|
      ≤ ε := by
  dsimp only
  rw [postH_command_probability _ M ρ i σ]
  exact selectedCircuit_probability_error_le h J t hε M ρ i

end

end QuantumProgram.IsingChain
