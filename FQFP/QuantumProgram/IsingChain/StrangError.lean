/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.IsingChain.Error
public import FQFP.QuantumProgram.IsingChain.Strang

/-!
# Error certificates for fused Ising circuits

The two orientations share an exact target. Their different nested-commutator weights
give different certified step counts.
-/

@[expose] public section

open Qudit NormedSpace TrotterError

namespace QuantumProgram.IsingChain

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

variable {e : ℕ}

private theorem strang_pair_bound {H : Qudit} [Nontrivial H.state] (X Y : Operator H)
    (hX : star X = -X) (hY : star Y = -Y) {r : ℕ} (hr : 0 < r) :
    ‖(exp (((1 / r : ℝ) / 2) • X) * exp ((1 / r : ℝ) • Y) *
      exp (((1 / r : ℝ) / 2) • X)) ^ r - exp (X + Y)‖ ≤
      (‖⁅Y, ⁅Y, X⁆⁆‖ / 12 + ‖⁅X, ⁅X, Y⁆⁆‖ / 24) / (r : ℝ) ^ 2 := by
  let : NormedAlgebra ℝ (Operator H) := .restrictScalars ℝ ℂ _
  let : NormedAlgebra ℚ (Operator H) := .restrictScalars ℚ ℂ _
  have half (s : ℝ) : exp ((s / 2) • Y) * exp ((s / 2) • Y) = exp (s • Y) := by
    rw [← exp_add_of_commute (Commute.refl _), ← add_smul, add_halves]
  have hK (i : Fin 2) : star (![X, Y] i) = -(![X, Y] i) := by
    fin_cases i <;> assumption
  have bd := norm_suzuki2_pow_sub_exp_le ![X, Y] hK (t := 1) zero_le_one hr
  simpa [suzuki2, half, upperSum, Fin.sum_univ_two, Finset.sum_filter, adPow,
    pow_two, ← div_eq_inv_mul] using bd

local notation "phase" => fun (s : ℝ) => (-Complex.I) * (s : ℂ)

private theorem phase_skew {H : Qudit} {A : Operator H} (hA : IsSelfAdjoint A) (t : ℝ) :
    star (phase t • A) = -(phase t • A) := by
  simp [StarModule.star_smul, hA.star_eq, neg_smul]

private theorem Layer.selfAdjoint (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    IsSelfAdjoint (L.hamiltonian h J) := by
  cases L
  · exact isSelfAdjoint_fieldHamiltonian h
  · exact isSelfAdjoint_interactionHamiltonian J

private theorem Layer.hamiltonian_add_other (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    L.hamiltonian h J + L.other.hamiltonian h J
      = fieldHamiltonian h + interactionHamiltonian J := by
  cases L
  · rfl
  · exact add_comm ..

/-- Nested-commutator error of a fused physical circuit at either sign of time. -/
theorem strangCircuit_error_le_commutators (L : Layer) (h : Fin (e + 1) → ℝ)
    (J : Fin e → ℝ) (t : ℝ) {r : ℕ} (hr : 0 < r) :
    let A := L.hamiltonian h J
    let B := L.other.hamiltonian h J
    ‖(program (strangCircuit L h J t r)).toOperator -
      exp (phase t • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤
      |t| ^ 3 * (‖⁅B, ⁅B, A⁆⁆‖ / 12 + ‖⁅A, ⁅A, B⁆⁆‖ / 24) / (r : ℝ) ^ 2 := by
  dsimp only
  rcases subsingleton_or_nontrivial (tensorPower Qubit e).state with hS | hS
  · rw [Subsingleton.elim (program _).toOperator (exp _), sub_self, norm_zero]
    positivity
  let A := L.hamiltonian h J
  let B := L.other.hamiltonian h J
  have bd := strang_pair_bound (H := tensorPower Qubit e) (phase t • A) (phase t • B)
    (phase_skew (L.selfAdjoint h J) t) (phase_skew (L.other.selfAdjoint h J) t) hr
  have scale (u : ℝ) (P : Operator (tensorPower Qubit e)) :
      u • (phase t • P) = phase (t * u) • P := by
    rw [← Complex.coe_smul, smul_smul]
    congr 1
    change (u : ℂ) * (-Complex.I * t) = -Complex.I * ↑(t * u)
    push_cast
    ring
  rw [← smul_add, L.hamiltonian_add_other] at bd
  simp only [scale, smul_lie, lie_smul, norm_smul, norm_mul, norm_neg, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul] at bd
  rw [toOperator_strangCircuit]
  unfold strangStep Layer.evolution
  rw [show t / (r : ℝ) = t * (1 / r) by ring,
    show t * (1 / (r : ℝ)) / 2 = t * (1 / r / 2) by ring]
  exact bd.trans_eq (by ring)

/-- Sum of absolute coefficients of one layer. -/
def Layer.weight (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) : ℝ :=
  match L with
  | .field => ∑ i, |h i|
  | .interaction => ∑ j, |J j|

private theorem norm_hamiltonian_le (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    ‖L.hamiltonian h J‖ ≤ L.weight h J := by
  cases L
  · exact norm_fieldHamiltonian_le h
  · exact norm_interactionHamiltonian_le J

private theorem layer_commutator_le (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    ‖⁅L.hamiltonian h J, L.other.hamiltonian h J⁆‖ ≤ 2 * couplingBound h J := by
  cases L
  · rw [← norm_neg, lie_skew]
    exact norm_commutator_le_coefficients h J
  · exact norm_commutator_le_coefficients h J

private theorem nested_layer_le (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) :
    ‖⁅L.hamiltonian h J, ⁅L.hamiltonian h J, L.other.hamiltonian h J⁆⁆‖ ≤
      4 * L.weight h J * couplingBound h J := by
  apply (norm_commutator_le _ _).trans
  calc
    _ ≤ 2 * L.weight h J * (2 * couplingBound h J) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (norm_hamiltonian_le L h J) (by norm_num))
        (layer_commutator_le L h J) (norm_nonneg _) (by
          exact mul_nonneg (by norm_num) ((norm_nonneg _).trans (norm_hamiltonian_le L h J)))
    _ = _ := by ring

/-- Coefficient-only Strang constant using the endpoint bound on the first commutator. -/
def strangConstant (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ) : ℝ :=
  4 * L.other.weight h J * couplingBound h J / 12 + 4 * L.weight h J * couplingBound h J / 24

/-- Coefficient-only operator error for the actual fused native instruction list. -/
theorem strangCircuit_error_le (L : Layer) (h : Fin (e + 1) → ℝ) (J : Fin e → ℝ)
    (t : ℝ) {r : ℕ} (hr : 0 < r) :
    ‖(program (strangCircuit L h J t r)).toOperator -
      exp (phase t • (fieldHamiltonian h + interactionHamiltonian J))‖ ≤
      |t| ^ 3 * strangConstant L h J / (r : ℝ) ^ 2 := by
  apply (strangCircuit_error_le_commutators L h J t hr).trans
  unfold strangConstant
  have hL : L.other.other = L := by cases L <;> rfl
  gcongr
  · simpa only [hL] using nested_layer_le L.other h J
  · exact nested_layer_le L h J

end

end QuantumProgram.IsingChain
