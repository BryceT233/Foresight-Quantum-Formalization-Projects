/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Unitary
public import FQFP.Analysis.Normed.Algebra.ProductFormula.RepeatedSteps
public import FQFP.CQM.Qudit.Error.UnitaryEvolution

/-!
# First-order Lie–Trotter simulation

For a finite ordered Hamiltonian decomposition, execute one exponential gate per term
in increasing index order and repeat the slice. The commutator bound determines a
positive step count for any requested positive operator-norm tolerance.
-/

@[expose] public section

open NormedSpace Qudit TrotterError

namespace QuantumProgram

noncomputable section

attribute [local instance] LieRing.ofAssociativeRing

variable {S : Qudit} {m : ℕ}

/-- The skew-adjoint Schrödinger generator of a self-adjoint Hamiltonian term (in units ℏ = 1). -/
def schrodingerGenerator (h : selfAdjoint (Operator S)) : Operator S :=
  (-Complex.I) • h.val

/-- Multiplication by `-i` turns a self-adjoint Hamiltonian into a skew-adjoint generator. -/
theorem star_schrodingerGenerator (h : selfAdjoint (Operator S)) :
    star (schrodingerGenerator h) = -schrodingerGenerator h := by
  simp [schrodingerGenerator, StarModule.star_smul, h.prop.star_eq]

/-- Evolve for time `s` under a single Hamiltonian term. -/
def hamiltonianGate (h : selfAdjoint (Operator S)) (s : ℝ) : UnitaryProgram S :=
  letI : NormedAlgebra ℚ (Operator S) := .restrictScalars ℚ ℂ _
  let U : unitary (Operator S) :=
    ⟨exp (s • schrodingerGenerator h),
      exp_smul_mem_unitary_of_skewAdjoint (star_schrodingerGenerator h) s⟩
  .gateHom .whole (unitaryHom U)

variable (h : Fin m → selfAdjoint (Operator S))

/-- One Lie–Trotter slice applies the individual term evolutions in increasing index order. -/
def trotterStep (s : ℝ) : UnitaryProgram S :=
  UnitaryProgram.sequence ((List.finRange m).map fun j => hamiltonianGate (h j) s)

/-- The straight-line program of `n` equal slices for total time `t`. -/
def trotterProgram (t : ℝ) (n : ℕ) : UnitaryProgram S :=
  UnitaryProgram.sequence (List.replicate n (trotterStep h (t / n)))

/-- Operator semantics of the generated gates, including the order within each slice. -/
theorem toOperator_trotterProgram (t : ℝ) (n : ℕ) :
    (trotterProgram h t n).toOperator =
      ((List.finRange m).reverse.map fun j => exp ((t / n) • schrodingerGenerator (h j))).prod
        ^ n := by
  have hgate (j : Fin m) (s : ℝ) :
      (hamiltonianGate (h j) s).toOperator = exp (s • schrodingerGenerator (h j)) := rfl
  simp only [trotterProgram, UnitaryProgram.toOperator_sequence, List.reverse_replicate,
    List.map_replicate, List.prod_replicate, trotterStep, ← List.map_reverse, List.map_map,
    Function.comp_def, hgate]

/-- The first-order error numerator for this ordered decomposition and time. -/
def trotterErrorConstant (t : ℝ) : ℝ :=
  (t ^ 2 / 2) * ∑ i, ‖⁅upperSum (fun j => (h j).val) i, (h i).val⁆‖

/-- A positive step count for tolerance `ε`, including a single step for a zero commutator bound. -/
def trotterSteps (t ε : ℝ) : ℕ :=
  max 1 ⌈trotterErrorConstant h t / ε⌉₊

/-- The chosen number of slices is always positive. -/
theorem trotterSteps_pos (t ε : ℝ) : 0 < trotterSteps h t ε :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)

/-- The Lie–Trotter program with its number of slices selected from the requested tolerance. -/
def trotterSimulation (t ε : ℝ) : UnitaryProgram S :=
  trotterProgram h t (trotterSteps h t ε)

/-- For either sign of time the operator-norm error is bounded by the commutator constant
divided by the number of slices. -/
theorem trotterProgram_error_le (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(trotterProgram h t n).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • ∑ j, (h j).val)‖ ≤ trotterErrorConstant h t / n := by
  rcases subsingleton_or_nontrivial S.state with hS | hS
  · rw [Subsingleton.elim (trotterProgram h t n).toOperator (exp _), sub_self, norm_zero]
    unfold trotterErrorConstant
    positivity
  let : NormedAlgebra ℚ (Operator S) := .restrictScalars ℚ ℂ _
  let : NormedAlgebra ℝ (Operator S) := .restrictScalars ℝ ℂ _
  have bound := norm_ordered_exp_pow_sub_exp_le (fun i => schrodingerGenerator (h i))
    (fun i => star_schrodingerGenerator (h i)) t hn
  rw [toOperator_trotterProgram]
  simpa only [schrodingerGenerator, upperSum, ← Finset.smul_sum, smul_lie, lie_smul,
    norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, trotterErrorConstant,
    ← Complex.coe_smul, smul_smul, mul_comm (t : ℂ)] using bound

/-- Choosing the step count from the tolerance produces a program within that operator error. -/
theorem trotterSimulation_error_le (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(trotterSimulation h t ε).toOperator -
      exp (((-Complex.I) * (t : ℂ)) • ∑ j, (h j).val)‖ ≤ ε := by
  apply (trotterProgram_error_le h t (trotterSteps_pos h t ε)).trans
  have hceil : trotterErrorConstant h t / ε ≤ (trotterSteps h t ε : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  exact (div_le_iff₀ (Nat.cast_pos.mpr (trotterSteps_pos h t ε))).mpr
    ((div_le_iff₀ hε).mp hceil |>.trans_eq (mul_comm _ _))

end

end QuantumProgram
