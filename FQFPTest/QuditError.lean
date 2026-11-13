/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Error.ProductFormula
import FQFP.CQM.Qudit.Channel.Basic

/-!
# Trace-distance and simulation-error clients

These check normalization on orthogonal and mixed states, zero-dimensional boundaries,
global phases, nonprojective POVMs, and compatibility with the existing channel interface.
-/

open CategoryTheory CategoryTheory.DaggerCategory Qudit
open scoped ComplexOrder BigOperators

noncomputable section

local notation "ρ₀" => Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))
local notation "ρ₁" => Density.pure (UnitState.ofBasis (ZBasis 2) (1 : Fin 2))

-- Orthogonal pure states have distance exactly one, not two or one half.
private lemma orthogonal_distance : (ρ₀).traceDistance ρ₁ = 1 := by
  apply le_antisymm (Density.traceDistance_le_one _ _)
  have h := (POVM.computational 2).abs_probability_sub_le_traceDistance ρ₀ ρ₁ 0
  simpa [POVM.computational, POVM.probability_ofBasis_pure] using h

-- Diagonal mixed-state trace distance agrees with the classical Bernoulli distance.
example (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    (Density.mix p hp₀ hp₁ ρ₀ ρ₁).traceDistance (Density.mix q hq₀ hq₁ ρ₀ ρ₁) =
      |p - q| := by
  have heq : (Density.mix p hp₀ hp₁ ρ₀ ρ₁).op - (Density.mix q hq₀ hq₁ ρ₀ ρ₁).op =
      ((p - q : ℝ) : ℂ) • ((ρ₀).op - (ρ₁).op) := by
    simp only [Density.op_mix]
    push_cast
    module
  rw [Density.traceDistance, heq, LinearMap.traceNorm_smul, Complex.norm_real,
    Real.norm_eq_abs]
  have h := orthogonal_distance
  unfold Density.traceDistance at h
  rw [mul_div_assoc, h, mul_one]

-- Global phases remain invisible to trace distance.
example (v : UnitState Qubit) :
    (Density.pure (v.phase Complex.I (by simp))).traceDistance (Density.pure v) = 0 := by
  rw [Density.pure_phase, Density.traceDistance_self]

-- The entire outcome set has zero probability discrepancy.
example (ρ σ : Density Qubit) :
    |(∑ i, (POVM.computational 2).probability ρ i) -
      ∑ i, (POVM.computational 2).probability σ i| = 0 := by
  rw [POVM.sum_probability, POVM.sum_probability]
  norm_num

-- Three nonprojective full-rank effects are legitimate clients of the error bound.
private def uniformThree : POVM Qubit (Fin 3) where
  op _ := (1 / 3 : ℂ) • 1
  positive _ := LinearMap.isPositive_one.smul_of_nonneg
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  sum_op := by
    simp only [Fin.sum_univ_three, ← add_smul]
    norm_num

example (ρ σ : Density Qubit) (s : Finset (Fin 3)) :
    |(∑ i ∈ s, uniformThree.probability ρ i) - ∑ i ∈ s, uniformThree.probability σ i| ≤
      ρ.traceDistance σ := uniformThree.abs_sum_probability_sub_le_traceDistance ρ σ s

-- A qubit gate estimate applies to arbitrary mixed inputs of the existing channel layer.
example (ρ : Density Qubit) (U : Qubit ⟶ Qubit) [IsUnitary U] {ε : ℝ}
    (hε : ‖(U.hom - Qubit.H.asHom.hom).toContinuousLinearMap‖ ≤ ε) (i : Fin 2) :
    |(POVM.computational 2).probability ((QuantumChannel.ofIsometry U).map ρ) i -
      (POVM.computational 2).probability ((QuantumChannel.ofIsometry Qubit.H.asHom).map ρ) i| ≤
      ε := by
  rw [QuantumChannel.map_ofIsometry, QuantumChannel.map_ofIsometry]
  exact (POVM.computational 2).abs_probability_map_sub_le ρ U Qubit.H.asHom hε i

-- All analysis remains meaningful on the zero space; it still has no density input.
example : LinearMap.traceNorm (0 : Operator (std 0)) = 0 := LinearMap.traceNorm_zero

example : IsEmpty (Density (std 0)) := inferInstance

-- The unitary bridge requires no manually supplied named instance.
example {H : Qudit} (U : unitary (H.state →L[ℂ] H.state)) : IsUnitary (unitaryHom U) :=
  inferInstance

example {H : Qudit} (ρ : Density H) (U V : unitary (H.state →L[ℂ] H.state)) :
    (ρ.evolve U).traceDistance (ρ.evolve V) ≤ ‖U.val - V.val‖ :=
  ρ.traceDistance_evolve_le_opNorm U V

-- A nontrivial Hilbert operator model: the original commutator bound controls a qutrit POVM.
example {Υ Γ : ℕ} (P : TrotterError.ProductFormulaData Υ Γ)
    (A : Fin Γ → (std 3).state →L[ℂ] (std 3).state) (hA : ∀ i, star (A i) = -(A i))
    (p : ℕ) (hp : 1 ≤ p) (horder : P.IsOrderOf p A) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (ρ : Density (std 3)) (i : Fin 3) :
    |(POVM.computational 3).probability (ρ.evolve (productFormulaEvolution P A hA t)) i -
      (POVM.computational 3).probability (ρ.evolve (exactEvolution A hA t)) i| ≤
      2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * TrotterError.αComm p A * t ^ (p + 1) :=
  abs_probability_productFormula_sub_le (POVM.computational 3) P A hA p hp horder hΥ t ht ρ i

-- A single-generator Lie-Trotter formula supplies an actual order proof, with no oracle assumption.
example (A : (std 3).state →L[ℂ] (std 3).state) (hA : star A = -A)
    (t : ℝ) (ht : 0 ≤ t) (ρ : Density (std 3)) :
    (ρ.evolve (productFormulaEvolution (TrotterError.lieTrotterData 1) (fun _ => A)
      (fun _ => hA) t)).traceDistance (ρ.evolve (exactEvolution (Γ := 1) (fun _ => A)
        (fun _ => hA) t)) ≤ TrotterError.αComm 1 (fun _ : Fin 1 => A) * t ^ 2 := by
  have horder : (TrotterError.lieTrotterData 1).IsOrderOf 1 (fun _ => A) := by
    have heq (s : ℝ) : (TrotterError.lieTrotterData 1).eval (fun _ => A) s =
        NormedSpace.exp (s • ∑ _ : Fin 1, A) := by
      rw [TrotterError.lieTrotterData_eval_eq]
      simp [List.finRange_succ]
    simp only [TrotterError.ProductFormulaData.IsOrderOf, heq, sub_self, norm_zero]
    exact Asymptotics.isBigO_zero _ _
  simpa using traceDistance_productFormula_le (TrotterError.lieTrotterData 1)
    (fun _ => A) (fun _ => hA) 1 (by norm_num) horder (by norm_num) t ht ρ

end
