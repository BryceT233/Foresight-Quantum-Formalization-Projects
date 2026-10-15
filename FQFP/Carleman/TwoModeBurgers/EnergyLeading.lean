/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Obstruction
public import FQFP.Carleman.TwoModeBurgers.Closure

/-!
# Anisotropic energy leading coefficients

The first Lie derivative of energy has degree two. Its later iterates have a
nonzero `a²b^(n-1)` coefficient when the damping rates differ.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

private lemma coefficient_lieDerivation_energy_20 (α γ β : ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) energy).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 0) = -α := by
  rw [lieDerivation_energy]
  simp [X_pow_eq_monomial, Finsupp.ext_iff, Fin.forall_fin_two]

private lemma coefficient_lieDerivation_energy_02 (α γ β : ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) energy).coeff
      (Finsupp.single 0 0 + Finsupp.single 1 2) = -γ := by
  rw [lieDerivation_energy]
  simp [X_pow_eq_monomial, Finsupp.ext_iff, Fin.forall_fin_two]

/-- The first energy derivative remains quadratic. -/
lemma lieDerivation_energy_totalDegree_le_two (α γ β : ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) energy).totalDegree ≤ 2 := by
  have heq : (mkDerivation ℝ (vectorField α γ β)) energy =
      C (-α) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 +
        C (-γ) * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2 := by
    rw [lieDerivation_energy]
    simp only [map_neg]
    ring
  rw [heq]
  have h₁ := totalDegree_mul (C (-α) : MvPolynomial (Fin 2) ℝ) ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2)
  have h₂ := totalDegree_mul (C (-γ) : MvPolynomial (Fin 2) ℝ) ((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)
  have h₃ := totalDegree_pow (X 0 : MvPolynomial (Fin 2) ℝ) 2
  have h₄ := totalDegree_pow (X 1 : MvPolynomial (Fin 2) ℝ) 2
  have hadd := totalDegree_add
    (C (-α) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2)
    (C (-γ) * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)
  simp only [totalDegree_C, totalDegree_X] at h₁ h₂ h₃ h₄
  lia

/-- After the first step, each energy iterate gains at most one degree. -/
theorem lieIterate_energy_totalDegree_le (α γ β : ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (energy)).totalDegree ≤ n + 2 := by
  induction n with
  | zero => simpa only [Function.iterate_succ_apply', Function.iterate_zero,
      id_eq, zero_add] using
      lieDerivation_energy_totalDegree_le_two α γ β
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := lieDerivation_totalDegree_le α γ β
      (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) (energy))
    lia

private lemma coefficient_zero_lieIterate_energy_high (α γ β : ℝ) (n k : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 1]) energy).coeff
      (Finsupp.single 0 0 + Finsupp.single 1 (k + 3)) = 0 := by
  induction n with
  | zero =>
    exact coefficient_eq_zero_of_totalDegree_lt _ _ _
      (by have h := lieIterate_energy_totalDegree_le α γ β 0; lia)
  | succ n ih =>
    rw [Function.iterate_succ_apply', show k + 3 = (k + 2) + 1 by lia,
      coefficient_zero_lieDerivation]
    simp only [show (k + 2) + 1 = k + 3 by lia, ih, mul_zero]

private lemma coefficient_lieIterate_energy_base (α γ β : ℝ) :
    (((mkDerivation ℝ (vectorField α γ β))^[2]) energy).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 1) = 2 * β * (γ - α) := by
  change (((mkDerivation ℝ (vectorField α γ β))^[1 + 1]) energy).coeff
    (Finsupp.single 0 2 + Finsupp.single 1 1) = _
  rw [Function.iterate_succ_apply', coefficient_two_lieDerivation]
  have hdeg := lieDerivation_energy_totalDegree_le_two α γ β
  have hzero : (((mkDerivation ℝ (vectorField α γ β))^[1]) energy).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 1) = 0 :=
    coefficient_eq_zero_of_totalDegree_lt _ _ _
      (by simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] using
        (show ((mkDerivation ℝ (vectorField α γ β)) energy).totalDegree < 2 + 1 by lia))
  rw [hzero]
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
  rw [coefficient_lieDerivation_energy_20, coefficient_lieDerivation_energy_02]
  ring

/-- The `a²b^(n+1)` coefficient of the `(n+2)`nd energy iterate. -/
theorem coefficient_lieIterate_energy (α γ β : ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) energy).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 (n + 1)) =
      2 ^ (n + 1) * β ^ (n + 1) * (γ - α) := by
  induction n with
  | zero => simpa using coefficient_lieIterate_energy_base α γ β
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by lia, Function.iterate_succ_apply',
      coefficient_two_lieDerivation]
    have hdeg := lieIterate_energy_totalDegree_le α γ β (n + 1)
    have hzero₁ : (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) energy).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (n + 1 + 1)) = 0 :=
      coefficient_eq_zero_of_totalDegree_lt _ _ _ (by lia)
    have hzero₂ : (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) energy).coeff
        (Finsupp.single 0 0 + Finsupp.single 1 (n + 1 + 2)) = 0 := by
      simpa only [show n + 1 + 2 = n + 3 by lia] using
        coefficient_zero_lieIterate_energy_high α γ β (n + 1) n
    rw [hzero₁, hzero₂, ih]
    simp only [pow_succ]
    ring

/-- Anisotropic damping gives every later energy iterate its maximal degree. -/
theorem lieIterate_energy_totalDegree (α γ β : ℝ) (hβ : β ≠ 0)
    (hαγ : α ≠ γ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) (energy)).totalDegree = n + 3 := by
  have hcoeff : (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) energy).coeff
      (Finsupp.single 0 2 + Finsupp.single 1 (n + 1)) ≠ 0 := by
    rw [coefficient_lieIterate_energy]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ hβ)) (sub_ne_zero.mpr (Ne.symm hαγ))
  have hlow := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hlow' : 2 + (n + 1) ≤
      (((mkDerivation ℝ (vectorField α γ β))^[n + 2]) energy).totalDegree := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hlow
  have hhigh := lieIterate_energy_totalDegree_le α γ β (n + 1)
  lia

/-- Unequal damping precludes a finite invariant polynomial closure of energy. -/
theorem no_finite_polynomial_closure_energy (α γ β : ℝ) (hβ : β ≠ 0)
    (hαγ : α ≠ γ) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ energy ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  rintro ⟨V, hfin, henergy, hV⟩
  have : FiniteDimensional ℝ V := hfin
  obtain ⟨N, hN⟩ := finiteDimensional_totalDegree_bounded V
  have hmem := lieIterate_mem_invariant α γ β V hV henergy (N + 2)
  have hdegree := hN _ hmem
  rw [lieIterate_energy_totalDegree α γ β hβ hαγ] at hdegree
  lia

/-- Under nonzero coupling, energy has a finite polynomial closure exactly at equal damping. -/
theorem energy_finite_polynomial_closure_iff (α γ β : ℝ) (hβ : β ≠ 0) :
    (∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ energy ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V) ↔ α = γ := by
  constructor
  · intro h
    by_contra hαγ
    exact no_finite_polynomial_closure_energy α γ β hβ hαγ h
  · rintro rfl
    obtain ⟨V, hfin, _, henergy, hV⟩ := energy_has_finite_polynomial_closure α β
    exact ⟨V, hfin, henergy, hV⟩

end TwoModeBurgers
