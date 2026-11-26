/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Carleman.TwoModeBurgers.EnergyLeading
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# Polynomial functions of the energy

The paper studies the Krylov closure of `P(E)` for every one-variable real
polynomial `P`. Here `Polynomial.aeval energy P` represents that observable;
the coordinate polynomial ring and its derivation use Mathlib's APIs directly.
The hypothesis `0 < P.natDegree` is exactly the paper's nonconstant condition.

## Main results

* `coefficient_lieIterate_polynomial_energy` gives a nonzero leading
  coefficient for every nonconstant `P` under anisotropic damping.
* `polynomial_energy_krylov_finite` and `polynomial_energy_krylov_infinite`
  state the paper's finite/infinite Krylov dichotomy directly.
* `polynomial_energy_finite_closure_iff` gives the finite-closure dichotomy.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

/-- In the equal-damping case, each energy power is a Lie-derivative eigenvector. -/
lemma lieDerivation_energy_pow (α β : ℝ) (k : ℕ) :
    (mkDerivation ℝ (vectorField α α β)) (energy ^ k) =
      C (-(2 * α * (k : ℝ))) * energy ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Derivation.leibniz, ih, lieDerivation_energy_of_equal_damping]
    simp only [smul_eq_mul, map_neg, map_mul, map_ofNat, map_natCast,
      map_add, map_one, Nat.cast_add, Nat.cast_one]
    ring

/-- Every polynomial function of energy has finite polynomial closure at equal damping. -/
theorem polynomial_energy_has_finite_closure (α β : ℝ) (P : Polynomial ℝ) :
    ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ Polynomial.aeval energy P ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α α β)) p ∈ V := by
  let s : Finset (MvPolynomial (Fin 2) ℝ) :=
    (Finset.range (P.natDegree + 1)).image (energy ^ ·)
  let V := Submodule.span ℝ (s : Set (MvPolynomial (Fin 2) ℝ))
  have hpow {k : ℕ} (hk : k ≤ P.natDegree) : energy ^ k ∈ V := by
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by lia), rfl⟩
  have hP : Polynomial.aeval energy P ∈ V := by
    rw [Polynomial.aeval_eq_sum_range]
    apply Submodule.sum_mem
    intro k hk
    exact V.smul_mem _ (hpow (by simpa using hk))
  have hV : ∀ p ∈ V, (mkDerivation ℝ (vectorField α α β)) p ∈ V := by
    intro p hp
    have hspan : V ≤ V.comap (mkDerivation ℝ (vectorField α α β)).toLinearMap := by
      apply Submodule.span_le.mpr
      intro q hq
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
      change (mkDerivation ℝ (vectorField α α β)) (energy ^ k) ∈ V
      rw [lieDerivation_energy_pow]
      simpa only [Algebra.smul_def, C_eq_algebraMap] using
        V.smul_mem (-(2 * α * (k : ℝ)))
          (Submodule.subset_span (Finset.mem_coe.mpr hq))
    exact hspan hp
  exact ⟨V, inferInstance, hP, hV⟩

private lemma energy_pow_pure_coefficient (r : ℕ) :
    (energy ^ r).coeff
        (Finsupp.single 0 0 + Finsupp.single 1 (2 * r)) =
          (1 / 2 : ℝ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : energy ^ (r + 1) =
        C (1 / 2 : ℝ) * X 0 ^ 2 * energy ^ r +
          C (1 / 2 : ℝ) * X 1 ^ 2 * energy ^ r := by
      rw [pow_succ, energy]
      ring
    rw [hp]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_assoc, coeff_C_mul]
    rw [show 2 * (r + 1) = 2 * r + 2 by lia, coeff_first_pow_mul, coeff_second_pow_mul,
      ite_eq_right (by decide : ¬ 2 ≤ 0), ite_eq_left (by lia : 2 ≤ 2 * r + 2),
      Nat.add_sub_cancel, ih]
    simp [pow_succ']

private lemma energy_totalDegree_le_two : energy.totalDegree ≤ 2 := by
  have hmul := totalDegree_mul (C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ)
    ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + X 1 ^ 2)
  have hadd := totalDegree_add ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) (X 1 ^ 2)
  have hzero := totalDegree_pow (X 0 : MvPolynomial (Fin 2) ℝ) 2
  have hone := totalDegree_pow (X 1 : MvPolynomial (Fin 2) ℝ) 2
  simp only [totalDegree_C, totalDegree_X] at hmul hzero hone
  change (C (1 / 2 : ℝ) * (X 0 ^ 2 + X 1 ^ 2) :
    MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2
  lia

private lemma energy_pow_totalDegree_le (k : ℕ) : (energy ^ k).totalDegree ≤ 2 * k := by
  calc
    (energy ^ k).totalDegree ≤ k * energy.totalDegree := totalDegree_pow energy k
    _ ≤ 2 * k := by
      simpa [mul_comm] using Nat.mul_le_mul_left k energy_totalDegree_le_two

private lemma polynomial_energy_top_coefficient (P : Polynomial ℝ)
    (e : Fin 2 →₀ ℕ) (he : e.degree = 2 * P.natDegree) :
    (Polynomial.aeval energy P).coeff e =
      P.coeff P.natDegree * (energy ^ P.natDegree).coeff e := by
  rw [Polynomial.aeval_eq_sum_range, coeff_sum]
  simp only [coeff_smul]
  rw [Finset.sum_eq_single P.natDegree]
  · rfl
  · intro k hk hne
    have hklt : k < P.natDegree := by
      have := Finset.mem_range.mp hk
      lia
    have hzero : (energy ^ k).coeff e = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by
        have hd := energy_pow_totalDegree_le k
        change (energy ^ k).totalDegree < e.degree
        rw [he]
        lia)
    simp [hzero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by lia))).elim

private lemma polynomial_energy_pure_top_coefficient (P : Polynomial ℝ) :
    (Polynomial.aeval energy P).coeff
        (Finsupp.single 0 0 + Finsupp.single 1 (2 * P.natDegree)) =
          P.coeff P.natDegree * (1 / 2 : ℝ) ^ P.natDegree := by
  rw [polynomial_energy_top_coefficient P _ (by simp),
    energy_pow_pure_coefficient]

private lemma polynomial_energy_totalDegree_le (P : Polynomial ℝ) :
    (Polynomial.aeval energy P).totalDegree ≤ 2 * P.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro k hk
  have hsmul := totalDegree_smul_le (P.coeff k) (energy ^ k)
  have hpow := energy_pow_totalDegree_le k
  have hk' : k ≤ P.natDegree := by
    have := Finset.mem_range.mp hk
    lia
  lia

private lemma lieDerivation_polynomial_energy_totalDegree_le (α γ β : ℝ)
    (P : Polynomial ℝ) :
    ((mkDerivation ℝ (vectorField α γ β))
      (Polynomial.aeval energy P)).totalDegree ≤ 2 * P.natDegree := by
  by_cases hr : 0 < P.natDegree
  · rw [Derivation.comp_aeval_eq]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
    have hmul := totalDegree_mul (Polynomial.aeval energy P.derivative)
      ((mkDerivation ℝ (vectorField α γ β)) energy)
    have hpoly := polynomial_energy_totalDegree_le P.derivative
    have hder := Polynomial.natDegree_derivative_le P
    have henergy := lieDerivation_energy_totalDegree_le_two α γ β
    lia
  · have hzero : P.natDegree = 0 := by lia
    rw [Polynomial.eq_C_of_natDegree_eq_zero hzero]
    simp

private lemma lieDerivation_second_energy (α γ β : ℝ) :
    (mkDerivation ℝ (vectorField α γ β))
        ((mkDerivation ℝ (vectorField α γ β)) energy) =
      C (2 * α ^ 2) * X 0 ^ 2 + C (2 * γ ^ 2) * X 1 ^ 2 +
        C (2 * β * (γ - α)) * X 0 ^ 2 * X 1 := by
  rw [lieDerivation_energy]
  simp only [map_sub, Derivation.leibniz, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, mkDerivation_X, vectorField,
    Matrix.cons_val_zero, Matrix.cons_val_one, derivation_C,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, map_neg,
    mul_zero]
  simp only [map_mul, map_pow, map_sub, map_ofNat]
  ring

private lemma lieIterate_two_polynomial_energy (α γ β : ℝ) (P : Polynomial ℝ) :
    (((mkDerivation ℝ (vectorField α γ β))^[2])
      (Polynomial.aeval energy P)) =
      (mkDerivation ℝ (vectorField α γ β))
          (Polynomial.aeval energy P.derivative) *
        (mkDerivation ℝ (vectorField α γ β)) energy +
      Polynomial.aeval energy P.derivative *
        (mkDerivation ℝ (vectorField α γ β))
          ((mkDerivation ℝ (vectorField α γ β)) energy) := by
  change (mkDerivation ℝ (vectorField α γ β))
    ((mkDerivation ℝ (vectorField α γ β)) (Polynomial.aeval energy P)) = _
  rw [Derivation.comp_aeval_eq]
  simp only [Algebra.smul_def, Algebra.algebraMap_self_apply,
    Derivation.leibniz]
  ring

private lemma coeff_mul_second_energy (α γ β : ℝ)
    (q : MvPolynomial (Fin 2) ℝ) (j : ℕ) (hq : q.totalDegree ≤ j) :
    (q * ((mkDerivation ℝ (vectorField α γ β))
      ((mkDerivation ℝ (vectorField α γ β)) energy))).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (j + 1)) =
      2 * β * (γ - α) * q.coeff
        (Finsupp.single 0 0 + Finsupp.single 1 j) := by
  have hquad (c : ℝ) (i : Fin 2) :
      (q * (C c * X i ^ 2)).totalDegree ≤ j + 2 := by
    have h₁ := totalDegree_mul q (C c * X i ^ 2)
    have h₂ := totalDegree_mul (C c : MvPolynomial (Fin 2) ℝ) (X i ^ 2)
    have h₃ := totalDegree_pow (X i : MvPolynomial (Fin 2) ℝ) 2
    simp only [totalDegree_C, totalDegree_X] at h₂ h₃
    lia
  have hzero (c : ℝ) (i : Fin 2) :
      (q * (C c * X i ^ 2)).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (j + 1)) = 0 :=
    coefficient_eq_zero_of_totalDegree_lt _ 2 (j + 1) (by
      have h := hquad c i
      lia)
  rw [lieDerivation_second_energy, mul_add, mul_add]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hzero,
    zero_add]
  have hcubic : q * (C (2 * β * (γ - α)) * X 0 ^ 2 * X 1) =
      C (2 * β * (γ - α)) * (X 0 ^ 2 * X 1 ^ 1 * q) := by ring
  rw [hcubic, coeff_C_mul, coeff_pow_mul_pow_mul]
  simp

private lemma coefficient_lieIterate_polynomial_energy_two (α γ β : ℝ)
    (P : Polynomial ℝ) (hr : 0 < P.natDegree) :
    (((mkDerivation ℝ (vectorField α γ β))^[2])
      (Polynomial.aeval energy P)).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (2 * P.natDegree - 1)) =
      2 * β * (γ - α) * (P.natDegree : ℝ) * P.coeff P.natDegree *
        (1 / 2 : ℝ) ^ (P.natDegree - 1) := by
  have hderdeg : P.derivative.natDegree = P.natDegree - 1 :=
    Polynomial.natDegree_derivative P
  have hQdegree : (Polynomial.aeval energy P.derivative).totalDegree ≤
      2 * (P.natDegree - 1) := by
    rw [← hderdeg]
    exact polynomial_energy_totalDegree_le P.derivative
  have hfirstdegree :
      ((mkDerivation ℝ (vectorField α γ β))
          (Polynomial.aeval energy P.derivative) *
        (mkDerivation ℝ (vectorField α γ β)) energy).totalDegree ≤
          2 * P.natDegree := by
    have hmul := totalDegree_mul
      ((mkDerivation ℝ (vectorField α γ β))
        (Polynomial.aeval energy P.derivative))
      ((mkDerivation ℝ (vectorField α γ β)) energy)
    have hq := lieDerivation_polynomial_energy_totalDegree_le α γ β P.derivative
    have he := lieDerivation_energy_totalDegree_le_two α γ β
    rw [hderdeg] at hq
    lia
  have hfirstzero :
      ((mkDerivation ℝ (vectorField α γ β))
          (Polynomial.aeval energy P.derivative) *
        (mkDerivation ℝ (vectorField α γ β)) energy).coeff
          (Finsupp.single 0 2 + Finsupp.single 1 (2 * P.natDegree - 1)) = 0 :=
    coefficient_eq_zero_of_totalDegree_lt _ 2 (2 * P.natDegree - 1) (by
      lia)
  have hQcoeff : (Polynomial.aeval energy P.derivative).coeff
      (Finsupp.single 0 0 + Finsupp.single 1 (2 * (P.natDegree - 1))) =
        (P.natDegree : ℝ) * P.coeff P.natDegree *
          (1 / 2 : ℝ) ^ (P.natDegree - 1) := by
    have htop := polynomial_energy_pure_top_coefficient P.derivative
    rw [hderdeg] at htop
    rw [htop, Polynomial.coeff_derivative,
      show P.natDegree - 1 + 1 = P.natDegree by lia]
    have hcast : ((P.natDegree - 1 : ℕ) : ℝ) + 1 = (P.natDegree : ℝ) := by
      exact_mod_cast (show P.natDegree - 1 + 1 = P.natDegree by lia)
    conv_rhs => rw [← hcast]
    ring
  rw [lieIterate_two_polynomial_energy, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, hfirstzero]
  rw [show 2 * P.natDegree - 1 = 2 * (P.natDegree - 1) + 1 by lia,
    coeff_mul_second_energy α γ β _ _ hQdegree, hQcoeff]
  ring

private lemma polynomial_energy_iterate_totalDegree_le (α γ β : ℝ)
    (P : Polynomial ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 1])
      (Polynomial.aeval energy P)).totalDegree ≤ 2 * P.natDegree + n := by
  rw [Function.iterate_succ_apply]
  exact (lieIterate_totalDegree_le α γ β n _).trans
    (Nat.add_le_add_right (lieDerivation_polynomial_energy_totalDegree_le α γ β P) n)

/-- The highest `a²b^j` coefficient in every later iterate of `P(E)`. -/
theorem coefficient_lieIterate_polynomial_energy (α γ β : ℝ)
    (P : Polynomial ℝ) (hr : 0 < P.natDegree) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 2])
      (Polynomial.aeval energy P)).coeff
        (Finsupp.single 0 2 + Finsupp.single 1 (2 * P.natDegree + n - 1)) =
      (2 * β) ^ n *
        (2 * β * (γ - α) * (P.natDegree : ℝ) * P.coeff P.natDegree *
          (1 / 2 : ℝ) ^ (P.natDegree - 1)) := by
  have hdeg := lieDerivation_polynomial_energy_totalDegree_le α γ β P
  have hindex : 2 * P.natDegree - 1 + n = 2 * P.natDegree + n - 1 := by lia
  calc
    _ = (2 * β) ^ n * (((mkDerivation ℝ (vectorField α γ β))^[2]) (Polynomial.aeval energy P)).coeff
          (Finsupp.single 0 2 + Finsupp.single 1 (2 * P.natDegree - 1)) := by
      rw [Function.iterate_succ_apply _ (n + 1), Function.iterate_succ_apply _ 1,
        Function.iterate_one]
      simpa only [hindex] using coefficient_two_lieIterate_of_totalDegree_le α γ β n
        (2 * P.natDegree - 1) ((mkDerivation ℝ (vectorField α γ β)) (Polynomial.aeval energy P))
        (by lia)
    _ = _ := by rw [coefficient_lieIterate_polynomial_energy_two α γ β P hr]

/-- For nonzero coupling and unequal damping, the later iterates of a
nonconstant polynomial in energy have strictly increasing degrees. -/
theorem lieIterate_polynomial_energy_totalDegree (α γ β : ℝ)
    (hβ : β ≠ 0) (hαγ : α ≠ γ) (P : Polynomial ℝ)
    (hr : 0 < P.natDegree) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n + 2])
      (Polynomial.aeval energy P)).totalDegree =
        2 * P.natDegree + n + 1 := by
  have hP : P ≠ 0 := by
    intro h
    simp [h] at hr
  have hlead : P.coeff P.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hcoeff :
      (((mkDerivation ℝ (vectorField α γ β))^[n + 2])
        (Polynomial.aeval energy P)).coeff
          (Finsupp.single 0 2 + Finsupp.single 1
            (2 * P.natDegree + n - 1)) ≠ 0 := by
    rw [coefficient_lieIterate_polynomial_energy α γ β P hr n]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) hβ)) ?_
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (mul_ne_zero (by norm_num) hβ)
            (sub_ne_zero.mpr (Ne.symm hαγ))
        · exact_mod_cast (Nat.ne_of_gt hr)
      · exact hlead
    · exact pow_ne_zero _ (by norm_num)
  have hlow := add_le_totalDegree_of_coeff_ne_zero hcoeff
  have hhigh := polynomial_energy_iterate_totalDegree_le α γ β P (n + 1)
  lia

/-- Nonconstant `P(E)` has no finite invariant polynomial closure when the
damping rates differ and the coupling is nonzero. -/
theorem no_finite_polynomial_closure_polynomial_energy (α γ β : ℝ)
    (hβ : β ≠ 0) (hαγ : α ≠ γ) (P : Polynomial ℝ)
    (hr : 0 < P.natDegree) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ Polynomial.aeval energy P ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  apply no_finite_polynomial_closure_of_unbounded_totalDegree
  intro N
  refine ⟨N + 2, ?_⟩
  rw [lieIterate_polynomial_energy_totalDegree α γ β hβ hαγ P hr]
  lia

/-- Every polynomial of energy has a finite-dimensional Krylov space at equal damping. -/
theorem polynomial_energy_krylov_finite (α β : ℝ) (P : Polynomial ℝ) :
    FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range (fun n : ℕ =>
        ((mkDerivation ℝ (vectorField α α β))^[n])
          (Polynomial.aeval energy P)))) :=
  (finiteDimensional_span_lieIterate_iff _ _ _ _).2 (polynomial_energy_has_finite_closure α β P)

/-- The polynomial Krylov space of a nonconstant `P(E)` is infinite-dimensional
under anisotropic damping and nonzero coupling. -/
theorem polynomial_energy_krylov_infinite (α γ β : ℝ)
    (hβ : β ≠ 0) (hαγ : α ≠ γ) (P : Polynomial ℝ)
    (hr : 0 < P.natDegree) :
    ¬ FiniteDimensional ℝ
      (Submodule.span ℝ (Set.range (fun n : ℕ =>
        ((mkDerivation ℝ (vectorField α γ β))^[n])
          (Polynomial.aeval energy P)))) :=
  fun h ↦ no_finite_polynomial_closure_polynomial_energy α γ β hβ hαγ P hr
    ((finiteDimensional_span_lieIterate_iff _ _ _ _).1 h)

/-- A nonconstant polynomial of energy has finite polynomial closure exactly
when the damping rates agree, under nonzero coupling. -/
theorem polynomial_energy_finite_closure_iff (α γ β : ℝ)
    (hβ : β ≠ 0) (P : Polynomial ℝ) (hr : 0 < P.natDegree) :
    (∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ Polynomial.aeval energy P ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V) ↔ α = γ := by
  constructor
  · intro h
    by_contra hαγ
    exact no_finite_polynomial_closure_polynomial_energy α γ β hβ hαγ P hr h
  · rintro rfl
    exact polynomial_energy_has_finite_closure α β P

end TwoModeBurgers
