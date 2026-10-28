/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.MvPolynomial.Derivation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The two-mode Burgers polynomial vector field

The model has coordinates `a` and `b` with equations
`a' = -α a + β a b` and `b' = -γ b - β a²`. Here `MvPolynomial.X 0`
represents `a` and `MvPolynomial.X 1` represents `b`. The Lie derivative
is `MvPolynomial.mkDerivation ℝ (vectorField α γ β)`.

## Main definitions

* `TwoModeBurgers.vectorField`: the quadratic vector field.
* `TwoModeBurgers.energy`: the Euclidean energy observable.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

/-- The polynomial right-hand side of the two-mode system. -/
def vectorField (α γ β : ℝ) : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  ![C (-α) * X 0 + C β * X 0 * X 1,
    C (-γ) * X 1 + C (-β) * X 0 ^ 2]

/-- Half the sum of the squares of the state coordinates. -/
def energy : MvPolynomial (Fin 2) ℝ := C (1 / 2 : ℝ) * (X 0 ^ 2 + X 1 ^ 2)

private lemma half_mul_two : (C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) * 2 = 1 := by
  simpa only [map_mul, map_one, map_ofNat] using
    congrArg (fun x : ℝ ↦ (C x : MvPolynomial (Fin 2) ℝ)) (show (1 / 2 : ℝ) * 2 = 1 by norm_num)

/-- The nonlinear terms cancel from the Lie derivative of energy. -/
theorem lieDerivation_energy (α γ β : ℝ) :
    (mkDerivation ℝ (vectorField α γ β)) energy =
      -C α * X 0 ^ 2 - C γ * X 1 ^ 2 := by
  simp only [energy, one_div, Derivation.leibniz, map_add, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, mkDerivation_X, vectorField,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, neg_mul, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, derivation_C,
    mul_zero, add_zero]
  calc
    _ = -((C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) * 2) * C α * X 0 ^ 2 -
        ((C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) * 2) * C γ * X 1 ^ 2 := by ring_nf
    _ = _ := by rw [half_mul_two]; ring

/-- Equal damping rates give an exact one-dimensional energy closure. -/
theorem lieDerivation_energy_of_equal_damping (α β : ℝ) :
    (mkDerivation ℝ (vectorField α α β)) energy = -C (2 * α) * energy := by
  rw [lieDerivation_energy]
  simp only [energy, map_mul, map_ofNat]
  calc
    _ = -((C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) * 2) * C α * X 0 ^ 2 -
        ((C (1 / 2 : ℝ) : MvPolynomial (Fin 2) ℝ) * 2) * C α * X 1 ^ 2 := by
          rw [half_mul_two]
          ring
    _ = _ := by ring

/-- Both components of the vector field have total degree at most two. -/
lemma vectorField_totalDegree_le_two (α γ β : ℝ) (i : Fin 2) :
    (vectorField α γ β i).totalDegree ≤ 2 := by
  fin_cases i
  · calc
      _ ≤ max (C (-α) * X (0 : Fin 2)).totalDegree
          (C β * X (0 : Fin 2) * X (1 : Fin 2)).totalDegree :=
        totalDegree_add _ _
      _ ≤ 2 := by
        have h₁ := totalDegree_mul (C (-α)) (X (0 : Fin 2))
        have h₂ := totalDegree_mul (C β * X (0 : Fin 2)) (X (1 : Fin 2))
        have h₃ := totalDegree_mul (C β) (X (0 : Fin 2))
        simp only [totalDegree_X, totalDegree_C] at h₁ h₂ h₃
        lia
  · calc
      _ ≤ max (C (-γ) * X (1 : Fin 2)).totalDegree
          (C (-β) * X (0 : Fin 2) ^ 2).totalDegree :=
        totalDegree_add _ _
      _ ≤ 2 := by
        have h₁ := totalDegree_mul (C (-γ)) (X (1 : Fin 2))
        have h₂ := totalDegree_mul (C (-β)) ((X (0 : Fin 2)) ^ 2)
        have h₃ := totalDegree_pow (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) 2
        simp only [totalDegree_X, totalDegree_C] at h₁ h₂ h₃
        lia

/-- One Lie derivative raises total degree by at most one. -/
theorem lieDerivation_totalDegree_le (α γ β : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    ((mkDerivation ℝ (vectorField α γ β)) p).totalDegree ≤ p.totalDegree + 1 := by
  simpa using
    totalDegree_mkDerivation_le (vectorField α γ β) 2
      (vectorField_totalDegree_le_two α γ β) p

/-- Each Lie derivative increases the total degree by at most one. -/
theorem lieIterate_totalDegree_le (α γ β : ℝ) (n : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n]) (p)).totalDegree ≤ p.totalDegree + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := lieDerivation_totalDegree_le α γ β (((mkDerivation ℝ (vectorField α γ β))^[n]) (p))
    lia

/-- Both coordinate iterates have degree at most `n + 1`. -/
theorem lieIterate_coordinate_totalDegree_le (α γ β : ℝ) (n : ℕ) :
    (((mkDerivation ℝ (vectorField α γ β))^[n])
      (X 0 : MvPolynomial (Fin 2) ℝ)).totalDegree ≤ n + 1 ∧
      (((mkDerivation ℝ (vectorField α γ β))^[n])
        (X 1 : MvPolynomial (Fin 2) ℝ)).totalDegree ≤ n + 1 := by
  have ha := lieIterate_totalDegree_le α γ β n (X 0 : MvPolynomial (Fin 2) ℝ)
  have hb := lieIterate_totalDegree_le α γ β n (X 1 : MvPolynomial (Fin 2) ℝ)
  simpa [totalDegree_X, Nat.add_comm] using And.intro ha hb

end TwoModeBurgers
