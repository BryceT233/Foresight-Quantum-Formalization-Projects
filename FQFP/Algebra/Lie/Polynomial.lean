/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Polynomial.Module.Degree
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Convolution brackets on Lie-valued polynomials

The bilinear convolution bracket commutes with evaluation and Lie homomorphisms.
Its finite-support formula shows that the bracket adds coefficientwise degree bounds.

## Main results

* `PolynomialModule.eval_lieBracket`: evaluation preserves the bracket.
* `PolynomialModule.map_lieBracket`: Lie homomorphisms preserve the bracket.
* `PolynomialModule.DegreeLE.lieBracket`: the bracket adds degree bounds.
-/

@[expose] public noncomputable section

namespace PolynomialModule

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

/-- The bilinear convolution bracket of Lie polynomials. -/
def lieBracket : PolynomialModule ℚ L →ₗ[ℚ]
    PolynomialModule ℚ L →ₗ[ℚ] PolynomialModule ℚ L :=
  lift fun i ↦
    ({ toFun := fun x ↦ lift fun j ↦ (lsingle ℚ (i + j)).comp (LieAlgebra.ad ℚ L x)
       map_add' := by
        intro x y
        apply LinearMap.ext
        intro p
        induction p using induction_linear with
        | zero => simp
        | add p q hp hq =>
          simp only [LinearMap.map_add, LinearMap.add_apply] at hp hq ⊢
          rw [hp, hq]
        | single j z => simp
       map_smul' := by
        intro r x
        apply LinearMap.ext
        intro p
        induction p using induction_linear with
        | zero => simp
        | add p q hp hq =>
          simp only [LinearMap.map_add, LinearMap.smul_apply] at hp hq ⊢
          rw [hp, hq]
        | single j z => simp } :
      L →ₗ[ℚ] PolynomialModule ℚ L →ₗ[ℚ] PolynomialModule ℚ L)

@[simp]
theorem lieBracket_single (i j : ℕ) (x y : L) :
    lieBracket (single ℚ i x) (single ℚ j y) = single ℚ (i + j) ⁅x, y⁆ := by
  simp [lieBracket, lsingle]

/-- Evaluation preserves the convolution bracket. -/
theorem eval_lieBracket (r : ℚ) (p q : PolynomialModule ℚ L) :
    eval r (lieBracket p q) = ⁅eval r p, eval r q⁆ := by
  induction p using induction_linear with
  | zero => simp
  | add p p' hp hp' => simp [hp, hp', add_lie]
  | single i x =>
    induction q using induction_linear with
    | zero => simp
    | add q q' hq hq' => simp [hq, hq', lie_add]
    | single j y => simp [pow_add, smul_lie, lie_smul, smul_smul, mul_comm]

/-- Lie algebra homomorphisms commute with the polynomial convolution bracket. -/
theorem map_lieBracket {L' : Type*} [LieRing L'] [LieAlgebra ℚ L']
    (f : L →ₗ⁅ℚ⁆ L') (p q : PolynomialModule ℚ L) :
    map ℚ f.toLinearMap (lieBracket p q) =
      lieBracket (map ℚ f.toLinearMap p) (map ℚ f.toLinearMap q) := by
  induction p using induction_linear with
  | zero => simp
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']
  | single i x =>
    induction q using induction_linear with
    | zero => simp
    | add q q' hq hq' => simp only [map_add, hq, hq']
    | single j y => simp

/-- Finite support formula for the convolution bracket. -/
theorem lieBracket_eq_sum (p q : PolynomialModule ℚ L) :
    lieBracket p q = p.coeff.sum fun i x ↦ q.coeff.sum fun j y ↦
      single ℚ (i + j) ⁅x, y⁆ := by
  simp only [lieBracket, lift, LinearMap.comp_apply,
    Finsupp.lsum_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

/-- A convolution bracket adds the auxiliary polynomial degree bounds. -/
theorem DegreeLE.lieBracket {p q : PolynomialModule ℚ L} {m n : ℕ}
    (hp : DegreeLE p m) (hq : DegreeLE q n) : DegreeLE (lieBracket p q) (m + n) := by
  rw [lieBracket_eq_sum]
  apply degreeLE_sum
  intro i hi
  apply degreeLE_sum
  intro j hj
  exact degreeLE_single _ (Nat.add_le_add (hp.le_of_mem_support hi) (hq.le_of_mem_support hj))

end PolynomialModule
