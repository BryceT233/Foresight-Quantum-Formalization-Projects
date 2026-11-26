/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.RingTheory.MvPolynomial.DerivationCompression
public import FQFP.Analysis.Calculus.Deriv.MvPolynomialTrunc
public import FQFP.Algebra.MvPolynomial.Eval
public import FQFP.Analysis.ODE.Linear

/-! # Carleman approximants, state recovery, and the error equation -/

@[expose] public noncomputable section
namespace MvPolynomial
variable {σ : Type*} [Finite σ]

/-- The lifted approximation retaining degrees `0, …, N`. -/
def carlemanLiftedApproximant (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) :
    ℝ → Module.Dual ℝ (truncTotal σ ℝ (N + 1)).range :=
  Classical.choose
    ((compressedDerivation (mkDerivation ℝ F) (N + 1)).existsUnique_dualTrajectory
      ((aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype)).exists

lemma carlemanLiftedApproximant_spec
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) :
    carlemanLiftedApproximant F x₀ N 0 =
        (aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype ∧
      ∀ t p, HasDerivAt (fun s => carlemanLiftedApproximant F x₀ N s p)
        ((compressedDerivation (mkDerivation ℝ F) (N + 1)).dualMap
          (carlemanLiftedApproximant F x₀ N t) p) t :=
  Classical.choose_spec
    ((compressedDerivation (mkDerivation ℝ F) (N + 1)).existsUnique_dualTrajectory
      ((aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype)).exists

lemma carlemanLiftedApproximant_initial
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) :
    carlemanLiftedApproximant F x₀ N 0 =
      (aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype :=
  (carlemanLiftedApproximant_spec F x₀ N).1

lemma carlemanLiftedApproximant_hasDerivAt
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) (t : ℝ)
    (p : (truncTotal σ ℝ (N + 1)).range) :
    HasDerivAt (fun s => carlemanLiftedApproximant F x₀ N s p)
      ((compressedDerivation (mkDerivation ℝ F) (N + 1)).dualMap
        (carlemanLiftedApproximant F x₀ N t) p) t :=
  (carlemanLiftedApproximant_spec F x₀ N).2 t p

/-- Differentiate a projected observable by truncating before and after applying the derivation. -/
lemma carlemanLiftedApproximant_hasDerivAt_rangeRestrict
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) (t : ℝ) (p : MvPolynomial σ ℝ) :
    HasDerivAt (fun s => carlemanLiftedApproximant F x₀ N s
      ((truncTotal σ ℝ (N + 1)).rangeRestrict p))
      (carlemanLiftedApproximant F x₀ N t
        ((truncTotal σ ℝ (N + 1)).rangeRestrict
          (mkDerivation ℝ F (truncTotal σ ℝ (N + 1) p)))) t := by
  simpa only [LinearMap.dualMap_apply, compressedDerivation_rangeRestrict] using
    carlemanLiftedApproximant_hasDerivAt F x₀ N t ((truncTotal σ ℝ (N + 1)).rangeRestrict p)

lemma eq_carlemanLiftedApproximant
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ)
    (Y : ℝ → Module.Dual ℝ (truncTotal σ ℝ (N + 1)).range)
    (hinit : Y 0 = (aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype)
    (hode : ∀ t p, HasDerivAt (fun s => Y s p)
      ((compressedDerivation (mkDerivation ℝ F) (N + 1)).dualMap (Y t) p) t) :
    Y = carlemanLiftedApproximant F x₀ N :=
  ((compressedDerivation (mkDerivation ℝ F) (N + 1)).existsUnique_dualTrajectory
    ((aeval x₀).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype)).unique
      ⟨hinit, hode⟩ (carlemanLiftedApproximant_spec F x₀ N)

lemma carlemanLiftedApproximant_one
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) (t : ℝ) :
    carlemanLiftedApproximant F x₀ N t
      ((truncTotal σ ℝ (N + 1)).rangeRestrict 1) = 1 := by
  have htrunc : truncTotal σ ℝ (N + 1) 1 = 1 :=
    (truncTotal_eq_self_iff (N + 1) (by lia) 1).mpr (by simp)
  have hderiv (s : ℝ) : HasDerivAt
      (fun t => carlemanLiftedApproximant F x₀ N t
        ((truncTotal σ ℝ (N + 1)).rangeRestrict 1)) 0 s := by
    simpa only [htrunc, Derivation.map_one_eq_zero, map_zero] using
      carlemanLiftedApproximant_hasDerivAt_rangeRestrict F x₀ N s 1
  calc
    _ = carlemanLiftedApproximant F x₀ N 0
        ((truncTotal σ ℝ (N + 1)).rangeRestrict 1) :=
      is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
        (fun s => (hderiv s).deriv) t 0
    _ = 1 := by simp [carlemanLiftedApproximant_initial, htrunc]

/-- Recover the state by reading the projected linear observables. -/
def carlemanApproximant (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) :
    ℝ → σ → ℝ :=
  fun t i => carlemanLiftedApproximant F x₀ N t
    ((truncTotal σ ℝ (N + 1)).rangeRestrict (X i))

lemma carlemanApproximant_initial
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    carlemanApproximant F x₀ N 0 = x₀ := by
  funext i
  simp [carlemanApproximant, carlemanLiftedApproximant_initial,
    truncTotal_X (N + 1) (by lia)]

lemma carlemanApproximant_zero_order
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (t : ℝ) :
    carlemanApproximant F x₀ 0 t = 0 := by
  funext i
  have hp := truncTotal_rangeRestrict_eq_zero_of_isHomogeneous 1 (isHomogeneous_X ℝ i) le_rfl
  simp only [carlemanApproximant, hp, map_zero, Pi.zero_apply]

lemma carlemanApproximant_hasDerivAt
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (i : σ) :
    HasDerivAt (fun s => carlemanApproximant F x₀ N s i)
      (carlemanLiftedApproximant F x₀ N t
        ((truncTotal σ ℝ (N + 1)).rangeRestrict (F i))) t := by
  simpa only [carlemanApproximant, truncTotal_X (N + 1) (by lia), mkDerivation_X] using
    carlemanLiftedApproximant_hasDerivAt_rangeRestrict F x₀ N t (X i)

lemma hasDerivAt_aeval_sub_carlemanLiftedApproximant
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (N : ℕ) (p : (truncTotal σ ℝ (N + 1)).range) :
    let D := mkDerivation ℝ F
    let E := (aeval (x t)).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype -
      carlemanLiftedApproximant F x₀ N t
    HasDerivAt
      (fun s => aeval (x s) (p : MvPolynomial σ ℝ) - carlemanLiftedApproximant F x₀ N s p)
      ((compressedDerivation D (N + 1)).dualMap E p +
        aeval (x t) (D p - truncTotal σ ℝ (N + 1) (D p))) t := by
  refine ((hasDerivAt_aeval_compressed_with_residual F x t hx (N + 1) p).sub
    (carlemanLiftedApproximant_hasDerivAt F x₀ N t p)).congr_deriv ?_
  simp only [map_sub, LinearMap.sub_apply, add_sub_right_comm]

lemma carlemanLiftedApproximant_error_initial
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (hx₀ : x 0 = x₀) (N : ℕ) :
    (aeval (x 0)).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype -
      carlemanLiftedApproximant F x₀ N 0 = 0 := by
  rw [hx₀, carlemanLiftedApproximant_initial, sub_self]

lemma carlemanApproximant_error_eq
    (F : σ → MvPolynomial σ ℝ) (x₀ x : σ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (i : σ) :
    x i - carlemanApproximant F x₀ N t i =
      ((aeval x).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype -
        carlemanLiftedApproximant F x₀ N t)
        ((truncTotal σ ℝ (N + 1)).rangeRestrict (X i)) := by
  simp [carlemanApproximant, truncTotal_X (N + 1) (by lia)]

lemma carlemanLiftedApproximant_eq_aeval_of_invariant_range
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (hx₀ : x 0 = x₀)
    (hx : ∀ t i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (N : ℕ)
    (hinv : ∀ p ∈ (truncTotal σ ℝ (N + 1)).range,
      mkDerivation ℝ F p ∈ (truncTotal σ ℝ (N + 1)).range) :
    carlemanLiftedApproximant F x₀ N =
      fun t => (aeval (x t)).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype := by
  symm
  apply eq_carlemanLiftedApproximant
  · rw [hx₀]
  · intro t p
    refine (hasDerivAt_aeval_compressed_with_residual F x t (hx t) (N + 1) p).congr_deriv ?_
    rw [truncTotal_eq_self_of_mem_range _ (hinv p p.property), sub_self, map_zero, add_zero]

/-- Every positive-order approximant is exact for an affine vector field. -/
lemma carlemanApproximant_eq_of_totalDegree_le_one
    (F : σ → MvPolynomial σ ℝ) (hF : ∀ i, (F i).totalDegree ≤ 1)
    (x₀ : σ → ℝ) (x : ℝ → σ → ℝ) (hx₀ : x 0 = x₀)
    (hx : ∀ t i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (N : ℕ) (hN : 1 ≤ N) : carlemanApproximant F x₀ N = x := by
  have heq := carlemanLiftedApproximant_eq_aeval_of_invariant_range F x₀ x hx₀ hx N
    (fun p hp => mkDerivation_mem_range_truncTotal_of_totalDegree_le_one F hF (N + 1) hp)
  funext t i
  simp [carlemanApproximant, heq, truncTotal_X (N + 1) (by lia)]

lemma translated_carlemanApproximant_initial
    (F : σ → MvPolynomial σ ℝ) (x₀ q : σ → ℝ) (N : ℕ) (hN : 1 ≤ N) (i : σ) :
    q i + carlemanApproximant
      (fun j => aeval (fun k => C (q k) + X k) (F j))
      (fun j => x₀ j - q j) N 0 i = x₀ i := by
  rw [carlemanApproximant_initial _ _ N hN]
  exact add_sub_cancel _ _

end MvPolynomial
