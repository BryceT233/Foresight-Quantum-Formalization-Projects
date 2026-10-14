/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.MatrixEvolution
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Norm bounds for forced linear evolution and Carleman truncation errors

The abstract bounds work in any real normed space. The Carleman application
uses the maximum norm on the coordinates of an arbitrary finite observable
basis, so no norm is added to the algebraic definition of the approximant.
Operator and residual bounds are explicit hypotheses of these estimates.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

/-- A convenient zero-initial-data bound, also valid when the growth rate is zero. -/
lemma gronwallBound_zero_le_mul_exp (K ε t : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound 0 K ε t ≤ ε * t * Real.exp (K * t) := by
  by_cases hKzero : K = 0
  · simp [gronwallBound, hKzero]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    rw [gronwallBound_of_K_ne_0 hKzero]
    simp only [zero_mul, zero_add]
    have hexp : Real.exp (K * t) - 1 ≤ (K * t) * Real.exp (K * t) := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(K * t)))
        (Real.exp_nonneg (K * t))
      rw [← Real.exp_add] at h
      simp only [neg_add_cancel, Real.exp_zero] at h
      nlinarith
    calc
      _ ≤ ε / K * ((K * t) * Real.exp (K * t)) :=
        mul_le_mul_of_nonneg_left hexp (div_nonneg hε hK)
      _ = ε * t * Real.exp (K * t) := by field_simp

namespace ContinuousLinearMap
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Grönwall's estimate for a bounded linear generator with additive forcing.
Only right derivatives on the half-open interval and continuity on its closure are needed. -/
lemma norm_le_gronwallBound_of_forced
    (A : V →L[ℝ] V) (E r : ℝ → V) (a b δ K ε : ℝ)
    (hE : ContinuousOn E (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ico a b, HasDerivWithinAt E (A (E s) + r s) (Set.Ici s) s)
    (hinit : ‖E a‖ ≤ δ) (hA : ‖A‖ ≤ K)
    (hr : ∀ s ∈ Set.Ico a b, ‖r s‖ ≤ ε) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖E t‖ ≤ gronwallBound δ K ε (t - a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le hE hode hinit _ t ht
  intro s hs
  calc
    ‖A (E s) + r s‖ ≤ ‖A (E s)‖ + ‖r s‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖E s‖ + ε := add_le_add (A.le_opNorm _) (hr s hs)
    _ ≤ K * ‖E s‖ + ε := add_le_add
      (mul_le_mul_of_nonneg_right hA (norm_nonneg (E s))) le_rfl

/-- A bound without division by the growth rate, for zero initial error. -/
lemma norm_le_mul_exp_of_forced_zero_initial
    (A : V →L[ℝ] V) (E r : ℝ → V) (a b K ε : ℝ)
    (hE : ContinuousOn E (Set.Icc a b))
    (hode : ∀ s ∈ Set.Ico a b, HasDerivWithinAt E (A (E s) + r s) (Set.Ici s) s)
    (hinit : E a = 0) (hA : ‖A‖ ≤ K) (hε : 0 ≤ ε)
    (hr : ∀ s ∈ Set.Ico a b, ‖r s‖ ≤ ε) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖E t‖ ≤ ε * (t - a) * Real.exp (K * (t - a)) := by
  exact (A.norm_le_gronwallBound_of_forced E r a b 0 K ε hE hode
    (by simp [hinit]) hA hr t ht).trans
      (gronwallBound_zero_le_mul_exp K ε (t - a) ((norm_nonneg A).trans hA) hε)

end ContinuousLinearMap

namespace LinearMap
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- Recovering an observable from finite dual coordinates costs its coefficient `ℓ¹` norm. -/
lemma abs_apply_le_sum_abs_repr_mul_norm_coordinates
    (B : Module.Basis ι ℝ E) (ℓ : Module.Dual ℝ E) (p : E) :
    |ℓ p| ≤ (∑ i, |B.repr p i|) * ‖fun i => ℓ (B i)‖ := by
  classical
  calc
    |ℓ p| = |∑ i, B.repr p i * ℓ (B i)| := by
      conv_lhs => rw [← B.sum_repr p]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ ≤ ∑ i, |B.repr p i * ℓ (B i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |B.repr p i| * ‖fun i => ℓ (B i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm (fun i => ℓ (B i)) i)
        (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

end LinearMap

namespace MvPolynomial
variable {σ ι : Type*} [Finite σ] [Fintype ι] [DecidableEq ι]

/-- The existing scalar observable error equation assembled in finite basis coordinates. -/
lemma hasDerivAt_aeval_sub_carlemanLiftedApproximant_coordinates
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (N : ℕ) (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range) :
    let D := mkDerivation ℝ F
    let A := (LinearMap.toMatrix B B (compressedDerivation D (N + 1))).transpose
    let E := fun s i => aeval (x s) (B i : MvPolynomial σ ℝ) -
      carlemanLiftedApproximant F x₀ N s (B i)
    let r := fun s i => aeval (x s)
      (D (B i) - truncTotal σ ℝ (N + 1) (D (B i)))
    HasDerivAt E (A.mulVec (E t) + r t) t := by
  dsimp only
  apply hasDerivAt_pi.mpr
  intro i
  let E := (aeval (x t)).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype -
    carlemanLiftedApproximant F x₀ N t
  have hcoords := LinearMap.dualMap_coordinates B
    (compressedDerivation (mkDerivation ℝ F) (N + 1)) E i
  change HasDerivAt (fun s => aeval (x s) (B i : MvPolynomial σ ℝ) -
    carlemanLiftedApproximant F x₀ N s (B i))
    (((LinearMap.toMatrix B B (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVec
      (fun j => E (B j)) i + aeval (x t)
        (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))) t
  rw [hcoords]
  exact hasDerivAt_aeval_sub_carlemanLiftedApproximant F x₀ x t hx N (B i)

/-- A quantitative lifted error bound in any finite observable basis.
The residual is exactly the evaluation of the discarded high-degree part. -/
lemma norm_aeval_sub_carlemanLiftedApproximant_le_gronwallBound
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (N : ℕ) (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range)
    (a b δ K ε : ℝ)
    (hx : ∀ s ∈ Set.Icc a b, ∀ i, HasDerivAt (fun t => x t i) (aeval (x s) (F i)) s)
    (hinit : ‖fun i => aeval (x a) (B i : MvPolynomial σ ℝ) -
      carlemanLiftedApproximant F x₀ N a (B i)‖ ≤ δ)
    (hK : ‖LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix B B
        (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVecLin‖ ≤ K)
    (hr : ∀ s ∈ Set.Ico a b, ‖fun i => aeval (x s)
      (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))‖ ≤ ε)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖fun i => aeval (x t) (B i : MvPolynomial σ ℝ) -
      carlemanLiftedApproximant F x₀ N t (B i)‖ ≤ gronwallBound δ K ε (t - a) := by
  let E := fun s i => aeval (x s) (B i : MvPolynomial σ ℝ) -
    carlemanLiftedApproximant F x₀ N s (B i)
  let r := fun s i => aeval (x s)
    (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))
  let A := LinearMap.toContinuousLinearMap
    ((LinearMap.toMatrix B B (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVecLin
  have hderiv (s : ℝ) (hs : s ∈ Set.Icc a b) : HasDerivAt E (A (E s) + r s) s :=
    hasDerivAt_aeval_sub_carlemanLiftedApproximant_coordinates F x₀ x s (hx s hs) N B
  apply A.norm_le_gronwallBound_of_forced E r a b δ K ε
    (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt) hinit hK hr t ht

/-- Equal initial states give the convenient bound `ε t exp(Kt)` on `[0,T]`. -/
lemma norm_aeval_sub_carlemanLiftedApproximant_le_mul_exp
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (N : ℕ) (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range)
    (T K ε : ℝ) (hx₀ : x 0 = x₀)
    (hx : ∀ s ∈ Set.Icc 0 T, ∀ i, HasDerivAt (fun t => x t i) (aeval (x s) (F i)) s)
    (hK : ‖LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix B B
        (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVecLin‖ ≤ K)
    (hε : 0 ≤ ε)
    (hr : ∀ s ∈ Set.Ico 0 T, ‖fun i => aeval (x s)
      (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))‖ ≤ ε)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖fun i => aeval (x t) (B i : MvPolynomial σ ℝ) -
      carlemanLiftedApproximant F x₀ N t (B i)‖ ≤ ε * t * Real.exp (K * t) := by
  have hinit : ‖fun i => aeval (x 0) (B i : MvPolynomial σ ℝ) -
      carlemanLiftedApproximant F x₀ N 0 (B i)‖ ≤ 0 := by
    simp [hx₀, carlemanLiftedApproximant_initial]
    rfl
  have hbound := norm_aeval_sub_carlemanLiftedApproximant_le_gronwallBound
    F x₀ x N B 0 T 0 K ε hx hinit hK hr t ht
  simp only [sub_zero] at hbound
  exact hbound.trans (gronwallBound_zero_le_mul_exp K ε t ((norm_nonneg _).trans hK) hε)

/-- State-coordinate recovery in an arbitrary basis, with its explicit coefficient factor. -/
lemma abs_sub_carlemanApproximant_le_mul_exp
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range)
    (T K ε : ℝ) (hx₀ : x 0 = x₀)
    (hx : ∀ s ∈ Set.Icc 0 T, ∀ i, HasDerivAt (fun t => x t i) (aeval (x s) (F i)) s)
    (hK : ‖LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix B B
        (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVecLin‖ ≤ K)
    (hε : 0 ≤ ε)
    (hr : ∀ s ∈ Set.Ico 0 T, ‖fun i => aeval (x s)
      (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))‖ ≤ ε)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : σ) :
    |x t i - carlemanApproximant F x₀ N t i| ≤
      (∑ j, |B.repr ((truncTotal σ ℝ (N + 1)).rangeRestrict (X i)) j|) *
        (ε * t * Real.exp (K * t)) := by
  let ℓ := (aeval (x t)).toLinearMap.comp (truncTotal σ ℝ (N + 1)).range.subtype -
    carlemanLiftedApproximant F x₀ N t
  rw [carlemanApproximant_error_eq F x₀ (x t) N hN t i]
  calc
    _ ≤ (∑ j, |B.repr ((truncTotal σ ℝ (N + 1)).rangeRestrict (X i)) j|) *
        ‖fun j => ℓ (B j)‖ :=
      LinearMap.abs_apply_le_sum_abs_repr_mul_norm_coordinates B ℓ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (norm_aeval_sub_carlemanLiftedApproximant_le_mul_exp F x₀ x N B T K ε
        hx₀ hx hK hε hr t ht) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- If the basis contains all coordinate observables, maximum-norm recovery has constant one. -/
lemma norm_sub_carlemanApproximant_le_mul_exp_of_basis_contains_X [Fintype σ]
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (x : ℝ → σ → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range)
    (κ : σ → ι) (hB : ∀ i, (B (κ i) : MvPolynomial σ ℝ) = X i)
    (T K ε : ℝ) (hx₀ : x 0 = x₀)
    (hx : ∀ s ∈ Set.Icc 0 T, ∀ i, HasDerivAt (fun t => x t i) (aeval (x s) (F i)) s)
    (hK : ‖LinearMap.toContinuousLinearMap
      ((LinearMap.toMatrix B B
        (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose).mulVecLin‖ ≤ K)
    (hε : 0 ≤ ε)
    (hr : ∀ s ∈ Set.Ico 0 T, ‖fun i => aeval (x s)
      (mkDerivation ℝ F (B i) - truncTotal σ ℝ (N + 1) (mkDerivation ℝ F (B i)))‖ ≤ ε)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖x t - carlemanApproximant F x₀ N t‖ ≤ ε * t * Real.exp (K * t) := by
  have hbound := norm_aeval_sub_carlemanLiftedApproximant_le_mul_exp
    F x₀ x N B T K ε hx₀ hx hK hε hr t ht
  have hobs (i : σ) : B (κ i) = (truncTotal σ ℝ (N + 1)).rangeRestrict (X i) := by
    apply Subtype.ext
    change (B (κ i) : MvPolynomial σ ℝ) = truncTotal σ ℝ (N + 1) (X i)
    rw [truncTotal_X (N + 1) (by lia)]
    exact hB i
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg hε ht.1) (Real.exp_nonneg _))).mpr
  intro i
  calc
    ‖(x t - carlemanApproximant F x₀ N t) i‖ ≤
        ‖fun j => aeval (x t) (B j : MvPolynomial σ ℝ) -
          carlemanLiftedApproximant F x₀ N t (B j)‖ := by
      have h := norm_le_pi_norm (fun j => aeval (x t) (B j : MvPolynomial σ ℝ) -
        carlemanLiftedApproximant F x₀ N t (B j)) (κ i)
      simpa [hobs i, carlemanApproximant, truncTotal_X (N + 1) (by lia)] using h
    _ ≤ _ := hbound

end MvPolynomial

namespace Matrix
variable {ι : Type*} [Fintype ι]

/-- Absolute row sums bound the generator norm in maximum coordinates. -/
lemma norm_mulVec_toContinuousLinearMap_le_of_row_sum_le
    (A : Matrix ι ι ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hrows : ∀ i, ∑ j, |A i j| ≤ K) :
    ‖LinearMap.toContinuousLinearMap A.mulVecLin‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg v))).mpr
  intro i
  change ‖A.mulVec v i‖ ≤ K * ‖v‖
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrows i) (norm_nonneg v)

end Matrix
