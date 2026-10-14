/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.Approximant
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The scalar quadratic equation `x' = x²`

The order-`N` recovered Carleman trajectory is the first `N` terms of a
geometric series. This module connects that explicit expression to the
existing approximant, the exact rational solution, and uniform convergence.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MvPolynomial Filter

namespace Carleman.ScalarQuadratic

/-- The concrete polynomial vector field for `x' = x²`. -/
def vectorField : Unit → MvPolynomial Unit ℝ := fun _ => X () ^ 2

/-- The exact scalar solution, defined away from the pole in the ODE lemmas. -/
def solution (a t : ℝ) : ℝ := a / (1 - a * t)

private def liftedCoordinate (a : ℝ) (N k : ℕ) (t : ℝ) : ℝ :=
  carlemanLiftedApproximant vectorField (fun _ => a) N t
    ((truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ k))

private lemma truncTotal_X_pow (N k : ℕ) :
    truncTotal Unit ℝ (N + 1) (X () ^ k) =
      if k ≤ N then (X () : MvPolynomial Unit ℝ) ^ k else 0 := by
  have hk : ((X () : MvPolynomial Unit ℝ) ^ k).IsHomogeneous k := by
    simpa using (isHomogeneous_X ℝ ()).pow k
  simpa [Nat.lt_succ_iff] using truncTotal_of_isHomogeneous (N + 1) k hk

private lemma derivation_X_pow (k : ℕ) :
    mkDerivation ℝ vectorField (X () ^ k) = (k : ℝ) • (X () : MvPolynomial Unit ℝ) ^ (k + 1) := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Derivation.leibniz_pow]
    simp only [Nat.add_sub_cancel, mkDerivation_X, vectorField, smul_eq_mul]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp only [Algebra.smul_def, algebraMap_eq]
    rw [← pow_add]

private lemma compressedDerivation_X_pow (N k : ℕ) :
    compressedDerivation (mkDerivation ℝ vectorField) (N + 1)
        ((truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ k)) =
      (k : ℝ) • (truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ (k + 1)) := by
  apply Subtype.ext
  change truncTotal Unit ℝ (N + 1)
    (mkDerivation ℝ vectorField (truncTotal Unit ℝ (N + 1) (X () ^ k))) =
      (k : ℝ) • truncTotal Unit ℝ (N + 1) (X () ^ (k + 1))
  rw [truncTotal_X_pow]
  by_cases hk : k ≤ N
  · rw [ite_eq_left hk, derivation_X_pow, map_smul]
  · rw [ite_eq_right hk, map_zero, map_zero, truncTotal_X_pow,
      ite_eq_right (show ¬ k + 1 ≤ N by lia), smul_zero]

private lemma liftedCoordinate_initial (a : ℝ) (N k : ℕ) (hk : k ≤ N) :
    liftedCoordinate a N k 0 = a ^ k := by
  simp [liftedCoordinate, carlemanLiftedApproximant_initial, truncTotal_X_pow, hk]

private lemma liftedCoordinate_eq_zero (a : ℝ) (N k : ℕ) (hk : N < k) (t : ℝ) :
    liftedCoordinate a N k t = 0 := by
  have hz : (truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ k) = 0 := by
    apply Subtype.ext
    simp [truncTotal_X_pow, not_le.mpr hk]
  simp [liftedCoordinate, hz]

private lemma liftedCoordinate_hasDerivAt (a : ℝ) (N k : ℕ) (t : ℝ) :
    HasDerivAt (liftedCoordinate a N k) ((k : ℝ) * liftedCoordinate a N (k + 1) t) t := by
  unfold liftedCoordinate
  simpa only [LinearMap.dualMap_apply, compressedDerivation_X_pow,
    map_smul, smul_eq_mul] using
    carlemanLiftedApproximant_hasDerivAt vectorField (fun _ => a) N t
      ((truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ k))

private def coordinatePolynomial (a : ℝ) (k r : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), ((k + j - 1).choose j : ℝ) * a ^ (k + j) * t ^ j

private lemma coordinatePolynomial_initial (a : ℝ) (k r : ℕ) :
    coordinatePolynomial a k r 0 = a ^ k := by
  simp only [coordinatePolynomial, Finset.sum_range_succ']
  simp

private lemma coordinatePolynomial_zero (a : ℝ) (k : ℕ) :
    coordinatePolynomial a k 0 = fun _ => a ^ k := by
  funext t
  simp [coordinatePolynomial]

private lemma coordinatePolynomial_hasDerivAt (a : ℝ) (k r : ℕ) (t : ℝ) :
    HasDerivAt (coordinatePolynomial a k (r + 1))
      ((k : ℝ) * coordinatePolynomial a (k + 1) r t) t := by
  have hterm (j : ℕ) : HasDerivAt
      (fun s => ((k + (j + 1) - 1).choose (j + 1) : ℝ) * a ^ (k + (j + 1)) * s ^ (j + 1))
      ((k : ℝ) * ((k + 1 + j - 1).choose j : ℝ) * a ^ (k + 1 + j) * t ^ j) t := by
    have hc : ((k + j).choose (j + 1) : ℝ) * (j + 1 : ℝ) =
        (k : ℝ) * ((k + j).choose j : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_sub_cancel, Nat.mul_comm] using
        Nat.choose_succ_right_eq (k + j) j)
    convert (hasDerivAt_pow (j + 1) t).const_mul
      (((k + (j + 1) - 1).choose (j + 1) : ℝ) * a ^ (k + (j + 1))) using 1
    rw [show k + (j + 1) - 1 = k + j by lia,
      show k + 1 + j - 1 = k + j by lia,
      show k + (j + 1) = k + 1 + j by lia]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    calc
      _ = (((k + j).choose (j + 1) : ℝ) * (j + 1 : ℝ)) * a ^ (k + 1 + j) * t ^ j := by
        rw [hc]
      _ = _ := by ring
  have hsum :=
    (HasDerivAt.fun_sum (u := Finset.range (r + 1)) (fun j _ => hterm j)).add_const (a ^ k)
  convert hsum using 1
  · funext s
    simp only [coordinatePolynomial, Finset.sum_range_succ']
    simp
  · simp only [coordinatePolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private lemma liftedCoordinate_eq_polynomial (a : ℝ) (N k r : ℕ) (hkr : k + r = N) :
    liftedCoordinate a N k = coordinatePolynomial a k r := by
  induction r generalizing k with
  | zero =>
    have hdiff (t : ℝ) : HasDerivAt
        (fun s => liftedCoordinate a N k s - coordinatePolynomial a k 0 s) 0 t := by
      have hk : N < k + 1 := by lia
      convert (liftedCoordinate_hasDerivAt a N k t).sub (hasDerivAt_const t (a ^ k)) using 1
      · funext s
        simp only [coordinatePolynomial_zero, Pi.sub_apply]
      · simp only [liftedCoordinate_eq_zero a N (k + 1) hk, mul_zero, sub_zero]
    funext t
    have hconst := is_const_of_deriv_eq_zero (fun t => (hdiff t).differentiableAt)
      (fun t => (hdiff t).deriv) t 0
    rw [liftedCoordinate_initial a N k (by lia), coordinatePolynomial_initial, sub_self] at hconst
    exact sub_eq_zero.mp hconst
  | succ r ih =>
    have hnext := ih (k + 1) (by lia)
    have hdiff (t : ℝ) : HasDerivAt
        (fun s => liftedCoordinate a N k s - coordinatePolynomial a k (r + 1) s) 0 t := by
      convert (liftedCoordinate_hasDerivAt a N k t).sub
        (coordinatePolynomial_hasDerivAt a k r t) using 1
      rw [hnext, sub_self]
    funext t
    have hconst := is_const_of_deriv_eq_zero (fun t => (hdiff t).differentiableAt)
      (fun t => (hdiff t).deriv) t 0
    rw [liftedCoordinate_initial a N k (by lia), coordinatePolynomial_initial, sub_self] at hconst
    exact sub_eq_zero.mp hconst

/-- Every retained monomial coordinate has an explicit finite polynomial evolution. -/
lemma carlemanLiftedApproximant_pow_eq (a : ℝ) (N k r : ℕ) (hkr : k + r = N) (t : ℝ) :
    carlemanLiftedApproximant vectorField (fun _ => a) N t
        ((truncTotal Unit ℝ (N + 1)).rangeRestrict (X () ^ k)) =
      ∑ j ∈ Finset.range (r + 1), ((k + j - 1).choose j : ℝ) * a ^ (k + j) * t ^ j :=
  congrFun (liftedCoordinate_eq_polynomial a N k r hkr) t

/-- Order `N` retains exactly the first `N` terms of the geometric expansion.
The identity also covers the zero-order recovery convention. -/
lemma carlemanApproximant_eq_sum (a : ℝ) (N : ℕ) (t : ℝ) :
    carlemanApproximant vectorField (fun _ => a) N t () =
      a * ∑ j ∈ Finset.range N, (a * t) ^ j := by
  cases N with
  | zero => simp [carlemanApproximant_zero_order]
  | succ N =>
    have h := carlemanLiftedApproximant_pow_eq a (N + 1) 1 N (by lia) t
    change carlemanLiftedApproximant vectorField (fun _ => a) (N + 1) t
      ((truncTotal Unit ℝ (N + 1 + 1)).rangeRestrict (X ())) = _
    simpa [pow_one, Nat.add_comm, mul_pow, pow_succ, Finset.mul_sum, mul_assoc,
      mul_left_comm, mul_comm] using h

@[simp] lemma solution_initial (a : ℝ) : solution a 0 = a := by
  simp [solution]

/-- The rational trajectory solves `x' = x²` wherever its denominator is nonzero. -/
lemma solution_hasDerivAt (a t : ℝ) (ht : 1 - a * t ≠ 0) :
    HasDerivAt (solution a) ((solution a t) ^ 2) t := by
  convert (hasDerivAt_const t a).div
    ((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul a)) ht using 1
  · funext s
    rfl
  · dsimp [solution]
    field_simp
    ring

/-- Exact error, including the zero-order convention. -/
lemma solution_sub_carlemanApproximant (a : ℝ) (N : ℕ) (t : ℝ)
    (ht : 1 - a * t ≠ 0) :
    solution a t - carlemanApproximant vectorField (fun _ => a) N t () =
      a * (a * t) ^ N / (1 - a * t) := by
  rw [carlemanApproximant_eq_sum, solution]
  have hgeom := geom_sum_mul_neg (a * t) N
  field_simp
  linear_combination -a * hgeom

/-- The interval hypothesis gives a positive denominator uniformly away from the pole. -/
lemma one_sub_mul_pos_of_mem_Icc (a T t : ℝ) (hq : |a| * T < 1)
    (ht : t ∈ Set.Icc (-T) T) : 0 < 1 - a * t := by
  have hat : |a * t| ≤ |a| * T := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) (abs_nonneg a)
  linarith [le_abs_self (a * t)]

/-- The exact ODE holds within the certified closed interval, including its endpoints. -/
lemma solution_hasDerivWithinAt_of_mem_Icc (a T t : ℝ) (hq : |a| * T < 1)
    (ht : t ∈ Set.Icc (-T) T) :
    HasDerivWithinAt (solution a) ((solution a t) ^ 2) (Set.Icc (-T) T) t :=
  (solution_hasDerivAt a t (one_sub_mul_pos_of_mem_Icc a T t hq ht).ne').hasDerivWithinAt

/-- Geometric error bound uniform over the compact time interval `[-T,T]`. -/
lemma abs_solution_sub_carlemanApproximant_le (a T : ℝ) (hT : 0 ≤ T)
    (hq : |a| * T < 1) (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-T) T) :
    |solution a t - carlemanApproximant vectorField (fun _ => a) N t ()| ≤
      |a| * (|a| * T) ^ N / (1 - |a| * T) := by
  have hden := one_sub_mul_pos_of_mem_Icc a T t hq ht
  have hat : |a * t| ≤ |a| * T := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) (abs_nonneg a)
  rw [solution_sub_carlemanApproximant a N t hden.ne', abs_div, abs_mul, abs_pow,
    abs_of_pos hden]
  apply div_le_div₀
  · positivity
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg (a * t)) hat N) (abs_nonneg a)
  · linarith
  · linarith [le_abs_self (a * t)]

/-- The recovered Carleman trajectories converge uniformly on every certified interval. -/
lemma tendstoUniformlyOn_carlemanApproximant (a T : ℝ) (hT : 0 ≤ T) (hq : |a| * T < 1) :
    TendstoUniformlyOn (fun N t => carlemanApproximant vectorField (fun _ => a) N t ())
      (solution a) atTop (Set.Icc (-T) T) := by
  have hlim : Tendsto (fun N : ℕ => |a| * (|a| * T) ^ N / (1 - |a| * T)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (mul_nonneg (abs_nonneg a) hT) hq).const_mul |a|).div_const (1 - |a| * T)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN t ht
  exact lt_of_le_of_lt (by simpa only [Real.dist_eq] using
    abs_solution_sub_carlemanApproximant_le a T hT hq N t ht) hN

/-- Pointwise convergence throughout the geometric expansion domain. -/
lemma tendsto_carlemanApproximant (a t : ℝ) (ht : |a * t| < 1) :
    Tendsto (fun N => carlemanApproximant vectorField (fun _ => a) N t ()) atTop
      (𝓝 (solution a t)) := by
  exact (tendstoUniformlyOn_carlemanApproximant a |t| (abs_nonneg t)
    (by simpa only [abs_mul] using ht)).tendsto_at ⟨neg_abs_le t, le_abs_self t⟩

end Carleman.ScalarQuadratic
