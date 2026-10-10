/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.CommutatorExpansion.Basic

import FQFP.TrotterError.ListLemmas
import FQFP.TrotterError.IntervalIntegral

/-!
# Norm bounds for the multi-layer commutator remainder

General and skew-adjoint remainder estimates, including estimates after left
multiplication. This module is independent of the multi-layer expansion proof
and of time-ordered evolution.
-/

@[expose] public section

namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### Norm bounds for `thm:comm_exp_conj` -/

/-- The integral-norm estimation shared by the general and skew-adjoint remainder bounds: given a
nonnegative `C` and a pointwise bound for the smul'd conjugation, the beta integral yields
`C * |τ|^m / D * |τ|^q / q`. -/
lemma norm_integral_smul_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
  have hcont_g : Continuous (fun u : ℝ => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) := by
    fun_prop
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖
        ≤ |∫ u in 0..τ, C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun u => (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
                (expSMulConj A X u))
              (g := fun u => C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with u hu
              exact hpoint u hu
            · exact hcont_g.intervalIntegrable 0 τ
    _ = C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
            rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
            have hnonneg : 0 ≤ (∫ u in Set.uIoc (0 : ℝ) τ,
                C * (|τ - u| ^ (q - 1) * |τ| ^ m / D)) :=
              setIntegral_nonneg measurableSet_uIoc (fun u _ => by positivity)
            rw [abs_of_nonneg hnonneg]
            have hint : (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D)) =
                (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
              calc
                (∫ u in Set.uIoc (0 : ℝ) τ, (|τ - u| ^ (q - 1) * |τ| ^ m / D))
                    = (∫ u in Set.uIoc (0 : ℝ) τ, (|τ| ^ m / D) * |τ - u| ^ (q - 1)) := by
                        apply setIntegral_congr_fun measurableSet_uIoc
                        intro u _
                        ring
                _ = (|τ| ^ m / D) * (∫ u in Set.uIoc (0 : ℝ) τ, |τ - u| ^ (q - 1)) := by
                        rw [integral_const_mul]
                _ = (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) := by
                        rw [integral_abs_sub_pow_uIoc q τ hq]
            rw [integral_const_mul, hint]
            ring

/-- The norm of the `expSMulConj` integral is bounded by `C · |τ|^(q+m) / (q · D)` whenever the
conjugation is pointwise bounded by `C`. Shared by the general and skew-adjoint branches. -/
lemma norm_conj_smul_integral_le_of_norm_conj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      C * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) τ,
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by
    intro u hu
    have habs : |(τ - u) ^ (q - 1) * τ ^ m / D| = |τ - u| ^ (q - 1) * |τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ =
        (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    calc
      ‖(((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
          = (|τ - u| ^ (q - 1) * |τ| ^ m / D) * ‖expSMulConj A X u‖ := hsmul
      _ ≤ (|τ - u| ^ (q - 1) * |τ| ^ m / D) * C :=
              mul_le_mul_of_nonneg_left (hconj u hu) (by positivity)
      _ = C * (|τ - u| ^ (q - 1) * |τ| ^ m / D) := by ring
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * (|τ| ^ m / D) * (|τ| ^ q / (q : ℝ)) :=
            norm_integral_smul_conj_le A X q m D hq hD τ C hC hpoint
    _ = C * |τ| ^ (q + m) / ((q : ℝ) * D) := by
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            field_simp [hq_ne, hDne]
            ring

/-- The norm of the integral in one remainder summand is bounded by `‖X‖ · |τ|^(q+m) / (q · D) ·
e^{2|τ|‖A‖}`. Here the integrand is `((τ-u)^(q-1) · τ^m / D) • (e^{uA} X e^{-uA})`. -/
lemma norm_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (A X : 𝔸) (q m : ℕ) (D : ℝ) (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) •
        (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (2 * |τ| * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hconj : ∀ u ∈ Set.uIoc (0 : ℝ) τ, ‖expSMulConj A X u‖ ≤ C := by
    intro u hu
    refine (norm_expSMulConj_le A X u).trans ?_
    have harg : 2 * |u| * ‖A‖ ≤ 2 * |τ| * ‖A‖ := by
      have habs_u : |u| ≤ |τ| := by
        simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hu)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs_u (by norm_num))
        (norm_nonneg A)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (norm_nonneg X)
  calc
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖
        ≤ C * |τ| ^ (q + m) / ((q : ℝ) * D) :=
            norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ C hC hconj
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (2 * |τ| * ‖A‖) := by
            dsimp [C]
            ring_nf

/-- For `0 ≤ τ` and `u ∈ [0, -τ]`, the absorbed conjugation `e^{τA} e^{uA} X e^{-uA}` has norm
at most `‖X‖ · e^{τ‖A‖}`: the two inner exponentials `e^{(τ+u)A}` and `e^{-uA}` telescope to a
single factor of `τ`. -/
lemma norm_exp_mul_expSMulConj_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (τ u : ℝ) (hτ : 0 ≤ τ)
    (hu : u ∈ Set.uIcc (0 : ℝ) (-τ)) :
    ‖exp (τ • A) * expSMulConj A X u‖ ≤ ‖X‖ * Real.exp (τ * ‖A‖) := by
  have hu' : u ∈ Set.uIcc (-τ) (0 : ℝ) := by simpa [Set.uIcc_comm] using hu
  have hu'' : u ∈ Set.Icc (-τ) (0 : ℝ) := by
    rwa [Set.uIcc_of_le (neg_nonpos.mpr hτ)] at hu'
  have hge : -τ ≤ u := hu''.1
  have hle0 : u ≤ 0 := hu''.2
  have hτu : 0 ≤ τ + u := by linarith
  have hcomm : Commute (τ • A) (u • A) := (Commute.refl A).smul_left τ |>.smul_right u
  have h_exp : exp (τ • A) * exp (u • A) = exp ((τ + u) • A) := by
    rw [add_smul τ u A]
    exact (exp_add_of_commute hcomm).symm
  have h_prod : exp (τ • A) * expSMulConj A X u = exp ((τ + u) • A) * X * exp (-u • A) := by
    rw [expSMulConj, ← mul_assoc, ← mul_assoc, h_exp]
  have h1 : ‖exp ((τ + u) • A)‖ ≤ Real.exp ((τ + u) * ‖A‖) := by
    have hnorm : ‖(τ + u) • A‖ = (τ + u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτu]
    simpa [hnorm] using norm_exp_le ((τ + u) • A)
  have h2 : ‖exp (-u • A)‖ ≤ Real.exp ((-u) * ‖A‖) := by
    have hnorm : ‖u • A‖ = (-u) * ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hle0]
    simpa [hnorm] using norm_exp_le (-u • A)
  calc
    ‖exp (τ • A) * expSMulConj A X u‖
        = ‖exp ((τ + u) • A) * X * exp (-u • A)‖ := by rw [h_prod]
    _ ≤ ‖exp ((τ + u) • A)‖ * ‖X‖ * ‖exp (-u • A)‖ := by
            exact (norm_mul_le (exp ((τ + u) • A) * X) (exp (-u • A))).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le (exp ((τ + u) • A)) X) (norm_nonneg _))
    _ ≤ Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖) := by
            exact mul_le_mul (mul_le_mul h1 (le_refl ‖X‖) (norm_nonneg _) (by positivity)) h2
              (norm_nonneg _) (by positivity)
    _ = ‖X‖ * Real.exp (τ * ‖A‖) := by
            have harg : (τ + u) * ‖A‖ + (-u) * ‖A‖ = τ * ‖A‖ := by ring
            calc
              Real.exp ((τ + u) * ‖A‖) * ‖X‖ * Real.exp ((-u) * ‖A‖)
                  = ‖X‖ * (Real.exp ((τ + u) * ‖A‖) * Real.exp ((-u) * ‖A‖)) := by ring
              _ = ‖X‖ * Real.exp ((τ + u) * ‖A‖ + (-u) * ‖A‖) := by rw [Real.exp_add]
              _ = ‖X‖ * Real.exp (τ * ‖A‖) := by rw [harg]

/-- The norm of the integral of the *absorbed* conjugation `e^{τA} e^{uA} X e^{-uA}` times the
scalar `(-τ-u)^(q-1) (-τ)^m / D` is bounded by `‖X‖ |τ|^(q+m)/(q·D) e^{τ‖A‖}` — one factor of
`τ` instead of the naive `2|τ|`. -/
lemma norm_absorbed_conj_smul_integral_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸] (A X : 𝔸) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖) := by
  let C : ℝ := ‖X‖ * Real.exp (τ * ‖A‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg X) (Real.exp_nonneg _)
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) (-τ),
      ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) • (exp (τ • A) * expSMulConj A X u)‖
        ≤ C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) := by
    intro u hu
    have habs : |(-τ - u) ^ (q - 1) * (-τ) ^ m / D| = |-τ - u| ^ (q - 1) * |-τ| ^ m / D := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_nonneg (le_of_lt hD)]
    have hsmul : ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖ =
        (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * ‖exp (τ • A) * expSMulConj A X u‖ := by
      rw [norm_smul, Real.norm_eq_abs, habs]
    have hconj : ‖exp (τ • A) * expSMulConj A X u‖ ≤ C :=
      norm_exp_mul_expSMulConj_le A X τ u hτ (Set.uIoc_subset_uIcc hu)
    calc
      ‖(((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) • (exp (τ • A) * expSMulConj A X u)‖
          = (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * ‖exp (τ • A) * expSMulConj A X u‖ := hsmul
      _ ≤ (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) * C := by gcongr
      _ = C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D) := by ring
  have hcont_g : Continuous (fun u : ℝ => C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) := by
    fun_prop
  calc
    ‖∫ u in 0..(-τ), (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
        (exp (τ • A) * expSMulConj A X u)‖
        ≤ |∫ u in 0..(-τ), C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)| := by
            refine intervalIntegral.norm_integral_le_abs_of_norm_le
              (f := fun u => (((-τ - u) ^ (q - 1) * (-τ) ^ m / D) : ℝ) •
                (exp (τ • A) * expSMulConj A X u))
              (g := fun u => C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) ?_ ?_
            · rw [ae_restrict_iff' measurableSet_uIoc]
              filter_upwards with u hu
              exact hpoint u hu
            · exact hcont_g.intervalIntegrable 0 (-τ)
    _ = C * (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
            rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
            have hnonneg : 0 ≤ (∫ u in Set.uIoc (0 : ℝ) (-τ),
                C * (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) :=
              setIntegral_nonneg measurableSet_uIoc (fun u _ => by positivity)
            rw [abs_of_nonneg hnonneg]
            have hint : (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ - u| ^ (q - 1) * |-τ| ^ m / D)) =
                (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
              calc
                (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ - u| ^ (q - 1) * |-τ| ^ m / D))
                    = (∫ u in Set.uIoc (0 : ℝ) (-τ), (|-τ| ^ m / D) * |-τ - u| ^ (q - 1)) := by
                        apply setIntegral_congr_fun measurableSet_uIoc
                        intro u _
                        ring
                _ = (|-τ| ^ m / D) * (∫ u in Set.uIoc (0 : ℝ) (-τ), |-τ - u| ^ (q - 1)) := by
                        rw [integral_const_mul]
                _ = (|-τ| ^ m / D) * (|-τ| ^ q / (q : ℝ)) := by
                        rw [integral_abs_sub_pow_uIoc q (-τ) hq]
            rw [integral_const_mul, hint]
            ring
    _ = ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) * Real.exp (τ * ‖A‖) := by
            dsimp [C]
            have hq_ne : (q : ℝ) ≠ 0 := by positivity
            have hDne : D ≠ 0 := ne_of_gt hD
            rw [abs_neg]
            field_simp [hq_ne, hDne]
            ring

/-- Peeling the last entry off the prefix `(ofFn f).take (j+1)`: its product is the product of
`(ofFn f).take j` times `f j`. -/
lemma ofFn_take_succ_prod {s : ℕ} {𝔸 : Type*} [Monoid 𝔸] (f : Fin s → 𝔸) (j : Fin s) :
    ((List.ofFn f).take ((j : ℕ) + 1)).prod = ((List.ofFn f).take (j : ℕ)).prod * f j := by
  have htake : (List.ofFn f).take ((j : ℕ) + 1) = (List.ofFn f).take (j : ℕ) ++ [f j] := by
    rw [← List.take_concat_get' (List.ofFn f) (j : ℕ) (by simp)]
    simp [List.getElem_ofFn]
  rw [htake, List.prod_append, List.prod_singleton]

/-- The telescoping `(∏_k e^{τA_k}) · (e^{-τA_{s-1}} ⋯ e^{-τA_{j+1}}) = e^{τA_0} ⋯ e^{τA_j}`: the
outer exponential factors beyond layer `j` cancel against the reversed dropped suffix. -/
lemma prod_exp_mul_drop_reverse_telescope {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod
      = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod := by
  have hsplit : (List.ofFn (fun k : Fin s => exp (τ • A k))).prod =
      ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod *
        ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod := by
    simpa only [List.prod_append] using
      (congrArg List.prod (List.take_append_drop ((j : ℕ) + 1)
        (List.ofFn (fun k : Fin s => exp (τ • A k))))).symm
  have hcancel : ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod = 1 := by
    have hmapL : ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)) =
        (((List.ofFn A).drop ((j : ℕ) + 1)).map (fun x : 𝔸 => exp (τ • x))) := by
      rw [List.ofFn_comp' A (fun x => exp (τ • x)), ← List.map_drop]
    have hmapR : (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse) =
        ((((List.ofFn A).drop ((j : ℕ) + 1)).map (fun x : 𝔸 => exp (-τ • x))).reverse) := by
      rw [List.ofFn_comp' A (fun x => exp (-τ • x)), ← List.map_drop]
    rw [hmapL, hmapR]
    simpa [List.map_reverse] using prod_mul_rev_eq_one_of_mul_eq_one
      (l := (List.ofFn A).drop ((j : ℕ) + 1))
      (f := fun x : 𝔸 => exp (τ • x))
      (g := fun x : 𝔸 => exp (-τ • x))
      (hfg := fun x => by simpa [neg_smul] using exp_mul_neg_self (τ • x))
  calc
    (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
      (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod
        = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod *
            ((List.ofFn (fun k : Fin s => exp (τ • A k))).drop ((j : ℕ) + 1)).prod *
            (((List.ofFn (fun k : Fin s => exp (-τ • A k))).drop ((j : ℕ) + 1)).reverse).prod := by
              rw [hsplit]
    _ = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod * 1 := by
              rw [mul_assoc, hcancel]
    _ = ((List.ofFn (fun k : Fin s => exp (τ • A k))).take ((j : ℕ) + 1)).prod := by rw [mul_one]

/-- The product of the norms of exponentials `∏ᵢ ‖exp (tᵢ • Aᵢ)‖` is bounded by
`exp (Σᵢ |tᵢ| · ‖Aᵢ‖)`. -/
lemma norm_prod_exp_smul_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {ι : Type*} (l : List ι)
    (A : ι → 𝔸) (t : ι → ℝ) :
    (l.map (fun i => ‖exp (t i • A i)‖)).prod ≤
      Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
  calc
    (l.map (fun i => ‖exp (t i • A i)‖)).prod
        ≤ (l.map (fun i => Real.exp (|t i| * ‖A i‖))).prod := by
            have hle : ∀ i ∈ l, ‖exp (t i • A i)‖ ≤ Real.exp (|t i| * ‖A i‖) := by
              intro i _
              simpa [norm_smul] using norm_exp_le (t i • A i)
            have hnonneg : ∀ i ∈ l, 0 ≤ ‖exp (t i • A i)‖ := by
              intro i _
              exact norm_nonneg (exp (t i • A i))
            exact List.prod_map_le_prod_map₀
              (f := fun i => ‖exp (t i • A i)‖)
              (g := fun i => Real.exp (|t i| * ‖A i‖))
              (s := l) hnonneg hle
    _ = Real.exp ((l.map (fun i => |t i| * ‖A i‖)).sum) := by
            rw [Real.exp_list_sum, List.map_map]
            rfl

/-- The norm of the product of `exp (τ • A i)` over a sublist `l` of `Fin s` is bounded by
`exp (|τ| * (l.map ‖A ·‖).sum)`. -/
lemma norm_prod_exp_smul_list_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] {s : ℕ} (A : Fin s → 𝔸) (l : List (Fin s)) (τ : ℝ) :
    ‖(l.map (fun i => exp (τ • A i))).prod‖ ≤
      Real.exp (|τ| * (l.map (fun i => ‖A i‖)).sum) := by
  have h := norm_prod_exp_smul_le (l := l) (A := A) (t := fun _ : Fin s => τ)
  calc
    ‖(l.map (fun i => exp (τ • A i))).prod‖
        ≤ (l.map (fun i => ‖exp (τ • A i)‖)).prod := by
            simpa [List.map_map, Function.comp_def] using
              List.norm_prod_le (l.map (fun i => exp (τ • A i)))
    _ ≤ Real.exp ((l.map (fun i => |τ| * ‖A i‖)).sum) := h
    _ = Real.exp (|τ| * (l.map (fun i => ‖A i‖)).sum) := by rw [List.sum_map_mul_left]

/-- The norm of the outer (left) exponential product of a remainder summand is bounded by
`exp (Σ_{i ≥ k} |τ| · ‖A i‖)`, expressed as a `List` sum over the dropped suffix. -/
lemma norm_ofFn_drop_reverse_prod_exp_le {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).reverse.map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := by
            rw [List.map_reverse, List.prod_reverse]
    _ = ((List.ofFn (fun i : Fin s => ‖exp (τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The norms of the strictly-smaller layers, `A j`, and the strictly-larger layers partition the
total norm sum: `(take j).sum + ‖A j‖ + (drop (j+1)).sum = Σ_i ‖A i‖`. -/
lemma sum_norm_take_add_point_add_drop {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸)
    (j : Fin s) :
    ((List.ofFn (fun i : Fin s => ‖A i‖)).take (j : ℕ)).sum + ‖A j‖ +
      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop ((j : ℕ) + 1)).sum = ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hdrop : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := by simp [l])
    rw [← hcons, List.sum_cons]
    simp [l, List.getElem_ofFn]
  calc
    (l.take (j : ℕ)).sum + ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum
        = (l.take (j : ℕ)).sum + (l.drop (j : ℕ)).sum := by rw [hdrop]; ring
    _ = l.sum := by simp
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-- The sum of the norms of `A j` and the strictly-larger layers is at most the total norm sum. -/
lemma norm_point_add_drop_sum_le {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) :
    ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤ ∑ i : Fin s, ‖A i‖ := by
  let l : List ℝ := List.ofFn (fun i : Fin s => ‖A i‖)
  have hlen : (j : ℕ) < l.length := by simp [l]
  have hsplit : (l.drop (j : ℕ)).sum = ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum := by
    have hcons := List.cons_getElem_drop_succ (l := l) (n := (j : ℕ)) (h := hlen)
    rw [← hcons, List.sum_cons]
    simp [l]
  calc
    ‖A j‖ + (l.drop ((j : ℕ) + 1)).sum = (l.drop (j : ℕ)).sum := hsplit.symm
    _ ≤ l.sum := by
        have hnonneg : ∀ a ∈ l, (0 : ℝ) ≤ a := by
          intro a ha
          rcases (List.mem_ofFn' (fun i : Fin s => ‖A i‖) a).mp (by simpa [l] using ha) with ⟨i, hi⟩
          rw [← hi]
          exact norm_nonneg (A i)
        exact (List.drop_sublist (j : ℕ) l).sum_le_sum hnonneg
    _ = ∑ i : Fin s, ‖A i‖ := by simp [l, List.sum_ofFn]

/-! ### Completion: layering the remainder sum into `αCommConj` -/

/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖

/-- Splitting `αCommConj` over `Fin (s + 1)` into the inner `Fin s` part (zero on the last
layer) and the part with nonzero outermost multiplicity. -/
lemma αCommConj_snoc_split {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin (s + 1) → 𝔸)
    (B : 𝔸) (p : ℕ) :
    αCommConj A B p = αCommConj (fun i : Fin s => A i.castSucc) B p +
      ∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
        (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖ := by
  calc
    αCommConj A B p
        = ∑ q' ∈ finAntidiagonal (s + 1) p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q' : ℝ) *
              ‖adSequence A q' B‖ := rfl
    _ = ∑ k ∈ range (p + 1), ∑ q ∈ finAntidiagonal s (p - k),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q k) : ℝ) *
              ‖adSequence A (Fin.snoc q k) B‖ := by
              rw [sum_finAntidiagonal_snoc]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          (∑ q ∈ finAntidiagonal s p,
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
              ‖adSequence A (Fin.snoc q 0) B‖) := by
              rw [sum_range_succ', Nat.sub_zero]
    _ = (∑ k ∈ range p, ∑ q ∈ finAntidiagonal s (p - (k + 1)),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q (k + 1)) : ℝ) *
              ‖adSequence A (Fin.snoc q (k + 1)) B‖) +
          αCommConj (fun i : Fin s => A i.castSucc) B p := by
              rw [show (∑ q ∈ finAntidiagonal s p,
                (Nat.multinomial (univ : Finset (Fin (s + 1))) (Fin.snoc q 0) : ℝ) *
                  ‖adSequence A (Fin.snoc q 0) B‖) =
                αCommConj (fun i : Fin s => A i.castSucc) B p from by
                simp [αCommConj, adSequence_snoc_zero, multinomial_snoc_zero]]
    _ = αCommConj (fun i : Fin s => A i.castSucc) B p +
          (∑ q ∈ (finAntidiagonal (s + 1) p).filter (fun q => q (Fin.last s) ≠ 0),
            (Nat.multinomial (univ : Finset (Fin (s + 1))) q : ℝ) * ‖adSequence A q B‖) := by
              rw [add_comm, sum_finAntidiagonal_filter_last_ne_zero]

/-- The layer sum is bounded by `αCommConj`: collapsing each `(j, q)` into the antidiagonal of
`Fin s` by padding with zeros (theory.tex:198-214, the `Σ_k Σ_q → Σ_{q₁+⋯+q_s=p}` step). -/
lemma layerSum_le_αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) :
    layerSum A B p ≤ αCommConj A B p := by
  induction s with
  | zero =>
      simp only [layerSum, αCommConj]
      exact sum_nonneg (fun q _ => mul_nonneg (by positivity) (norm_nonneg _))
  | succ s ih =>
      rw [layerSum, Fin.sum_univ_castSucc]
      have hsplit : (∑ j : Fin s,
          (fun j : Fin (s + 1) =>
            ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
              (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
                ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖) j.castSucc)
          = layerSum (fun i : Fin s => A i.castSucc) B p := rfl
      rw [hsplit, αCommConj_snoc_split A B p]
      exact add_le_add (ih (fun i : Fin s => A i.castSucc)) (le_refl _)

/-- The scalar coefficient in one remainder summand equals `multinomial(q) · |τ|^p / p!`. -/
lemma coeff_eq_multinomial_div_factorial {j p : ℕ} (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hsum : (∑ i : Fin (j + 1), q i) = p) (hlast : 1 ≤ q (Fin.last j)) :
    |τ| ^ p / ((q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
  have hfac : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) =
      (Nat.factorial (q (Fin.last j)) : ℝ) := by
    rw [← Nat.cast_mul]
    congr 1
    have h := Nat.factorial_succ (q (Fin.last j) - 1)
    rw [Nat.sub_add_cancel hlast] at h
    exact h.symm
  have hden : (q (Fin.last j) : ℝ) * (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
        (∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)) =
      ∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ) := by
    rw [hfac, Fin.prod_univ_castSucc, mul_comm]
  have hms : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) *
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) = (Nat.factorial p : ℝ) := by
    have h' := Nat.multinomial_spec (s := (univ : Finset (Fin (j + 1)))) (f := q)
    rw [hsum] at h'
    exact_mod_cast h'
  rw [hden]
  have hfac_p : (Nat.factorial p : ℝ) ≠ 0 := by positivity
  have hprod : (∏ i : Fin (j + 1), (Nat.factorial (q i) : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => by positivity)
  field_simp [hfac_p, hprod]
  rw [← hms]; ring

/-- The telescoped remainder summand (with left context `L`): the norm of
`L · (∏_k e^{τA_k}) · commutatorRemainderTerm A B (-τ) j q` telescopes to a single exponential
`exp(|τ| (C + Σ_k ‖A_k‖))`, with `‖L‖ ≤ exp(|τ| C)`. -/
lemma norm_mul_commutatorRemainderTerm_le {s : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (A : Fin s → 𝔸) (B : 𝔸) (L : 𝔸) (C : ℝ) (p : ℕ) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (τ : ℝ) (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0)
    (hL : ‖L‖ ≤ Real.exp (|τ| * C)) :
    ‖L * (List.ofFn (fun k : Fin s => exp (τ • A k))).prod *
        commutatorRemainderTerm A B (-τ) j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
        |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  let E : List 𝔸 := List.ofFn (fun k : Fin s => exp (τ • A k))
  let En : List 𝔸 := List.ofFn (fun k : Fin s => exp (-τ • A k))
  let N : List ℝ := List.ofFn (fun k : Fin s => ‖A k‖)
  let m : ℕ := q (Fin.last j)
  let r : ℕ := ∑ i : Fin j, q i.castSucc
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast' : 1 ≤ q (Fin.last j) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have hcont : Continuous (fun u : ℝ => (((-τ - u) ^ (m - 1) *
      (-τ) ^ r / D) : ℝ) • expSMulConj (A j) X u) := by
    fun_prop
  have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
    rw [add_comm]
    exact (Fin.sum_univ_castSucc (f := q)).symm.trans hsum
  have h_unfold : commutatorRemainderTerm A B (-τ) j q =
      ((En.drop ((j : ℕ) + 1)).reverse.prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • expSMulConj (A j) X u) *
        (E.drop ((j : ℕ) + 1)).prod) := by
    unfold commutatorRemainderTerm
    simp [X, D, E, En, m, r]
  have h_eq : L * E.prod * commutatorRemainderTerm A B (-τ) j q =
      L * (E.take (j : ℕ)).prod *
        (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
            D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
        (E.drop ((j : ℕ) + 1)).prod := by
    rw [h_unfold]
    calc
      L * E.prod * ((En.drop ((j : ℕ) + 1)).reverse.prod *
          (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
              D) : ℝ) • expSMulConj (A j) X u) *
          (E.drop ((j : ℕ) + 1)).prod)
          = L * (E.prod * (En.drop ((j : ℕ) + 1)).reverse.prod) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by ac_rfl
      _ = L * (E.take ((j : ℕ) + 1)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [prod_exp_mul_drop_reverse_telescope A j τ]
      _ = L * (E.take (j : ℕ)).prod * exp (τ • A j) *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • expSMulConj (A j) X u) *
            (E.drop ((j : ℕ) + 1)).prod := by
              rw [ofFn_take_succ_prod (fun k : Fin s => exp (τ • A k)) j]
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (exp (τ • A j) * (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^
              (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              ac_rfl
      _ = L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod := by
              congr 3
              rw [← integral_mul_left (exp (τ • A j))
                (fun u => (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  expSMulConj (A j) X u) hcont 0 (-τ)]
              apply intervalIntegral.integral_congr_uIoo
              intro u _
              change exp (τ • A j) * (((-τ - u) ^ (m - 1) * (-τ) ^
                  (∑ i : Fin j, q i.castSucc) / D) : ℝ) • expSMulConj (A j) X u =
                (((-τ - u) ^ (m - 1) * (-τ) ^ r / D) : ℝ) •
                  (exp (τ • A j) * expSMulConj (A j) X u)
              rw [mul_smul_comm]
  have htake : ‖(E.take (j : ℕ)).prod‖ ≤ Real.exp (|τ| * (N.take (j : ℕ)).sum) := by
    simpa [E, N, List.map_take, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).take (j : ℕ)) τ
  have hdrop : ‖(E.drop ((j : ℕ) + 1)).prod‖ ≤ Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
    simpa [E, N, List.map_drop, List.map_ofFn, Function.comp_def] using
      norm_prod_exp_smul_list_le A ((List.ofFn (fun k : Fin s => k)).drop ((j : ℕ) + 1)) τ
  have hint : ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
        D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (τ * ‖A j‖) :=
    norm_absorbed_conj_smul_integral_le (A j) X (q (Fin.last j)) (∑ i : Fin j, q i.castSucc) D
      hlast' hD τ hτ
  have hcomb : Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
        Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) =
      Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, abs_of_nonneg hτ]
    ring_nf
  have hexp_arg : C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum =
      C + ∑ k : Fin s, ‖A k‖ := by
    calc
      C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum
          = C + ((N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum) := by ring
      _ = C + ∑ k : Fin s, ‖A k‖ := by simpa [N] using sum_norm_take_add_point_add_drop A j
  calc
    ‖L * E.prod * commutatorRemainderTerm A B (-τ) j q‖
        = ‖L * (E.take (j : ℕ)).prod *
            (∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)) *
            (E.drop ((j : ℕ) + 1)).prod‖ := by rw [h_eq]
    _ ≤ ‖L‖ * ‖(E.take (j : ℕ)).prod‖ *
            ‖∫ u in 0..(-τ), (((-τ - u) ^ (m - 1) * (-τ) ^ r /
                D) : ℝ) • (exp (τ • A j) * expSMulConj (A j) X u)‖ *
            ‖(E.drop ((j : ℕ) + 1)).prod‖ := by
            exact (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
                ((q (Fin.last j) : ℝ) * D) * Real.exp (τ * ‖A j‖)) *
            Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum) := by
            refine mul_le_mul
              (mul_le_mul (mul_le_mul hL htake (by positivity) (by positivity)) hint
                (by positivity) (by positivity))
              hdrop (by positivity) (by positivity)
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            (Real.exp (|τ| * C) * Real.exp (|τ| * (N.take (j : ℕ)).sum) *
              Real.exp (τ * ‖A j‖) * Real.exp (|τ| * (N.drop ((j : ℕ) + 1)).sum)) := by
            ring_nf
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
            Real.exp (|τ| * (C + (N.take (j : ℕ)).sum + ‖A j‖ + (N.drop ((j : ℕ) + 1)).sum)) := by
            rw [hcomb]
    _ = ‖X‖ * (|τ| ^ p / ((q (Fin.last j) : ℝ) * D)) *
            Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            rw [hqsum, hexp_arg]
    _ = ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ)) *
            Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            dsimp [D]
            rw [← mul_assoc, coeff_eq_multinomial_div_factorial q τ hsum hlast']
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (|τ| * (C + ∑ k : Fin s, ‖A k‖)) := by
            dsimp [X]
            ring

/-- Combining the exponential factors of one remainder summand into the global exponential. -/
lemma exp_bound_combine {s} {𝔸 : Type*} [NormedRing 𝔸] (A : Fin s → 𝔸) (j : Fin s) (τ : ℝ) :
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
      Real.exp (2 * |τ| * ‖A j‖) *
        Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) ≤
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  have hS : ((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum =
      |τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum := by
    rw [List.ofFn_comp' (f := fun i : Fin s => ‖A i‖) (g := fun x : ℝ => |τ| * x),
      ← List.map_drop, List.sum_map_mul_left, List.map_id']
  calc
    Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
        Real.exp (2 * |τ| * ‖A j‖) *
          Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)
        = Real.exp (2 * (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum +
              |τ| * ‖A j‖)) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 1; ring
    _ ≤ Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              apply Real.exp_le_exp.mpr
              rw [hS]
              have hle : ‖A j‖ + ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum ≤
                  ∑ i : Fin s, ‖A i‖ := norm_point_add_drop_sum_le A j
              have h1 : 2 * (|τ| * ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum +
                    |τ| * ‖A j‖) = 2 * |τ| * (‖A j‖ +
                      ((List.ofFn (fun i : Fin s => ‖A i‖)).drop (j + 1)).sum) := by ring
              rw [h1]
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hle (abs_nonneg τ)) (by norm_num : 0 ≤ (2 : ℝ)))

/-- The norm of the outer (right) exponential product is bounded by the same suffix exponential. -/
lemma norm_ofFn_drop_prod_exp_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (k : ℕ) (τ : ℝ) :
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := by
  have h := norm_prod_exp_smul_le (l := (List.ofFn (fun i : Fin s => i)).drop k)
    (A := A) (t := fun _ : Fin s => -τ)
  have hmap : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => ‖exp (-τ • A i)‖) =
      (List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
  have hmap' : ((List.ofFn (fun i : Fin s => i)).drop k).map (fun i => |-τ| * ‖A i‖) =
      (List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k := by
    rw [List.map_drop, ← List.ofFn_comp']
    simp [abs_neg]
  rw [hmap, hmap'] at h
  calc
    ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).prod‖
        ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop k).map
            (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
    _ = ((List.ofFn (fun i : Fin s => ‖exp (-τ • A i)‖)).drop k).prod := by
            rw [List.map_drop, ← List.ofFn_comp']
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop k).sum) := h

/-- The norm bound of a single remainder summand. -/
lemma norm_commutatorRemainderTerm_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (j : Fin s) (q : Fin (j + 1) → ℕ) (hq : q ∈ finAntidiagonal (j + 1) p)
    (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hD : 0 < D := by positivity
  have houterL : ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_reverse_prod_exp_le A (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤
      Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) :=
    norm_ofFn_drop_prod_exp_le A (j + 1) τ
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) *
        Real.exp (2 * |τ| * ‖A j‖) := by
        simpa [D] using norm_conj_smul_integral_le (A j) X (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D (by lia) hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum, ← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum (by lia)
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
              ((q (Fin.last j) : ℝ) * D) *
              Real.exp (2 * |τ| * ‖A j‖)) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D)) *
          (Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum) *
            Real.exp (2 * |τ| * ‖A j‖) *
            Real.exp (((List.ofFn (fun i : Fin s => |τ| * ‖A i‖)).drop (j + 1)).sum)) := by ring
    _ ≤ ‖X‖ * ((Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ)) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              rw [hcoeff]; gcongr
              exact exp_bound_combine A j τ
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
              dsimp [X]; ring

/-- Shared summation skeleton of the left-multiplied commutator-remainder norm bound: given a
pointwise bound `‖M · commutatorRemainderTerm A B τ j q‖ ≤ ‖adSequence … q B‖ · multinomial(q) ·
|τ|^p/p! · F` with nonnegative `F`, the total left-multiplied remainder is bounded by
`αCommConj A B p · |τ|^p/p! · F`. -/
lemma norm_mul_commutatorRemainder_le_of_term_bound {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (M : 𝔸) (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ)
    (hF : 0 ≤ F)
    (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ,
      q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) →
        ‖M * commutatorRemainderTerm A B τ j q‖ ≤
          ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * F) :
    ‖M * commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
  rw [commutatorRemainder]
  simp_rw [Finset.mul_sum]
  have h1 : ‖∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), M * commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖M * commutatorRemainderTerm A B τ j q‖ := by
    apply norm_sum_le_of_le
    intros; exact norm_sum_le ..
  have h2 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0), ‖M * commutatorRemainderTerm A B τ j q‖ ≤
      ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F :=
    sum_le_sum (fun j _ => sum_le_sum (fun q hq => hterm j q hq))
  have h3 : ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
      (fun q => q (Fin.last j) ≠ 0),
        ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) * F ≤
      αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
    have hlayer : layerSum A B p ≤ αCommConj A B p := layerSum_le_αCommConj A B p
    have hnonneg : 0 ≤ |τ| ^ p / (Nat.factorial p : ℝ) * F := by positivity
    have hmain : (∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter
        (fun q => q (Fin.last j) ≠ 0),
          (‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ)) *
            (|τ| ^ p / (Nat.factorial p : ℝ) * F)) ≤
        αCommConj A B p * (|τ| ^ p / (Nat.factorial p : ℝ) * F) := by
      simp_rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (by simpa [layerSum, mul_comm] using hlayer) hnonneg
    simpa [div_eq_mul_inv, mul_assoc] using hmain
  exact h1.trans (h2.trans h3)

/-- A pointwise bound on the remainder terms gives the corresponding bound on the total
remainder. This is `norm_mul_commutatorRemainder_le_of_term_bound` with multiplier `1`. -/
lemma norm_commutatorRemainder_le_of_term_bound {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℝ 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) (F : ℝ)
    (hF : 0 ≤ F)
    (hterm : ∀ j : Fin s, ∀ q : Fin (j + 1) → ℕ,
      q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0) →
        ‖commutatorRemainderTerm A B τ j q‖ ≤
          ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
            (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
              (Nat.factorial p : ℝ) * F) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) * F := by
  simpa only [one_mul] using
    norm_mul_commutatorRemainder_le_of_term_bound (1 : 𝔸) A B p τ F hF
      (by simpa only [one_mul] using hterm)

/-- The spectral-norm bound of the commutator remainder (theory.tex:238-241, general operators). -/
theorem norm_commutatorRemainder_le {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖) := by
  refine norm_commutatorRemainder_le_of_term_bound A B p τ
    (Real.exp (2 * |τ| * ∑ i : Fin s, ‖A i‖)) (le_of_lt (Real.exp_pos _)) ?_
  intro j q hq
  exact norm_commutatorRemainderTerm_le A B p τ j q (mem_filter.mp hq).1 (mem_filter.mp hq).2

/-- The product of the norms of skew-exponentials `exp (τ • A i)` is at most `1`. -/
lemma norm_ofFn_drop_prod_le_one_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (hskew : ∀ i, star (A i) = -A i)
    (k : ℕ) (τ : ℝ) :
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod ≤ 1 := by
  have hle : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, ‖exp (τ • A i)‖ ≤ 1 := by
    intro i _
    exact (norm_exp_smul_of_skewAdjoint (hskew i) τ).le
  have hnonneg : ∀ i ∈ (List.ofFn (fun i : Fin s => i)).drop k, 0 ≤ ‖exp (τ • A i)‖ := by
    intro i _
    exact norm_nonneg (exp (τ • A i))
  have h := List.prod_map_le_prod_map₀
    (f := fun i : Fin s => ‖exp (τ • A i)‖)
    (g := fun _ : Fin s => (1 : ℝ))
    (s := (List.ofFn (fun i : Fin s => i)).drop k) hnonneg hle
  calc
    (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop k).map (fun x : 𝔸 => ‖x‖)).prod
        = (((List.ofFn (fun i : Fin s => i)).drop k).map
            (fun i : Fin s => ‖exp (τ • A i)‖)).prod := by
              rw [List.map_drop, List.map_ofFn, List.map_drop, List.map_ofFn]
              rfl
    _ ≤ (((List.ofFn (fun i : Fin s => i)).drop k).map (fun _ : Fin s => (1 : ℝ))).prod := h
    _ = 1 := by
      rw [List.map_drop, List.map_ofFn]
      apply List.prod_eq_one
      intro x hx
      have hx' : x ∈ List.ofFn (fun _ : Fin s => (1 : ℝ)) :=
        (List.drop_sublist k (List.ofFn (fun _ : Fin s => (1 : ℝ)))).subset hx
      rcases (List.mem_ofFn' (fun _ : Fin s => (1 : ℝ)) x).mp hx' with ⟨i, hi⟩
      rw [← hi]

/-- The norm of the integral in one skew-adjoint remainder summand is bounded by
`‖X‖ · |τ|^(q+m) / (q · D)` (no exponential factor). -/
lemma norm_conj_smul_integral_le_of_skew {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]
    [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A X : 𝔸) (hskew : star A = -A) (q m : ℕ) (D : ℝ)
    (hq : 1 ≤ q) (hD : 0 < D) (τ : ℝ) :
    ‖∫ u in 0..τ, (((τ - u) ^ (q - 1) * τ ^ m / D) : ℝ) • (expSMulConj A X u)‖ ≤
      ‖X‖ * |τ| ^ (q + m) / ((q : ℝ) * D) := by
  refine norm_conj_smul_integral_le_of_norm_conj_le A X q m D hq hD τ ‖X‖ (norm_nonneg X) ?_
  intro u _
  exact norm_expSMulConj_le_of_skewAdjoint A X hskew u

/-- The norm bound of a single remainder summand in the skew-adjoint case. -/
lemma norm_commutatorRemainderTerm_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ)
    (τ : ℝ) (hskew : ∀ i, star (A i) = -A i) (j : Fin s) (q : Fin (j + 1) → ℕ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖commutatorRemainderTerm A B τ j q‖ ≤
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
          (Nat.factorial p : ℝ) := by
  let X : 𝔸 := adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B
  let D : ℝ := (Nat.factorial (q (Fin.last j) - 1) : ℝ) *
    ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ)
  have hsum : (∑ i : Fin (j + 1), q i) = p := mem_finAntidiagonal.mp hq
  have hlast_le : 1 ≤ q (Fin.last j) := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hlast)
  have hD : 0 < D := by positivity
  have houterL :
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ = (((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := by rw [List.map_reverse, List.prod_reverse]
      _ ≤ 1 := norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) τ
  have houterR : ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ ≤ 1 := by
    calc
      ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖
          ≤ (((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).map
              (fun x : 𝔸 => ‖x‖)).prod := List.norm_prod_le _
      _ ≤ 1 := by simpa using norm_ofFn_drop_prod_le_one_of_skewAdjoint A hskew (j + 1) (-τ)
  have hint : ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        D) : ℝ) • (expSMulConj (A j) X u)‖ ≤
      ‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) := by
        simpa [D] using norm_conj_smul_integral_le_of_skew (A j) X (hskew j) (q (Fin.last j))
          (∑ i : Fin j, q i.castSucc) D hlast_le hD τ
  have hcoeff : |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) / ((q (Fin.last j) : ℝ) * D) =
      (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
        (Nat.factorial p : ℝ) := by
    have hqsum : q (Fin.last j) + (∑ i : Fin j, q i.castSucc) = p := by
      calc
        q (Fin.last j) + (∑ i : Fin j, q i.castSucc)
            = (∑ i : Fin j, q i.castSucc) + q (Fin.last j) := by rw [add_comm]
        _ = ∑ i : Fin (j + 1), q i := (Fin.sum_univ_castSucc (f := q)).symm
        _ = p := hsum
    rw [hqsum, ← mul_assoc]
    exact coeff_eq_multinomial_div_factorial q τ hsum hlast_le
  calc
    ‖commutatorRemainderTerm A B τ j q‖
        ≤ ‖((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod‖ *
            ‖∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
                D) : ℝ) • (expSMulConj (A j) X u)‖ *
            ‖((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod‖ := by
              unfold commutatorRemainderTerm
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * |τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
          ((q (Fin.last j) : ℝ) * D)) * 1 := by gcongr
    _ = ‖X‖ * (|τ| ^ (q (Fin.last j) + (∑ i : Fin j, q i.castSucc)) /
        ((q (Fin.last j) : ℝ) * D)) := by ring
    _ = ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p /
            (Nat.factorial p : ℝ) := by rw [hcoeff]; dsimp [X]; ring

/-- The spectral-norm bound of the commutator remainder for anti-Hermitian operators
(theory.tex:242-244). -/
theorem norm_commutatorRemainder_le_of_skewAdjoint {s} {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [StarRing 𝔸] [CStarRing 𝔸]
    [Nontrivial 𝔸] [StarModule ℝ 𝔸] [CompleteSpace 𝔸] (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ)
    (hskew : ∀ i, star (A i) = -A i) :
    ‖commutatorRemainder A B p τ‖ ≤ αCommConj A B p * |τ| ^ p / (Nat.factorial p : ℝ) := by
  simpa [mul_one] using (norm_commutatorRemainder_le_of_term_bound A B p τ 1 (by norm_num)
    (fun j q hq => by
      simpa [mul_one] using norm_commutatorRemainderTerm_le_of_skewAdjoint A B p τ hskew j q
        (mem_filter.mp hq).1 (mem_filter.mp hq).2))

end TrotterError
