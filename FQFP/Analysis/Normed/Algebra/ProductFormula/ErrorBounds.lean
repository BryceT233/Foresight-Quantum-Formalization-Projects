/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.OneNormScaling
public import FQFP.Analysis.Normed.Algebra.ProductFormula.CommutatorScaling
import FQFP.Analysis.Calculus.ListProd
public import FQFP.Analysis.Normed.Algebra.RealScalar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Main theorem: commutator scaling of Trotter error

The main theorems of *A Theory of Trotter Error* (arXiv:1912.08854): the norm bound for the
additive kernel `𝒯(τ)` and the commuting-scaling bounds for the Trotter error
`thm:trotter_error_comm_scaling`.

Real scalars are supplied by the canonical extension of the complete normed `ℚ`-algebra
(`open scoped RealScalar`), rather than a separate real-algebra hypothesis.

`CommutatorScaling.lean` supplies `αCommConj_sum_le_αComm` (`papers/rep.tex` lines 129–139),
the additive-kernel expansion, and the order-condition cancellation
`additiveKernel_eq_commutatorRemainder_sum` (`papers/theory.tex` lines 251–266).
The explicit multi-step bounds and sufficient step counts are proved below.

## Main results

* `trotter_error_bound_comm_scaling`, `trotter_error_bound_comm_scaling_of_skewAdjoint`:
  pointwise additive-error bounds for general and skew-adjoint summands.
* `multiplicative_error_bound_comm_scaling`,
  `multiplicative_error_bound_comm_scaling_of_skewAdjoint`: the corresponding multiplicative bounds.
* `trotter_error_bound_comm_scaling_pow`: the error after repeated equal steps.
* `trotter_error_le_of_comm_scaling_rpow_le`, `trotter_error_le_of_comm_scaling_ceil_le`:
  sufficient real-power and natural-number step counts.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open TrotterError.List
open ProductFormulaData
open scoped Topology BigOperators algebraMap RealScalar

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-! ### R3: the skew-adjoint norm bound -/

/-- Shared skeleton of the additive-kernel norm bound (`thm:trotter_error_order_cond`): from
per-remainder bounds `‖remᵢ(−τ)‖ ≤ αᵢ · C` and `‖rem_all(−τ)‖ ≤ α_all · C` with `0 ≤ C`, and the
coefficient bound `Σᵢ αᵢ + α_all ≤ 2 Υ Σ_γ α_γ`, conclude
`‖additiveKernel P H τ‖ ≤ 2 Υ (Σ_γ α_γ) · C`. -/
lemma norm_additiveKernel_le_of_rem_bound
    [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrem_i : ∀ i : Fin Υ × Fin Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
    (hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤
        αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C)
    (hcoeff : (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
        + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
        ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) :
    ‖additiveKernel P H τ‖ ≤
      2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by
  have hR2 := additiveKernel_eq_commutatorRemainder_sum P H p hp h_order τ
  calc
    ‖additiveKernel P H τ‖
        = ‖(∑ i : Fin Υ × Fin Γ,
              commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
            - commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ := by
              rw [hR2]
    _ ≤ ‖∑ i : Fin Υ × Fin Γ,
            commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          + ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ :=
              norm_sub_le _ _
    _ ≤ (∑ i : Fin Υ × Fin Γ,
            ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
          + ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ := by
              gcongr
              exact norm_sum_le univ
                (fun i => commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
    _ ≤ (∑ i : Fin Υ × Fin Γ,
            αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C := by
              refine add_le_add (sum_le_sum (fun i _ => hrem_i i)) hrem_all
    _ = ((∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p) * C := by
              rw [← sum_mul, ← add_mul]
    _ ≤ (2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) * C :=
              mul_le_mul_of_nonneg_right hcoeff hC
    _ = 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by ring

/-- `thm:trotter_error_order_cond` (anti-Hermitian branch): the spectral norm of the additive
kernel is bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p!`. -/
theorem norm_additiveKernel_le_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < Υ) (τ : ℝ) :
    ‖additiveKernel P H τ‖ ≤
      2 * (Υ : ℝ) * (∑ γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) := by
  have h_skew_suffix : ∀ i k, star (suffixGenerators P H i k) = -(suffixGenerators P H i k) := by
    intro i k
    exact star_generator_of_skew P H h_skew
      (((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).get k)
  have h_skew_ordered : ∀ k, star (orderedGenerators P H k) = -(orderedGenerators P H k) := by
    intro k
    exact star_generator_of_skew P H h_skew ((evalIndexList Υ Γ).get k)
  have hrem_i : ∀ i : Fin Υ × Fin Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p *
          (|τ| ^ p / (Nat.factorial p : ℝ)) := by
    intro i
    simpa [abs_neg, div_eq_mul_inv, mul_assoc] using
      norm_commutatorRemainder_le_of_skewAdjoint (suffixGenerators P H i) (P.generator H i) p
        (-τ) (h_skew_suffix i)
  have hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p *
        (|τ| ^ p / (Nat.factorial p : ℝ)) := by
    simpa [abs_neg, div_eq_mul_inv, mul_assoc] using
      norm_commutatorRemainder_le_of_skewAdjoint (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
        (-τ) h_skew_ordered
  simpa [div_eq_mul_inv, mul_assoc] using
    norm_additiveKernel_le_of_rem_bound P H p hp h_order τ (|τ| ^ p / (Nat.factorial p : ℝ))
      (by positivity) hrem_i hrem_all (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g: the general-operator norm bound -/

/-- `thm:trotter_error_comm_scaling` (general branch): the spectral norm of the additive kernel is
bounded by `2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(2|τ| Υ Σ ‖H_γ‖)`. -/
theorem norm_additiveKernel_le
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) (τ : ℝ) :
    ‖additiveKernel P H τ‖ ≤
      2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (2 * |τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let N : ℝ := (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖
  let C : ℝ := |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N)
  have hrem_i : ∀ i : Fin Υ × Fin Γ,
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
    intro i
    have hsum : (∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
        ‖suffixGenerators P H i k‖) ≤ N := sum_norm_suffixGenerators_le P H i
    have hexp : Real.exp (2 * |τ| *
        ∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
          ‖suffixGenerators P H i k‖) ≤ Real.exp (2 * |τ| * N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity))
    calc
      ‖commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| *
                ∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
                  ‖suffixGenerators P H i k‖) := by
              simpa [abs_neg] using
                norm_commutatorRemainder_le (suffixGenerators P H i) (P.generator H i) p (-τ)
      _ ≤ αCommConj (suffixGenerators P H i) (P.generator H i) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N) := by
              exact mul_le_mul_of_nonneg_left hexp
                (div_nonneg (mul_nonneg
                  (αCommConj_nonneg (suffixGenerators P H i) (P.generator H i) p)
                  (pow_nonneg (abs_nonneg τ) p)) (Nat.cast_nonneg _))
      _ = αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
              dsimp [C]
              ring_nf
  have hrem_all : ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C := by
    have hsum : (∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) ≤ N :=
      sum_norm_orderedGenerators_le P H
    have hexp :
        Real.exp (2 * |τ| * ∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) ≤
        Real.exp (2 * |τ| * N) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by positivity))
    calc
      ‖commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖
          ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| *
                ∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) := by
              simpa [abs_neg] using
                norm_commutatorRemainder_le (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)
      _ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * |τ| ^ p /
              (Nat.factorial p : ℝ) * Real.exp (2 * |τ| * N) := mul_le_mul_of_nonneg_left hexp
                (div_nonneg (mul_nonneg
                  (αCommConj_nonneg (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p)
                  (pow_nonneg (abs_nonneg τ) p)) (Nat.cast_nonneg _))
      _ = αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C := by
              dsimp [C]
              ring_nf
  have hC : 0 ≤ C := by positivity
  simpa [C, N, div_eq_mul_inv, mul_assoc] using
    norm_additiveKernel_le_of_rem_bound P H p hp h_order τ C hC hrem_i hrem_all
      (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g-residual: the telescoped residual bound -/

/-- The single suffix-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)` (rep.tex:50–113). -/
lemma norm_eval_mul_commutatorRemainderTerm_le
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (p : ℕ)
    (j : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length)
    (q : Fin (j + 1) → ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖P.eval H τ * commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖ ≤
      ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
          (P.generator H i)‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (|τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let Cprefix : ℝ := (((evalIndexList Υ Γ).take ((evalIndexList Υ Γ).idxOf i)).map
    (fun j => ‖H (P.perm j.1 j.2)‖)).sum + ‖H (P.perm i.1 i.2)‖
  have hL : ‖prefixFactorProd P H i τ * P.evalFactor H i τ‖ ≤ Real.exp (|τ| * Cprefix) :=
    norm_prefixFactorProd_mul_evalFactor_le P H i τ
  have hdecomp : P.eval H τ = (prefixFactorProd P H i τ * P.evalFactor H i τ) *
      (List.ofFn (fun k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length =>
        exp (τ • suffixGenerators P H i k))).prod := by
    rw [← strictSuffixFactorProd_eq_prod_suffixGenerators]
    exact eval_eq_prefix_mul_evalFactor_mul_strictSuffix P H i τ
  have hCsum :
      Cprefix + (∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
      ‖suffixGenerators P H i k‖) ≤ (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ :=
    prefix_point_suffix_norm_sum_le P H i
  have hterm := norm_mul_commutatorRemainderTerm_le (A := suffixGenerators P H i)
    (B := P.generator H i) (L := prefixFactorProd P H i τ * P.evalFactor H i τ) (C := Cprefix)
    (p := p) (j := j) (q := q) (τ := τ) hτ hq hlast hL
  calc
    ‖P.eval H τ * commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖
        = ‖(prefixFactorProd P H i τ * P.evalFactor H i τ) *
            (List.ofFn
              (fun k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length =>
              exp (τ • suffixGenerators P H i k))).prod *
            commutatorRemainderTerm (suffixGenerators P H i) (P.generator H i) (-τ) j q‖ := by
              rw [hdecomp]
    _ ≤ ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (P.generator H i)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (Cprefix + (∑ k : Fin
            ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
            ‖suffixGenerators P H i k‖))) := hterm
    _ ≤ ‖adSequence (suffixGenerators P H i ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (P.generator H i)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_le_mul_of_nonneg_left hCsum (abs_nonneg τ)])
              · positivity

/-- The single ordered-remainder summand, scaled by `P.eval H τ`, telescopes to a single exponential
`exp (|τ| · Υ · Σ ‖H γ‖)`. -/
lemma norm_eval_mul_commutatorRemainderTerm_ordered_le
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (j : Fin (evalIndexList Υ Γ).length) (q : Fin (j + 1) → ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hq : q ∈ finAntidiagonal (j + 1) p) (hlast : q (Fin.last j) ≠ 0) :
    ‖P.eval H τ * commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ) j q‖ ≤
      ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
          (∑ γ : Fin Γ, H γ)‖ *
        (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
        Real.exp (|τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  have hL : ‖(1 : 𝔸)‖ ≤ Real.exp (|τ| * 0) := by simp
  have hdecomp : P.eval H τ = (1 : 𝔸) * (List.ofFn (fun k : Fin (evalIndexList Υ Γ).length =>
      exp (τ • orderedGenerators P H k))).prod := by
    rw [one_mul]
    exact eval_eq_prod_orderedGenerators P H τ
  have hsum : (0 : ℝ) + (∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) ≤
      (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
    simpa using sum_norm_orderedGenerators_le P H
  have hterm := norm_mul_commutatorRemainderTerm_le (A := orderedGenerators P H)
    (B := ∑ γ : Fin Γ, H γ) (L := (1 : 𝔸)) (C := 0) (p := p) (j := j) (q := q) (τ := τ)
    hτ hq hlast hL
  calc
    ‖P.eval H τ * commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ) j q‖
        = ‖(1 : 𝔸) * (List.ofFn (fun k : Fin (evalIndexList Υ Γ).length =>
            exp (τ • orderedGenerators P H k))).prod *
            commutatorRemainderTerm (orderedGenerators P H) (∑ γ : Fin Γ, H γ) (-τ) j q‖ := by
              rw [hdecomp]
    _ ≤ ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (∑ γ : Fin Γ, H γ)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (0 + (∑ k : Fin (evalIndexList Υ Γ).length,
            ‖orderedGenerators P H k‖))) :=
          hterm
    _ ≤ ‖adSequence (orderedGenerators P H ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q
            (∑ γ : Fin Γ, H γ)‖ *
          (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) * |τ| ^ p / (Nat.factorial p : ℝ) *
          Real.exp (|τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · exact Real.exp_le_exp.mpr
                  (by nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg τ)])
              · positivity

/-- Shared skeleton of the additive-residual norm bound: from per-remainder bounds of the scaled
`P.eval H τ · remᵢ(-τ)` terms and the coefficient bound, conclude the telescoped residual bound. -/
lemma norm_additiveResidual_le_of_rem_bound
    [NormedAlgebra ℚ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (τ : ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hrem_i : ∀ i : Fin Υ × Fin Γ,
      ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
    (hrem_all : ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
        (-τ)‖ ≤ αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C)
    (hcoeff : (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
        + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
        ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) :
    ‖additiveResidual P H τ‖ ≤
      2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by
  rw [additiveResidual_eq_eval_mul_kernel P H τ]
  have hR2 := additiveKernel_eq_commutatorRemainder_sum P H p hp h_order τ
  rw [hR2, mul_sub, Finset.mul_sum]
  calc
    ‖(∑ i : Fin Υ × Fin Γ,
          P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ))
        - P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p (-τ)‖
        ≤ ‖∑ i : Fin Υ × Fin Γ,
              P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖
          + ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
              (-τ)‖ :=
              norm_sub_le _ _
    _ ≤ (∑ i : Fin Υ × Fin Γ,
            ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖)
          + ‖P.eval H τ * commutatorRemainder (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
              (-τ)‖ := by
              gcongr
              exact norm_sum_le univ
                (fun i => P.eval H τ * commutatorRemainder (suffixGenerators P H i)
                  (P.generator H i) p (-τ))
    _ ≤ (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p * C)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C := by
              refine add_le_add (sum_le_sum (fun i _ => hrem_i i)) hrem_all
    _ = ((∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p) * C := by
              rw [← sum_mul, ← add_mul]
    _ ≤ (2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p)) * C :=
              mul_le_mul_of_nonneg_right hcoeff hC
    _ = 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) * C := by ring

/-- `thm:trotter_error_comm_scaling` (general branch): the additive residual telescopes to
`2 Υ (Σ_γ α_comm) |τ|^p / p! · exp(|τ| Υ Σ ‖H_γ‖)` (rep.tex:96–113). -/
theorem norm_additiveResidual_le
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖additiveResidual P H τ‖ ≤
      2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) *
        |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let N : ℝ := (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖
  let C : ℝ := |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * N)
  have hC : 0 ≤ C := by positivity
  have hrem_i : ∀ i : Fin Υ × Fin Γ,
      ‖P.eval H τ * commutatorRemainder (suffixGenerators P H i) (P.generator H i) p (-τ)‖ ≤
        αCommConj (suffixGenerators P H i) (P.generator H i) p * C := by
    intro i
    have hbound := norm_mul_commutatorRemainder_le_of_term_bound (M := P.eval H τ)
      (A := suffixGenerators P H i) (B := P.generator H i) (p := p) (τ := -τ)
      (F := Real.exp (|τ| * N)) (by positivity) ?_
    · simpa [C, N, abs_neg, div_eq_mul_inv, mul_assoc] using hbound
    · intro j q hq
      have hqf := mem_filter.mp hq
      simpa [abs_neg, N, mul_assoc] using
        norm_eval_mul_commutatorRemainderTerm_le P H i p j q τ hτ hqf.1 hqf.2
  have hrem_all : ‖P.eval H τ * commutatorRemainder (orderedGenerators P H)
      (∑ γ : Fin Γ, H γ) p (-τ)‖ ≤
      αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p * C := by
    have hbound := norm_mul_commutatorRemainder_le_of_term_bound (M := P.eval H τ)
      (A := orderedGenerators P H) (B := ∑ γ : Fin Γ, H γ) (p := p) (τ := -τ)
      (F := Real.exp (|τ| * N)) (by positivity) ?_
    · simpa [C, N, abs_neg, div_eq_mul_inv, mul_assoc] using hbound
    · intro j q hq
      have hqf := mem_filter.mp hq
      simpa [abs_neg, N, mul_assoc] using
        norm_eval_mul_commutatorRemainderTerm_ordered_le P H p j q τ hτ hqf.1 hqf.2
  simpa [C, N, div_eq_mul_inv, mul_assoc] using
    norm_additiveResidual_le_of_rem_bound P H p hp h_order τ C hC hrem_i hrem_all
      (sum_αCommConj_suffix_add_ordered_le P H p hΥ)

/-! ### R3g-final: pointwise and asymptotic commuting-scaling bounds -/

/-- The additive error as an integral of the additive residual (the unfactored form of
`errorType_additive`). -/
lemma eval_sub_exp_eq_integral_residual
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (t : ℝ) :
    P.eval H t - exp (t • ∑ γ : Fin Γ, H γ) =
      ∫ τ in 0..t, exp ((t - τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ := by
  have h := errorType_additive P H t
  rw [h, add_sub_cancel_left]
  refine intervalIntegral.integral_congr_uIoo ?_
  intro τ _
  change exp ((t - τ) • (∑ γ : Fin Γ, H γ)) * P.eval H τ * additiveKernel P H τ =
    exp ((t - τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ
  rw [mul_assoc, additiveResidual_eq_eval_mul_kernel P H τ]

/-- `thm:trotter_error_comm_scaling` (general branch): the explicit pointwise commuting-scaling
bound with the exponential prefactor `exp (2 t Υ Σ ‖H_γ‖)`. -/
theorem trotter_error_bound_comm_scaling
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let S : 𝔸 := ∑ γ : Fin Γ, H γ
  let N : ℝ := ∑ γ : Fin Γ, ‖H γ‖
  let sAlpha : ℝ := ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (Υ : ℝ) * sAlpha
  have hS_le : ‖S‖ ≤ N := norm_sum_le univ H
  have hR3 : ∀ τ, 0 ≤ τ → ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (|τ| * (Υ : ℝ) * N) := by
    intro τ hτ
    simpa [C, sAlpha, N] using norm_additiveResidual_le P H p hp h_order hΥ τ hτ
  intro t ht
  calc
    ‖P.eval H t - exp (t • S)‖
        = ‖∫ τ in 0..t, exp ((t - τ) • S) * additiveResidual P H τ‖ := by
            rw [eval_sub_exp_eq_integral_residual P H t]
    _ ≤ (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
      have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
          ‖exp ((t - τ) • S) * additiveResidual P H τ‖ ≤
            C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (Υ : ℝ) * N) := by
        intro τ hτ
        have hτpos : 0 ≤ τ := le_of_lt hτ.1
        have hexpS : ‖exp ((t - τ) • S)‖ ≤ Real.exp (|t - τ| * N) := by
          calc
            ‖exp ((t - τ) • S)‖ ≤ Real.exp (‖(t - τ) • S‖) := FQFP.norm_exp_le _
            _ = Real.exp (|t - τ| * ‖S‖) := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ Real.exp (|t - τ| * N) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS_le (abs_nonneg _))
        have hres : ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
            Real.exp (|τ| * (Υ : ℝ) * N) := hR3 τ hτpos
        have harg : |t - τ| * N + |τ| * (Υ : ℝ) * N ≤ 2 * t * (Υ : ℝ) * N := by
          have hN : 0 ≤ N := sum_nonneg (fun γ _ => norm_nonneg _)
          have hΥR : 1 ≤ (Υ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hΥ)
          have harg' : |t - τ| + |τ| * (Υ : ℝ) ≤ 2 * t * (Υ : ℝ) := by
            rw [abs_of_nonneg hτpos, abs_of_nonneg (sub_nonneg.mpr hτ.2)]
            nlinarith [hτ.1.le, hτ.2, hΥR, ht]
          nlinarith [mul_le_mul_of_nonneg_left harg' hN]
        calc
          ‖exp ((t - τ) • S) * additiveResidual P H τ‖
              ≤ ‖exp ((t - τ) • S)‖ * ‖additiveResidual P H τ‖ := norm_mul_le _ _
          _ ≤ Real.exp (|t - τ| * N) * (C * |τ| ^ p / (Nat.factorial p : ℝ) *
                Real.exp (|τ| * (Υ : ℝ) * N)) :=
                mul_le_mul hexpS hres (norm_nonneg _) (Real.exp_pos _).le
          _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * (Real.exp (|t - τ| * N) *
                Real.exp (|τ| * (Υ : ℝ) * N)) := by ring
          _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|t - τ| * N +
                |τ| * (Υ : ℝ) * N) := by rw [← Real.exp_add]
          _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (Υ : ℝ) * N) := by
                refine mul_le_mul_of_nonneg_left ?_ ?_
                · exact Real.exp_le_exp.mpr harg
                · have hC_nonneg : 0 ≤ C := mul_nonneg
                    (mul_nonneg zero_le_two (Nat.cast_nonneg _))
                      (sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _))
                  positivity
      exact norm_intervalIntegral_le_const_mul_abs_pow_div_factorial_mul _ C
        (Real.exp (2 * t * (Υ : ℝ) * N)) p t ht hpoint
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (Υ : ℝ) * N) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                Real.exp (2 * t * (Υ : ℝ) * N) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (Υ : ℝ) * N) *
                  (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  = (C / (Nat.factorial p : ℝ)) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                      Real.exp (2 * t * (Υ : ℝ) * N)) := by ring
              _ ≤ (2 * (Υ : ℝ) ^ (p + 1) * αComm p H) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                    Real.exp (2 * t * (Υ : ℝ) * N)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
                    Real.exp (2 * t * (Υ : ℝ) * N) := by ring

/-- `thm:trotter_error_comm_scaling` (general branch): the commuting-scaling bound as `t → ∞`. -/
theorem trotter_error_comm_scaling
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1) *
        Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1))) (Real.exp_pos _).le)]
  calc
    ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
            Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) :=
            trotter_error_bound_comm_scaling P H p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
          (αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)) := by ring

/-! ### R4: commuting-scaling bound and Trotter number -/

/-- `eq:trotter_error_comm_scaling_bound` (anti-Hermitian): the explicit pointwise commuting-scaling
bound, valid for all `t ≥ 0`. -/
theorem trotter_error_bound_comm_scaling_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
  let S : 𝔸 := ∑ γ : Fin Γ, H γ
  let sAlpha : ℝ := ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (Υ : ℝ) * sAlpha
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hR3 : ∀ τ, ‖additiveKernel P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := by
    intro τ
    simpa [C, sAlpha] using norm_additiveKernel_le_of_skewAdjoint P H h_skew p hp h_order hΥ τ
  intro t ht
  calc
    ‖P.eval H t - exp (t • S)‖
        = ‖exp (t • S) * ∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ := by
            rw [eval_sub_exp_eq_exp_mul_integral P H t]
    _ = ‖∫ τ in 0..t, (exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ :=
          CStarRing.norm_mem_unitary_mul _ (exp_smul_mem_unitary_of_skewAdjoint hS_skew t)
    _ ≤ (C / (Nat.factorial p : ℝ)) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
      have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
          ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖ ≤
            C * |τ| ^ p / (Nat.factorial p : ℝ) := by
        intro τ _
        calc
          ‖(exp ((-τ) • S) * P.eval H τ) * additiveKernel P H τ‖
              = ‖additiveKernel P H τ‖ := CStarRing.norm_mem_unitary_mul _
                ((unitary 𝔸).mul_mem (exp_smul_mem_unitary_of_skewAdjoint hS_skew (-τ))
                  (P.eval_mem_unitary_of_skewAdjoint H h_skew τ))
          _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) := hR3 τ
      simpa only [mul_one] using
        norm_intervalIntegral_le_const_mul_abs_pow_div_factorial_mul _ C 1 p t ht
          (by simpa only [mul_one] using hpoint)
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ t ^ (p + 1) / ((p + 1 : ℕ) : ℝ) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              C / (Nat.factorial p : ℝ) * (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  ≤ 2 * (Υ : ℝ) ^ (p + 1) * αComm p H *
                      (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
                      ring

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian): the commuting-scaling bound as `t → ∞`. -/
theorem trotter_error_comm_scaling_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < Υ) :
    (fun t : ℝ ↦ ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1)))]
  calc
    ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) :=
            trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) * (αComm p H * t ^ (p + 1)) := by ring

/-! ### R3g-multiplicative: the multiplicative error commuting-scaling bound -/

/-- The multiplicative error as an integral of the additive residual (rep.tex:115-123):
`ℳ(t) = ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. Follows from `errorType_multiplicative` together with the additive
representation `𝒮(t) − e^{tH} = e^{tH} ∫₀ᵗ e^{-τH} ℛ(τ) dτ`. -/
lemma multiplicativeError_eq_integral_residual
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (t : ℝ) :
    multiplicativeError P H t =
      ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ := by
  have hM : P.eval H t - exp (t • (∑ γ : Fin Γ, H γ)) =
      exp (t • (∑ γ : Fin Γ, H γ)) * multiplicativeError P H t := by
    rw [errorType_multiplicative P H t]
    noncomm_ring
  have hR : P.eval H t - exp (t • (∑ γ : Fin Γ, H γ)) =
      exp (t • (∑ γ : Fin Γ, H γ)) *
        ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ := by
    rw [eval_sub_exp_eq_exp_mul_integral P H t]
    congr 1
    refine intervalIntegral.integral_congr_uIoo ?_
    intro τ _
    change exp ((-τ) • (∑ γ : Fin Γ, H γ)) * P.eval H τ * additiveKernel P H τ =
      exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ
    rw [mul_assoc, additiveResidual_eq_eval_mul_kernel P H τ]
  have he : exp ((-t) • (∑ γ : Fin Γ, H γ)) * exp (t • (∑ γ : Fin Γ, H γ)) = 1 := by
    simpa [neg_smul] using exp_neg_mul_self (t • (∑ γ : Fin Γ, H γ))
  calc
    multiplicativeError P H t
        = exp ((-t) • (∑ γ : Fin Γ, H γ)) *
            (exp (t • (∑ γ : Fin Γ, H γ)) * multiplicativeError P H t) := by
            rw [← mul_assoc, he, one_mul]
    _ = exp ((-t) • (∑ γ : Fin Γ, H γ)) * (P.eval H t - exp (t • (∑ γ : Fin Γ, H γ))) := by
            rw [hM.symm]
    _ = exp ((-t) • (∑ γ : Fin Γ, H γ)) * (exp (t • (∑ γ : Fin Γ, H γ)) *
            ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ) := by
            rw [hR]
    _ = ∫ τ in 0..t, exp ((-τ) • (∑ γ : Fin Γ, H γ)) * additiveResidual P H τ := by
            rw [← mul_assoc, he, one_mul]

/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the explicit pointwise
commuting-scaling bound for the multiplicative error with exponential prefactor
`exp (2 t Υ Σ ‖H_γ‖)`. -/
theorem multiplicative_error_bound_comm_scaling
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖multiplicativeError P H t‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let S : 𝔸 := ∑ γ : Fin Γ, H γ
  let N : ℝ := ∑ γ : Fin Γ, ‖H γ‖
  let sAlpha : ℝ := ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p
  let C : ℝ := 2 * (Υ : ℝ) * sAlpha
  have hS_le : ‖S‖ ≤ N := norm_sum_le univ H
  have hres : ∀ τ, 0 ≤ τ → ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
      Real.exp (|τ| * (Υ : ℝ) * N) := by
    intro τ hτ
    simpa [C, sAlpha, N] using norm_additiveResidual_le P H p hp h_order hΥ τ hτ
  intro t ht
  calc
    ‖multiplicativeError P H t‖
        = ‖∫ τ in 0..t, exp ((-τ) • S) * additiveResidual P H τ‖ := by
            rw [multiplicativeError_eq_integral_residual P H t]
    _ ≤ (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (Υ : ℝ) * N) *
          (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) := by
      have hpoint : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
          ‖exp ((-τ) • S) * additiveResidual P H τ‖ ≤
            C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (Υ : ℝ) * N) := by
        intro τ hτ
        have hτpos : 0 ≤ τ := le_of_lt hτ.1
        have hexpS : ‖exp ((-τ) • S)‖ ≤ Real.exp (|τ| * N) := by
          calc
            ‖exp ((-τ) • S)‖ ≤ Real.exp (‖(-τ) • S‖) := FQFP.norm_exp_le _
            _ = Real.exp (|τ| * ‖S‖) := by rw [norm_smul, Real.norm_eq_abs, abs_neg]
            _ ≤ Real.exp (|τ| * N) :=
                Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hS_le (abs_nonneg _))
        have hresτ : ‖additiveResidual P H τ‖ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) *
            Real.exp (|τ| * (Υ : ℝ) * N) := hres τ hτpos
        have harg : |τ| * N + |τ| * (Υ : ℝ) * N ≤ 2 * t * (Υ : ℝ) * N := by
          have hN : 0 ≤ N := sum_nonneg (fun γ _ => norm_nonneg _)
          have hΥR : 1 ≤ (Υ : ℝ) := mod_cast (Nat.succ_le_of_lt hΥ)
          have harg' : |τ| + |τ| * (Υ : ℝ) ≤ 2 * t * (Υ : ℝ) := by
            rw [abs_of_nonneg hτpos]
            nlinarith [hτ.1.le, hτ.2, hΥR, ht]
          nlinarith [mul_le_mul_of_nonneg_left harg' hN]
        calc
          ‖exp ((-τ) • S) * additiveResidual P H τ‖
              ≤ ‖exp ((-τ) • S)‖ * ‖additiveResidual P H τ‖ := norm_mul_le _ _
          _ ≤ Real.exp (|τ| * N) * (C * |τ| ^ p / (Nat.factorial p : ℝ) *
                Real.exp (|τ| * (Υ : ℝ) * N)) :=
                mul_le_mul hexpS hresτ (norm_nonneg _) (Real.exp_pos _).le
          _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * (Real.exp (|τ| * N) *
                Real.exp (|τ| * (Υ : ℝ) * N)) := by ring
          _ = C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (|τ| * N +
                |τ| * (Υ : ℝ) * N) := by rw [← Real.exp_add]
          _ ≤ C * |τ| ^ p / (Nat.factorial p : ℝ) * Real.exp (2 * t * (Υ : ℝ) * N) := by
                refine mul_le_mul_of_nonneg_left ?_ ?_
                · exact Real.exp_le_exp.mpr harg
                · have hC_nonneg : 0 ≤ C := mul_nonneg
                    (mul_nonneg zero_le_two (Nat.cast_nonneg _))
                      (sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _))
                  exact div_nonneg (mul_nonneg hC_nonneg (pow_nonneg (abs_nonneg τ) p))
                    (Nat.cast_nonneg _)
      exact norm_intervalIntegral_le_const_mul_abs_pow_div_factorial_mul _ C
        (Real.exp (2 * t * (Υ : ℝ) * N)) p t ht hpoint
    _ ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
          Real.exp (2 * t * (Υ : ℝ) * N) := by
            have hC_le : C / (Nat.factorial p : ℝ) ≤ 2 * (Υ : ℝ) ^ (p + 1) * αComm p H := by
              simpa [C, sAlpha] using two_mul_commScaling_div_factorial_le P H p
            have hnonneg : 0 ≤ (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                Real.exp (2 * t * (Υ : ℝ) * N) := by positivity
            have h1 := mul_le_mul_of_nonneg_right hC_le hnonneg
            calc
              (C / (Nat.factorial p : ℝ)) * Real.exp (2 * t * (Υ : ℝ) * N) *
                  (t ^ (p + 1) / ((p + 1 : ℕ) : ℝ))
                  = (C / (Nat.factorial p : ℝ)) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                      Real.exp (2 * t * (Υ : ℝ) * N)) := by ring
              _ ≤ (2 * (Υ : ℝ) ^ (p + 1) * αComm p H) * ((t ^ (p + 1) / ((p + 1 : ℕ) : ℝ)) *
                    Real.exp (2 * t * (Υ : ℝ) * N)) := h1
              _ = 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
                    Real.exp (2 * t * (Υ : ℝ) * N) := by ring

/-- `thm:trotter_error_comm_scaling` (general branch, multiplicative): the multiplicative-error
commuting-scaling bound as `t → ∞`. -/
theorem multiplicative_error_comm_scaling
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ) :
    (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1) *
        Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1))) (Real.exp_pos _).le)]
  calc
    ‖multiplicativeError P H t‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) *
            Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) :=
            multiplicative_error_bound_comm_scaling P H p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
          (αComm p H * t ^ (p + 1) * Real.exp (2 * t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)) := by ring

/-- In the skew-adjoint case, the multiplicative error is the additive error left-multiplied by a
unitary, so their norms agree. -/
lemma norm_multiplicativeError_eq_norm_sub_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (t : ℝ) :
    ‖multiplicativeError P H t‖ = ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖ := by
  let S : 𝔸 := ∑ γ : Fin Γ, H γ
  have hS_skew : star S = -S := sum_skewAdjoint H h_skew
  have hrel : multiplicativeError P H t = exp (-(t • S)) * (P.eval H t - exp (t • S)) := by
    rw [mul_sub]
    have hkey : exp (-(t • S)) * P.eval H t = 1 + multiplicativeError P H t := by
      rw [errorType_multiplicative P H t, ← mul_assoc, exp_neg_mul_self (t • S), one_mul]
    rw [hkey, exp_neg_mul_self (t • S)]
    abel
  rw [hrel, ← neg_smul t S]
  exact CStarRing.norm_mem_unitary_mul _ (exp_smul_mem_unitary_of_skewAdjoint hS_skew (-t))

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the multiplicative
error pointwise commuting-scaling bound, valid for all `t ≥ 0` (no exponential prefactor). -/
theorem multiplicative_error_bound_comm_scaling_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < Υ) :
    ∀ t : ℝ, 0 ≤ t →
      ‖multiplicativeError P H t‖ ≤
        2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) := by
  intro t ht
  exact (norm_multiplicativeError_eq_norm_sub_of_skewAdjoint P H h_skew t).le.trans
    (trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ t ht)

/-- `thm:trotter_error_comm_scaling` (anti-Hermitian branch, multiplicative): the
multiplicative-error commuting-scaling bound as `t → ∞`. -/
theorem multiplicative_error_comm_scaling_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸] (H : Fin Γ → 𝔸)
    (h_skew : ∀ γ, star (H γ) = -(H γ)) (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H)
    (hΥ : 0 < Υ) :
    (fun t : ℝ ↦ ‖multiplicativeError P H t‖) =O[Filter.atTop]
      (fun t : ℝ ↦ αComm p H * t ^ (p + 1)) := by
  have hα : 0 ≤ αComm p H := αComm_nonneg p H
  refine IsBigO.of_bound (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with t ht
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (mul_nonneg hα (pow_nonneg ht (p + 1)))]
  calc
    ‖multiplicativeError P H t‖
        ≤ 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H * t ^ (p + 1) :=
            multiplicative_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp h_order hΥ t ht
    _ = (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) * (αComm p H * t ^ (p + 1)) := by ring

end TrotterError

/-! ### Repeated steps and sufficient step counts -/

namespace TrotterError

open NormedSpace ProductFormulaData
open scoped BigOperators RealScalar

variable {Υ Γ : ℕ} {𝔸 : Type*} [NormedRing 𝔸]
variable [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]
variable [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-- Explicit commutator-scaling error bound after any positive number of equal steps. -/
theorem trotter_error_bound_comm_scaling_pow
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) {r : ℕ} (hr : 0 < r) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤
      (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
        αComm p H * t ^ (p + 1) / (r : ℝ) ^ p := by
  let C := 2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1) * αComm p H
  have hstep := trotter_error_bound_comm_scaling_of_skewAdjoint P H h_skew p hp
    h_order hΥ (t / (r : ℝ)) (div_nonneg ht (Nat.cast_nonneg r))
  calc
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖
        ≤ (r : ℝ) * ‖P.eval H (t / (r : ℝ)) - exp ((t / (r : ℝ)) • ∑ γ, H γ)‖ :=
          norm_eval_pow_sub_exp_le_of_skewAdjoint P H h_skew t hr
    _ ≤ (r : ℝ) * (C * (t / (r : ℝ)) ^ (p + 1)) :=
          mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg r)
    _ = C * t ^ (p + 1) / (r : ℝ) ^ p := by
          rw [mul_left_comm (r : ℝ) C, natCast_mul_pow_div_pow_succ t r p (by positivity)]
          simp only [div_eq_mul_inv, mul_assoc]

/-- A real `p`-th root of the explicit commutator bound gives a sufficient step threshold
for accuracy `ε`. The dependence on the summands, time, stages, and accuracy is explicit. -/
theorem trotter_error_le_of_comm_scaling_rpow_le
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) {r : ℕ} (hr : 0 < r)
    (hsteps : ((2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
      αComm p H * t ^ (p + 1) / ε) ^ (1 / (p : ℝ)) ≤ (r : ℝ)) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤ ε := by
  let D := (2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) * αComm p H * t ^ (p + 1)
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg (by positivity) (αComm_nonneg p H)) (pow_nonneg ht _)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by lia)
  have hpow : D / ε ≤ (r : ℝ) ^ p := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_inv_le_iff_of_pos (div_nonneg hD hε.le) (Nat.cast_nonneg r) hp').mp
      (by simpa only [one_div] using hsteps)
  refine (trotter_error_bound_comm_scaling_pow P H h_skew p hp h_order hΥ t ht hr).trans ?_
  change D / (r : ℝ) ^ p ≤ ε
  apply (div_le_iff₀ (by positivity : 0 < (r : ℝ) ^ p)).mpr
  simpa only [mul_comm] using (div_le_iff₀ hε).mp hpow

/-- Rounding the real threshold up and taking at least one step ensures accuracy `ε`.
Every larger integer step count also works, including when `t = 0` or `αComm p H = 0`. -/
theorem trotter_error_le_of_comm_scaling_ceil_le
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ))
    (p : ℕ) (hp : 1 ≤ p) (h_order : P.IsOrderOf p H) (hΥ : 0 < Υ)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) {r : ℕ}
    (hsteps : max 1 ⌈((2 / ((p + 1 : ℕ) : ℝ) * (Υ : ℝ) ^ (p + 1)) *
      αComm p H * t ^ (p + 1) / ε) ^ (1 / (p : ℝ))⌉₊ ≤ r) :
    ‖(P.eval H (t / (r : ℝ))) ^ r - exp (t • ∑ γ, H γ)‖ ≤ ε := by
  have hr : 0 < r := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hsteps)
  apply trotter_error_le_of_comm_scaling_rpow_le P H h_skew p hp h_order hΥ t ht ε hε hr
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hsteps)

end TrotterError
