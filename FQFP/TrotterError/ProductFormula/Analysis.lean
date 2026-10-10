/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.ProductFormula.Basic
public import FQFP.TrotterError.Commutator
public import FQFP.TrotterError.Calculus

import FQFP.TrotterError.ListLemmas

/-!
# Derivatives and estimates for product formulas

Multinomial derivative expansions, norm bounds, unitary evaluation, and bounds
for commutator sums associated with the ordered generators.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset
open TrotterError.List
open scoped Topology

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]

namespace ProductFormulaData

variable (P : ProductFormulaData Υ Γ)

/-- Per-factor norm bound `‖e^{s a_{(υ,γ)} H_{π_υ(γ)}}‖ ≤ Real.exp (|s| * ‖H_{π_υ(γ)}‖)`. -/
lemma norm_evalFactor_le [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (s : ℝ) :
    ‖P.evalFactor H i s‖ ≤ Real.exp (|s| * ‖H (P.perm i.1 i.2)‖) := by
  calc
    ‖P.evalFactor H i s‖ = ‖exp (s • P.generator H i)‖ := rfl
    _ ≤ Real.exp (‖s • P.generator H i‖) := norm_exp_le _
    _ = Real.exp (|s| * ‖P.generator H i‖) := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.exp (|s| * ‖H (P.perm i.1 i.2)‖) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (P.norm_generator_le H i) (abs_nonneg s))

/-- Each factor of a product formula with skew-adjoint summands is unitary. -/
lemma evalFactor_mem_unitary_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (hskew : ∀ γ, star (H γ) = -(H γ)) (i : Fin Υ × Fin Γ) (t : ℝ) :
    P.evalFactor H i t ∈ unitary 𝔸 :=
  exp_smul_mem_unitary_of_skewAdjoint (star_smul_of_skew (hskew (P.perm i.1 i.2))) t

/-- A product formula with skew-adjoint summands evaluates to a unitary element. -/
lemma eval_mem_unitary_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [ContinuousStar 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (hskew : ∀ γ, star (H γ) = -(H γ)) (t : ℝ) :
    P.eval H t ∈ unitary 𝔸 := by
  apply (unitary 𝔸).list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact P.evalFactor_mem_unitary_of_skewAdjoint H hskew i t

/-- A product formula with skew-adjoint summands has norm one in a nontrivial C*-algebra. -/
lemma norm_eval_eq_one_of_skewAdjoint
    [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [CompleteSpace 𝔸]
    [StarRing 𝔸] [CStarRing 𝔸] [Nontrivial 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (hskew : ∀ γ, star (H γ) = -(H γ)) (t : ℝ) :
    ‖P.eval H t‖ = 1 :=
  CStarRing.norm_of_mem_unitary (P.eval_mem_unitary_of_skewAdjoint H hskew t)

/-- The `k`-th iterated derivative of a single factor `P.evalFactor H i`. -/
lemma evalFactor_iteratedDeriv [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t : ℝ => P.evalFactor H i t) t =
      P.generator H i ^ k * P.evalFactor H i t := by
  dsimp [evalFactor]
  rw [iteratedDeriv_exp_smul_const (P.generator H i) k]

/-- The `(p + 1)`-st iterated derivative of `eval`, expanded as a multinomial Leibniz sum over
multi-indices on `Fin Υ × Fin Γ` (the paper's `𝒮^{(p+1)}(ut)` expansion, prelim.tex:174–178). -/
theorem eval_iteratedDeriv_succ [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (t : ℝ) :
    iteratedDeriv (p + 1) (fun t : ℝ => P.eval H t) t =
      ∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
        (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) •
          (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
            (((List.finRange Γ).reverse).map (fun γ : Fin Γ =>
              ((P.generator H (υ, γ)) ^ (q (υ, γ))) *
                exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod := by
  let l : List (Fin Υ × Fin Γ) := evalIndexList Υ Γ
  let f : Fin Υ × Fin Γ → ℝ → 𝔸 := fun i t => P.evalFactor H i t
  have hf : ∀ i ∈ l, ContDiffAt ℝ (p + 1) (f i) t := by
    intro i _
    simpa [f, evalFactor] using contDiffAt_exp_smul_const (P.generator H i) (p + 1) t
  rw [show (fun t : ℝ => P.eval H t) = fun t : ℝ => (l.map (fun i => f i t)).prod by rfl,
    iteratedDeriv_list_prod_general l f (p + 1) t hf]
  let e : Fin l.length ≃ Fin Υ × Fin Γ := evalIndexEquiv Υ Γ
  rw [sum_piAntidiag_univ_equiv e (p + 1)
    (fun q : Fin l.length → ℕ =>
      (Nat.multinomial (univ : Finset (Fin l.length)) q : ℝ) •
        (List.ofFn (fun j : Fin l.length =>
          iteratedDeriv (q j) (f (l.get j)) t)).prod)]
  apply sum_congr rfl
  intro q' hq'
  rw [← multinomial_univ_equiv e q']
  congr 1
  have hfac : (fun i : Fin Υ × Fin Γ => iteratedDeriv (q' i) (f i) t) =
      fun i : Fin Υ × Fin Γ =>
        P.generator H i ^ (q' i) * P.evalFactor H i t := by
    funext i; rw [evalFactor_iteratedDeriv P H i (q' i) t]
  calc
    (List.ofFn (fun j : Fin l.length => iteratedDeriv ((q' ∘ e) j) (f (l.get j)) t)).prod
        = (l.map (fun i => iteratedDeriv (q' i) (f i) t)).prod := by
            congr 1
            rw [show (fun j : Fin l.length => iteratedDeriv ((q' ∘ e) j) (f (l.get j)) t) =
                fun j : Fin l.length => iteratedDeriv (q' (l.get j)) (f (l.get j)) t by
              funext j
              rw [show ((q' ∘ e) j) = q' (l.get j) by rfl]]
            simpa using (List.ofFn_getElem_eq_map l (fun i => iteratedDeriv (q' i) (f i) t))
    _ = (l.map (fun i => P.generator H i ^ (q' i) *
          P.evalFactor H i t)).prod := by rw [hfac]
    _ = (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
            (((List.finRange Γ).reverse).map (fun γ : Fin Γ =>
              P.generator H (υ, γ) ^ (q' (υ, γ)) *
                P.evalFactor H (υ, γ) t)).prod)).prod := by
            rw [evalIndexList_map_prod (fun i =>
              P.generator H i ^ (q' i) * P.evalFactor H i t)]
    _ = (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
            (((List.finRange Γ).reverse).map (fun γ : Fin Γ =>
              ((P.generator H (υ, γ)) ^ (q' (υ, γ))) *
                exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod := by
            simp [evalFactor, generator, mul_smul]

/-! ### Norm bounds for the derivative expansion (prelim.tex:182–188) -/

/-- Per-factor norm bound: `‖(a • H)^q * exp (u t a • H)‖ ≤ ‖H‖^q * Real.exp (t * ‖H‖)`
(prelim.tex:183–184). -/
lemma norm_factor_le [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (q : ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖(P.generator H i) ^ q *
        exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖
      ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖) := by
  have hA := norm_smul_le_of_abs_le_one (P.coeff i) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i)
  have harg := norm_smul_exp_arg_le (P.coeff i) (H (P.perm i.1 i.2))
    (P.coeff_abs_le_one i) u t ht hu1
  calc
    ‖(P.generator H i) ^ q *
        exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))‖
        ≤ ‖P.generator H i‖ ^ q *
            Real.exp ((u * t) * ‖P.generator H i‖) := by
            rw [mul_smul]
            exact norm_pow_mul_exp_le (P.generator H i) q (u * t)
              (mul_nonneg hu0 ht)
    _ ≤ ‖H (P.perm i.1 i.2)‖ ^ q * Real.exp (t * ‖H (P.perm i.1 i.2)‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA q) (Real.exp_le_exp.mpr harg)
          (Real.exp_nonneg _) (pow_nonneg (norm_nonneg _) q)

/-- The ordered product in `𝔸` of the `(υ, γ)`-factors `A^{q} * exp (r • A)` in `eval`'s order. -/
noncomputable def derivProd {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (q : Fin Υ × Fin Γ → ℕ) (t : ℝ) : 𝔸 :=
  (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
    (((List.finRange Γ).reverse).map (fun γ : Fin Γ =>
      ((P.generator H (υ, γ)) ^ (q (υ, γ))) *
        exp ((t * P.coeff (υ, γ)) • H (P.perm υ γ)))).prod)).prod

/-- The product over the nested `List.finRange` lists equals the `prod` over the product
index type (the reverse order is irrelevant in a commutative monoid). -/
lemma nested_prod_eq_finset_prod {M : Type*} [CommMonoid M] (f : Fin Υ × Fin Γ → M) :
    (((List.finRange Υ).reverse).map (fun υ : Fin Υ =>
      (((List.finRange Γ).reverse).map (fun γ : Fin Γ => f (υ, γ))).prod)).prod =
        ∏ i : Fin Υ × Fin Γ, f i := by
  simp only [List.map_reverse, List.prod_reverse]
  simp_rw [← Fin.prod_univ_def]
  rw [← univ_product_univ, prod_product]

/-- The norm of the product over the `(υ, γ)`-factors is bounded by the product of the per-factor
bounds `‖H_π‖^q * Real.exp (t * ‖H_π‖)`. -/
lemma norm_derivProd_le [NormedAlgebra ℚ 𝔸] [NormedSpace ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (q : Fin Υ × Fin Γ → ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖P.derivProd H q (u * t)‖ ≤
      ∏ i : Fin Υ × Fin Γ,
        ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖) := by
  let g : Fin Υ × Fin Γ → 𝔸 := fun i =>
    (P.generator H i) ^ q i *
      exp ((u * t * P.coeff i) • H (P.perm i.1 i.2))
  have hflat : P.derivProd H q (u * t) = ((evalIndexList Υ Γ).map g).prod :=
    (evalIndexList_map_prod g).symm
  calc
    ‖P.derivProd H q (u * t)‖ = ‖((evalIndexList Υ Γ).map g).prod‖ := by rw [hflat]
    _ ≤ ((evalIndexList Υ Γ).map (fun i => ‖g i‖)).prod := by
        simpa [List.map_map, Function.comp_def] using List.norm_prod_le ((evalIndexList Υ Γ).map g)
    _ = ∏ i : Fin Υ × Fin Γ, ‖g i‖ := by
        rw [evalIndexList_map_prod (fun i => ‖g i‖), nested_prod_eq_finset_prod (fun i => ‖g i‖)]
    _ ≤ ∏ i : Fin Υ × Fin Γ,
          ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖) :=
        prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => norm_factor_le P H i (q i) u t ht hu0 hu1)

/-- `∑_{i : Fin Υ × Fin Γ} ‖H_{π_{i.1}(i.2)}‖ = Υ * ∑_γ ‖H_γ‖`. -/
lemma sum_norm_prod (H : Fin Γ → 𝔸) :
    (∑ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖) = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
  calc
    (∑ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖)
        = ∑ υ : Fin Υ, ∑ γ : Fin Γ, ‖H (P.perm υ γ)‖ := by
            rw [← univ_product_univ, sum_product]
    _ = ∑ υ : Fin Υ, ∑ γ : Fin Γ, ‖H γ‖ := by
            apply sum_congr rfl
            intro υ hυ
            exact Equiv.sum_comp (P.perm υ) (fun γ => ‖H γ‖)
    _ = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `(p + 1)`-st iterated derivative norm bound (prelim.tex:182–185):
`‖𝒮^{(p+1)}(ut)‖ ≤ (Υ · Σ_γ ‖H_γ‖)^{p+1} · Real.exp (t · Υ · Σ_γ ‖H_γ‖)`. -/
theorem eval_iteratedDeriv_norm_le
    [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (u t : ℝ)
    (ht : 0 ≤ t) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖iteratedDeriv (p + 1) (fun s : ℝ => P.eval H s) (u * t)‖ ≤
      ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) *
        Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  let B : Fin Υ × Fin Γ → ℝ := fun i => ‖H (P.perm i.1 i.2)‖
  have hB : (∑ i : Fin Υ × Fin Γ, B i) = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := sum_norm_prod P H
  have hE : (∑ i : Fin Υ × Fin Γ, t * B i) = t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
    rw [← mul_sum, hB]; ring
  rw [eval_iteratedDeriv_succ]
  calc
    ‖∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
        (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) •
          P.derivProd H q (u * t)‖
        ≤ ∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
            ‖(Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) •
              P.derivProd H q (u * t)‖ := norm_sum_le _ _
    _ = ∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
            (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) *
              ‖P.derivProd H q (u * t)‖ := by
            apply sum_congr rfl
            intro q hq
            rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
            (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) *
              (∏ i : Fin Υ × Fin Γ, B i ^ q i * Real.exp (t * B i)) := by
            apply sum_le_sum
            intro q hq
            exact mul_le_mul_of_nonneg_left (norm_derivProd_le P H q u t ht hu0 hu1)
              (Nat.cast_nonneg _)
    _ = ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) *
          Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
        calc
          (∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
              (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) *
                (∏ i : Fin Υ × Fin Γ, B i ^ q i * Real.exp (t * B i)))
              = (∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
                  (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) *
                    (∏ i : Fin Υ × Fin Γ, B i ^ q i) *
                      Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖)) := by
                  apply sum_congr rfl
                  intro q hq
                  rw [prod_mul_distrib, (Real.exp_sum univ (fun i => t * B i)).symm,
                    hE]
                  ring
          _ = (∑ q ∈ piAntidiag (univ : Finset (Fin Υ × Fin Γ)) (p + 1),
                  (Nat.multinomial (univ : Finset (Fin Υ × Fin Γ)) q : ℝ) *
                    (∏ i : Fin Υ × Fin Γ, B i ^ q i)) *
                Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by rw [← sum_mul]
          _ = (∑ i : Fin Υ × Fin Γ, B i) ^ (p + 1) *
                Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
                  rw [← sum_pow_eq_sum_piAntidiag
                    (univ : Finset (Fin Υ × Fin Γ)) B (p + 1)]
          _ = ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) ^ (p + 1) *
                Real.exp (t * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by rw [hB]

end ProductFormulaData

open ProductFormulaData

variable (P : ProductFormulaData Υ Γ)

/-- `Σ_k ‖fullGenerators P H k‖ = Υ · Σ_γ ‖H γ‖`: the sum of the norms of the
coefficient-free generators (in `evalIndexList` order) is the stage count times the total
summand norm. -/
lemma sum_norm_fullGenerators_eq (H : Fin Γ → 𝔸) :
    (∑ k : Fin (evalIndexList Υ Γ).length, ‖fullGenerators P H k‖) =
      (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
  simpa only [nsmul_eq_mul] using sum_fullGenerators P H (norm : 𝔸 → ℝ)

/-- `Σ_k ‖orderedGenerators P H k‖ ≤ Υ · Σ_γ ‖H γ‖` (the coefficients `|a| ≤ 1` drop out). -/
lemma sum_norm_orderedGenerators_le [NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) :
    (∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖) ≤
      (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
  have hle : ∀ k : Fin (evalIndexList Υ Γ).length,
      ‖orderedGenerators P H k‖ ≤ ‖fullGenerators P H k‖ := by
    intro k
    unfold orderedGenerators fullGenerators ProductFormulaData.generator
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (P.coeff_abs_le_one ((evalIndexList Υ Γ).get k))
  calc
    (∑ k : Fin (evalIndexList Υ Γ).length, ‖orderedGenerators P H k‖)
        ≤ ∑ k : Fin (evalIndexList Υ Γ).length, ‖fullGenerators P H k‖ :=
            sum_le_sum (fun k _ => hle k)
    _ = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := sum_norm_fullGenerators_eq P H

/-- The norm sum of suffix generators is bounded by the coefficient-free suffix sum. -/
lemma sum_norm_suffixGenerators_le_sum [NormedAlgebra ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) :
    (∑ k, ‖suffixGenerators P H i k‖) ≤
      (((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).map
        (fun j => ‖H (P.perm j.1 j.2)‖)).sum := by
  let l := (evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)
  calc
    (∑ k, ‖suffixGenerators P H i k‖)
        ≤ ∑ k : Fin l.length, ‖H (P.perm (l.get k).1 (l.get k).2)‖ :=
            sum_le_sum (fun k _ => P.norm_generator_le H (l.get k))
    _ = (l.map (fun j => ‖H (P.perm j.1 j.2)‖)).sum :=
      sum_get_comp l (fun j => ‖H (P.perm j.1 j.2)‖)

/-- `Σ_k ‖suffixGenerators P H i k‖ ≤ Υ · Σ_γ ‖H γ‖` (a suffix of the generators, with
coefficients dropped). -/
lemma sum_norm_suffixGenerators_le [NormedAlgebra ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) :
    (∑ k : Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length,
        ‖suffixGenerators P H i k‖) ≤ (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
  calc
    (∑ k, ‖suffixGenerators P H i k‖)
        ≤ (((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).map
            (fun j => ‖H (P.perm j.1 j.2)‖)).sum := sum_norm_suffixGenerators_le_sum P H i
    _ ≤ ((evalIndexList Υ Γ).map (fun j => ‖H (P.perm j.1 j.2)‖)).sum := by
      refine ((List.drop_sublist _ (evalIndexList Υ Γ)).map
        (fun j => ‖H (P.perm j.1 j.2)‖)).sum_le_sum ?_
      intro a ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      exact norm_nonneg _
    _ = (Υ : ℝ) * ∑ γ, ‖H γ‖ := by rw [sum_evalIndexList, P.sum_norm_prod H]

/-- The norm of the product formula is bounded by `exp (|s| · Υ · Σ ‖H γ‖)`: each factor
`e^{s a H}` has norm at most `exp (|s| ‖H‖)`, and the coefficient `|a| ≤ 1` drops out. -/
lemma norm_eval_le [NormedAlgebra ℚ 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸]
    (H : Fin Γ → 𝔸) (s : ℝ) :
    ‖P.eval H s‖ ≤ Real.exp (|s| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
  calc
    ‖P.eval H s‖ = ‖((evalIndexList Υ Γ).map (fun i => P.evalFactor H i s)).prod‖ := rfl
    _ ≤ ((evalIndexList Υ Γ).map (fun i => ‖P.evalFactor H i s‖)).prod := by
            simpa [List.map_map, Function.comp_def] using
              List.norm_prod_le ((evalIndexList Υ Γ).map (fun i => P.evalFactor H i s))
    _ ≤ ((evalIndexList Υ Γ).map (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))).prod := by
            refine List.prod_map_le_prod_map₀ (f := fun i => ‖P.evalFactor H i s‖)
              (g := fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖)) (s := evalIndexList Υ Γ) ?_ ?_
            · intro i _
              exact norm_nonneg _
            · intro i _
              exact P.norm_evalFactor_le H i s
    _ = ∏ i : Fin Υ × Fin Γ, Real.exp (|s| * ‖H (P.perm i.1 i.2)‖) := by
            rw [evalIndexList_map_prod (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))]
            rw [ProductFormulaData.nested_prod_eq_finset_prod
              (fun i => Real.exp (|s| * ‖H (P.perm i.1 i.2)‖))]
    _ = Real.exp (|s| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by
            rw [(Real.exp_sum (univ : Finset (Fin Υ × Fin Γ))
              (fun i => |s| * ‖H (P.perm i.1 i.2)‖)).symm]
            congr 1
            calc
              (∑ i : Fin Υ × Fin Γ, |s| * ‖H (P.perm i.1 i.2)‖)
                  = |s| * ∑ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖ := by rw [← mul_sum]
              _ = |s| * ((Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖) := by rw [P.sum_norm_prod H]
              _ = |s| * (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by ring

/-- `∑_i αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p = Υ · ∑_γ …`. -/
lemma sum_αCommConj_perm [Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (p : ℕ) :
    (∑ i : Fin Υ × Fin Γ, αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p)
      = (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
  rw [← univ_product_univ, sum_product]
  rw [sum_congr rfl (fun υ _ => Equiv.sum_comp (P.perm υ)
    (fun γ => αCommConj (orderedSummandsEval P H) (H γ) p))]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `star (P.generator H j) = -(P.generator H j)` whenever each `H γ` is anti-Hermitian. -/
lemma star_generator_of_skew [NormedSpace ℝ 𝔸] [Star 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (j : Fin Υ × Fin Γ) :
    star (P.generator H j) = -(P.generator H j) := by
  unfold ProductFormulaData.generator
  exact star_smul_of_skew (h_skew (P.perm j.1 j.2))

/-- Transport multiplicities to the evaluation list without changing the ordered commutator. -/
lemma adSequence_fullGenerators_eq [Algebra ℝ 𝔸] (H : Fin Γ → 𝔸)
    (q : Fin (Υ * Γ) → ℕ) (B : 𝔸) :
    adSequence (fullGenerators P H) (fun i => q (Fin.cast evalIndexList_length i)) B =
      adSequence (orderedSummandsEval P H) q B := by
  have h := adSequence_cast evalIndexList_length (fullGenerators P H)
    (fun i => q (Fin.cast evalIndexList_length i)) B
  simpa [fullGenerators_eq_orderedSummandsEval P H] using h.symm

/-- `αCommConj` of `fullGenerators` equals that of `orderedSummandsEval`. -/
lemma αCommConj_fullGenerators_eq [Algebra ℝ 𝔸] (H : Fin Γ → 𝔸) (B : 𝔸) (p : ℕ) :
    αCommConj (fullGenerators P H) B p = αCommConj (orderedSummandsEval P H) B p := by
  have hlen : (evalIndexList Υ Γ).length = Υ * Γ := evalIndexList_length
  calc
    αCommConj (fullGenerators P H) B p
        = αCommConj
            (fun i : Fin (Υ * Γ) => fullGenerators P H (Fin.cast hlen.symm i)) B p :=
            (αCommConj_cast hlen (fullGenerators P H) B p).symm
    _ = αCommConj (orderedSummandsEval P H) B p := by
            rw [fullGenerators_eq_orderedSummandsEval P H]

/-- Dropping the coefficients of `orderedGenerators` does not increase `αCommConj`. -/
lemma αCommConj_orderedGenerators_le [NormedAlgebra ℝ 𝔸]
    (H : Fin Γ → 𝔸) (B : 𝔸) (p : ℕ) :
    αCommConj (orderedGenerators P H) B p ≤ αCommConj (fullGenerators P H) B p := by
  have hord : orderedGenerators P H =
      fun k : Fin (evalIndexList Υ Γ).length =>
        P.coeff ((evalIndexList Υ Γ).get k) • fullGenerators P H k := by
    funext k
    simp [orderedGenerators, fullGenerators, ProductFormulaData.generator]
  rw [hord]
  exact αCommConj_smul_fun_le
    (fun k : Fin (evalIndexList Υ Γ).length => P.coeff ((evalIndexList Υ Γ).get k))
    (fullGenerators P H) (fun k => P.coeff_abs_le_one ((evalIndexList Υ Γ).get k)) B p

/-- Dropping the coefficients and extending the suffix to the full list does not increase
`αCommConj` of the suffix generators. -/
lemma αCommConj_suffixGenerators_le [NormedAlgebra ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (p : ℕ) :
    αCommConj (suffixGenerators P H i) (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
  let drop := (evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)
  let suffixFull : Fin drop.length → 𝔸 := fun k => H (P.perm (drop.get k).1 (drop.get k).2)
  have h1 : αCommConj (suffixGenerators P H i) (P.generator H i) p
      ≤ αCommConj suffixFull (P.generator H i) p := by
    have hsuffix : suffixGenerators P H i =
        fun k : Fin drop.length => P.coeff (drop.get k) • suffixFull k := by
      funext k
      simp [suffixGenerators, suffixFull, drop, ProductFormulaData.generator]
    rw [hsuffix]
    exact αCommConj_smul_fun_le (fun k : Fin drop.length => P.coeff (drop.get k)) suffixFull
      (fun k => P.coeff_abs_le_one (drop.get k)) (P.generator H i) p
  have h2 : αCommConj suffixFull (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (P.generator H i) p :=
    αCommConj_get_drop_le (evalIndexList Υ Γ) (fun j => H (P.perm j.1 j.2))
      ((evalIndexList Υ Γ).idxOf i + 1) (P.generator H i) p
  have h3 : αCommConj (fullGenerators P H) (P.generator H i) p
      ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
    simpa [ProductFormulaData.generator] using
      (αCommConj_smul_le (fullGenerators P H) (P.coeff i) (P.coeff_abs_le_one i)
        (H (P.perm i.1 i.2)) p)
  calc
    αCommConj (suffixGenerators P H i) (P.generator H i) p
        ≤ αCommConj suffixFull (P.generator H i) p := h1
    _ ≤ αCommConj (fullGenerators P H) (P.generator H i) p := h2
    _ ≤ αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := h3

/-- The sum of the conjugation scalings of the suffix generators and of the full ordered
generators is bounded by `2 · Υ · Σ_γ α_comm(H, H_γ)`: the coefficient-drop, suffix-extension,
permutation-reindexing, and `ΣH`-splitting steps shared by both branches of the additive-kernel
norm bound. -/
lemma sum_αCommConj_suffix_add_ordered_le [NormedAlgebra ℝ 𝔸]
    (H : Fin Γ → 𝔸) (p : ℕ) (hΥ : 0 < Υ) :
    (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
      + αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
      ≤ 2 * (Υ : ℝ) * (∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p) := by
  have hsum_i :
      (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
      ≤ (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
    calc
      (∑ i : Fin Υ × Fin Γ, αCommConj (suffixGenerators P H i) (P.generator H i) p)
          ≤ ∑ i : Fin Υ × Fin Γ,
              αCommConj (fullGenerators P H) (H (P.perm i.1 i.2)) p := by
              gcongr with i
              exact αCommConj_suffixGenerators_le P H i p
      _ = ∑ i : Fin Υ × Fin Γ,
            αCommConj (orderedSummandsEval P H) (H (P.perm i.1 i.2)) p := by
              apply sum_congr rfl
              intro i _
              exact αCommConj_fullGenerators_eq P H (H (P.perm i.1 i.2)) p
      _ = (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
              sum_αCommConj_perm P H p
  have hordered : αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
      ≤ (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
    calc
      αCommConj (orderedGenerators P H) (∑ γ : Fin Γ, H γ) p
          ≤ αCommConj (fullGenerators P H) (∑ γ : Fin Γ, H γ) p :=
              αCommConj_orderedGenerators_le P H (∑ γ : Fin Γ, H γ) p
      _ = αCommConj (orderedSummandsEval P H) (∑ γ : Fin Γ, H γ) p :=
              αCommConj_fullGenerators_eq P H (∑ γ : Fin Γ, H γ) p
      _ ≤ ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
              αCommConj_sum_le (orderedSummandsEval P H) H p
      _ ≤ (Υ : ℝ) * ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p := by
              have h1 : (1 : ℝ) ≤ (Υ : ℝ) := mod_cast hΥ
              have hnonneg : 0 ≤ ∑ γ : Fin Γ, αCommConj (orderedSummandsEval P H) (H γ) p :=
                sum_nonneg (fun γ _ => αCommConj_nonneg _ _ _)
              simpa using mul_le_mul_of_nonneg_right h1 hnonneg
  linarith

end TrotterError
