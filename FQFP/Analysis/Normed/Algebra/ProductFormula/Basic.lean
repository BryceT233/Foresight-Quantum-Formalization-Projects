/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
import FQFP.Analysis.Calculus.ListProd
public import Mathlib.Analysis.Asymptotics.Defs
public import FQFP.Analysis.Normed.Algebra.ProductFormula.Commutator
public import FQFP.Analysis.Normed.Algebra.ExponentialCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Product formulas

We define the general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of arXiv:1912.08854 (§2.3), its operations and estimates.
This file also defines the `p`-th order condition and the standard Suzuki constructions.

Following the paper's convention (`papers/prelim.tex` §2.1), the product
`∏_{γ=1}^{Γ} A_γ` denotes `A_Γ ⋯ A_2 A_1`, i.e. increasing indices from right to
left; we implement this with a reversed `List.finRange`. Since the factors
`e^{t a H}` do not commute, the product is taken with `List.prod` (ordered) rather
than `prod` (commutative) or `noncommProd` (which requires pairwise
commutativity).

## Main definitions

* `ProductFormulaData`: the data of a product formula `𝒮(t)` (stages `Υ`, summands `Γ`,
  coefficients `coeff`, permutations `perm`).
* `evalFactor`, `eval`, `generator`: the single factor, the full product, and the generator
  `a_{(υ,γ)} H_{π_υ(γ)}`.
* `evalIndexList`: the flattened factor-index order used by `eval`.
* `orderedSummands`, `orderedSummandsEval`: coefficient-free summands in canonical and evaluation
  order, respectively. `reverseStages` relates these orders without changing coefficients.
* `orderedGenerators`, `suffixGenerators`, `fullGenerators`: the generators of the product
  formula in `evalIndexList` order.
* `ProductFormulaData.IsOrderOf`: approximation order at time zero.
* `lieTrotter`, `suzuki2`, `suzuki`: the standard first-, second-, and higher-order formulas.
* `lieTrotterData`, `suzuki2Data`, `suzukiData`: their product-formula data.

## Main results

* `ProductFormulaData.eval_iteratedDeriv_succ`: the `(p + 1)`-st iterated derivative
  of `eval`, expanded as a multinomial Leibniz sum over `Fin Υ × Fin Γ`.
* `evalIndexList_eq_ofFn`, `evalIndexList_length`: the flattened index list as `List.ofFn`.
* `lieTrotter_eq_eval`, `suzuki2_eq_eval`, `suzuki_eq_eval`: agreement of the standard formulas
  with their product-formula data.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Finset
open TrotterError.List
open scoped Topology

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The data of a general product formula `𝒮(t) = ∏_{υ=1}^{Υ} ∏_{γ=1}^{Γ}
e^{t a_{(υ,γ)} H_{π_υ(γ)}}` (`eq:pf`): `Υ` stages, `Γ` summands, real coefficients
`a_{(υ,γ)}` uniformly bounded by `1` in absolute value, and per-stage permutations
`π_υ`. -/
structure ProductFormulaData (Υ Γ : ℕ) where
  /-- Real coefficients `a_{(υ,γ)}`. -/
  coeff : Fin Υ × Fin Γ → ℝ
  /-- Permutation `π_υ` of the summands within stage `υ`. -/
  perm : Fin Υ → Equiv.Perm (Fin Γ)
  /-- The coefficients are uniformly bounded by `1` in absolute value. -/
  coeff_abs_le_one : ∀ i : Fin Υ × Fin Γ, |coeff i| ≤ 1

namespace ProductFormulaData

variable (P : ProductFormulaData Υ Γ)

/-- The flattened list of factor indices `(υ, γ)`, in `eval`'s product order: the outer `Υ`-layer
runs right-to-left and, within each stage, the inner `Γ`-layer runs right-to-left. -/
def evalIndexList (Υ Γ : ℕ) : List (Fin Υ × Fin Γ) :=
  List.product (List.finRange Υ).reverse (List.finRange Γ).reverse

/-- The `(υ,γ)`-th generator `a_{(υ,γ)} H_{π_υ(γ)}`: the coefficient-scaled, permuted summand. -/
noncomputable def generator {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) : 𝔸 :=
  P.coeff i • H (P.perm i.1 i.2)

/-- The norm of the `(υ,γ)`-th generator `a_{(υ,γ)} H_{π_υ(γ)}` is bounded by the norm of the
permuted summand `H_{π_υ(γ)}` (the coefficient has `|a| ≤ 1`). -/
lemma norm_generator_le [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) :
    ‖P.generator H i‖ ≤ ‖H (P.perm i.1 i.2)‖ := by
  unfold ProductFormulaData.generator
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (P.coeff_abs_le_one i)

/-- The `(υ, γ)`-th factor `e^{t a_{(υ,γ)} H_{π_υ(γ)}}` of the product formula. -/
noncomputable def evalFactor {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) (t : ℝ) : 𝔸 :=
  exp (t • P.generator H i)

/-- The product formula `𝒮(t)` evaluated on summands `H` at time `t`. The product
is taken in the paper's right-to-left order `∏_{γ=1}^{Γ} A_γ = A_Γ ⋯ A_1`. -/
noncomputable def eval {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  ((evalIndexList Υ Γ).map (fun i => P.evalFactor H i t)).prod

/-- The product formula at time `0` is the identity: `𝒮(0) = I`. -/
@[simp]
theorem eval_zero [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : P.eval H 0 = 1 := by simp [eval, evalFactor]

/-- The product over the flattened index list equals the nested product in `eval`'s order. -/
lemma evalIndexList_map_prod {M : Type*} [Monoid M]
    (g : Fin Υ × Fin Γ → M) : ((evalIndexList Υ Γ).map g).prod =
      (((List.finRange Υ).reverse).map (fun υ =>
        (((List.finRange Γ).reverse).map (fun γ => g (υ, γ))).prod)).prod := by
  unfold evalIndexList List.product
  rw [List.flatMap_def, List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
  congr; funext a
  simp only [Function.comp_apply, List.map_map]
  rfl

/-- Summing a per-summand observable over all permuted stages repeats its sum `Υ` times. -/
lemma sum_perm {M : Type*} [AddCommMonoid M] (f : Fin Γ → M) :
    (∑ i : Fin Υ × Fin Γ, f (P.perm i.1 i.2)) = Υ • ∑ γ, f γ := by
  rw [← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_congr rfl (fun υ _ => Equiv.sum_comp (P.perm υ) f)]
  simp

/-! ### Operations on product-formula data -/

/-- Scale all coefficients by `c` (with `|c| ≤ 1` to preserve `coeff_abs_le_one`). -/
@[reducible] def scale {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (c : ℝ) (hc : |c| ≤ 1) :
    ProductFormulaData Υ Γ where
  coeff := fun i => c * P.coeff i
  perm := P.perm
  coeff_abs_le_one := fun i => by
    rw [abs_mul]
    simpa using mul_le_mul hc (P.coeff_abs_le_one i) (abs_nonneg (P.coeff i)) zero_le_one

/-- Scaling all coefficients by `c` is evaluation at time `c * t`. -/
lemma scale_eval (c : ℝ) (hc : |c| ≤ 1) [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    (scale P c hc).eval H t = P.eval H (c * t) := by
  unfold ProductFormulaData.eval scale ProductFormulaData.evalFactor ProductFormulaData.generator
  apply congrArg List.prod
  apply congrArg (fun f => List.map f (evalIndexList Υ Γ))
  funext i
  congr 1
  have hc' : t * (c * P.coeff i) = (c * t) * P.coeff i := by ring
  rw [smul_smul, smul_smul, hc']

/-- Concatenate `P` (outer/left) and `Q` (inner/right) into one product formula. -/
@[reducible] def concat {Υ₁ Υ₂ Γ : ℕ} (P : ProductFormulaData Υ₁ Γ)
    (Q : ProductFormulaData Υ₂ Γ) : ProductFormulaData (Υ₂ + Υ₁) Γ where
  coeff := fun i =>
    if h : (i.1 : ℕ) < Υ₂ then
      Q.coeff (⟨i.1.val, h⟩, i.2)
    else
      P.coeff (⟨i.1.val - Υ₂, by
        have hle : Υ₂ ≤ i.1.val := Nat.le_of_not_gt h
        have hlt : i.1.val < Υ₂ + Υ₁ := i.1.isLt
        lia⟩, i.2)
  perm := fun υ =>
    if h : (υ : ℕ) < Υ₂ then
      Q.perm ⟨υ.val, h⟩
    else
      P.perm ⟨υ.val - Υ₂, by
        have hle : Υ₂ ≤ υ.val := Nat.le_of_not_gt h
        have hlt : υ.val < Υ₂ + Υ₁ := υ.isLt
        lia⟩
  coeff_abs_le_one := fun i => by
    by_cases h : (i.1 : ℕ) < Υ₂
    · rw [dite_eq_left h]
      exact Q.coeff_abs_le_one (⟨i.1.val, h⟩, i.2)
    · have hle : Υ₂ ≤ i.1.val := Nat.le_of_not_gt h
      have hlt : i.1.val - Υ₂ < Υ₁ := by
        have hlt' : i.1.val < Υ₂ + Υ₁ := i.1.isLt
        lia
      rw [dite_eq_right h]
      exact P.coeff_abs_le_one (⟨i.1.val - Υ₂, hlt⟩, i.2)

/-- For a `Q`-stage, the `concat` generator is the `Q` generator. -/
private lemma concat_generator_castAdd {Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ)
    (Q : ProductFormulaData Υ₂ Γ) [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ₂ × Fin Γ) :
    (concat P Q).generator H (Fin.castAdd Υ₁ i.1, i.2) = Q.generator H i := by
  simp [ProductFormulaData.generator, Fin.castAdd]

/-- For a `P`-stage, the `concat` generator is the `P` generator. -/
private lemma concat_generator_natAdd {Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ)
    (Q : ProductFormulaData Υ₂ Γ) [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (υ : Fin Υ₁) (γ : Fin Γ) :
    (concat P Q).generator H (Fin.natAdd Υ₂ υ, γ) = P.generator H (υ, γ) := by
  simp [ProductFormulaData.generator, Fin.natAdd]

/-- For a `Q`-stage, the `concat` factor is the `Q` factor. -/
private lemma concat_evalFactor_castAdd {Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ)
    (Q : ProductFormulaData Υ₂ Γ) [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (i : Fin Υ₂ × Fin Γ) (t : ℝ) :
    (concat P Q).evalFactor H (Fin.castAdd Υ₁ i.1, i.2) t = Q.evalFactor H i t := by
  simp [ProductFormulaData.evalFactor, concat_generator_castAdd P Q H i]

/-- For a `P`-stage, the `concat` factor is the `P` factor. -/
private lemma concat_evalFactor_natAdd {Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ)
    (Q : ProductFormulaData Υ₂ Γ) [NormedSpace ℝ 𝔸]
    (H : Fin Γ → 𝔸) (υ : Fin Υ₁) (γ : Fin Γ) (t : ℝ) :
    (concat P Q).evalFactor H (Fin.natAdd Υ₂ υ, γ) t = P.evalFactor H (υ, γ) t := by
  simp [ProductFormulaData.evalFactor, concat_generator_natAdd P Q H υ γ]

/-- `concat P Q` evaluates as `P.eval` times `Q.eval`. -/
lemma concat_eval {Υ₁ Υ₂ : ℕ} (P : ProductFormulaData Υ₁ Γ) (Q : ProductFormulaData Υ₂ Γ)
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    (concat P Q).eval H t = P.eval H t * Q.eval H t := by
  rw [ProductFormulaData.eval, ProductFormulaData.eval, ProductFormulaData.eval,
    evalIndexList_map_prod (fun i => (concat P Q).evalFactor H i t),
    evalIndexList_map_prod (fun i => P.evalFactor H i t),
    evalIndexList_map_prod (fun i => Q.evalFactor H i t)]
  rw [finRange_reverse_add (n := Υ₂) (m := Υ₁)]
  rw [List.map_append, List.prod_append]
  rw [List.map_map, List.map_map]
  congr 1
  · apply congrArg List.prod
    apply congrArg (fun f => List.map f ((List.finRange Υ₁).reverse))
    funext υ
    apply congrArg List.prod
    apply congrArg (fun g : Fin Γ → 𝔸 => List.map g ((List.finRange Γ).reverse))
    funext γ
    rw [concat_evalFactor_natAdd P Q H υ γ t]
  · apply congrArg List.prod
    apply congrArg (fun f => List.map f ((List.finRange Υ₂).reverse))
    funext υ
    apply congrArg List.prod
    apply congrArg (fun g : Fin Γ → 𝔸 => List.map g ((List.finRange Γ).reverse))
    funext γ
    rw [concat_evalFactor_castAdd P Q H (υ, γ) t]

/-- Transport a product formula along a proof that the stage counts agree (the summand count
`Γ` is unchanged). This is the internal coercion that lets a recursion whose stage count has a
closed form (e.g. `5 · s`) compose with `concat`, which unfolds to a `+`-sum. -/
@[reducible] def castStages {n m Γ : ℕ} (h : n = m) (P : ProductFormulaData n Γ) :
    ProductFormulaData m Γ where
  coeff := fun i => P.coeff (Fin.cast h.symm i.1, i.2)
  perm := fun υ => P.perm (Fin.cast h.symm υ)
  coeff_abs_le_one := fun i => P.coeff_abs_le_one (Fin.cast h.symm i.1, i.2)

/-- Transporting along a stage-count equality does not change evaluation. -/
@[simp] lemma castStages_eval {n m : ℕ} (h : n = m) (P : ProductFormulaData n Γ)
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    (castStages h P).eval H t = P.eval H t := by
  subst h
  rfl

end ProductFormulaData

open ProductFormulaData

variable (P : ProductFormulaData Υ Γ)

/-! ### The ordered summands and generators -/

/-- The permuted summands in canonical stage-major order: index `i = υ * Γ + γ`
carries `H_{π_υ(γ)}`. Use `orderedSummandsEval` for the reversed order of `evalIndexList`.
Here `i.divNat` is the stage and `i.modNat` is the summand index within that stage. -/
noncomputable def orderedSummands {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    Fin (Υ * Γ) → 𝔸 :=
  fun i => H (P.perm (i.divNat) (i.modNat))

/-- The generators of the product formula in `evalIndexList` order (each carrying its coefficient
`a_{(υ,γ)}`). -/
noncomputable def orderedGenerators {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Fin (evalIndexList Υ Γ).length → 𝔸 :=
  fun k => P.generator H ((evalIndexList Υ Γ).get k)

/-- The generators strictly after `i` in `evalIndexList` order (each carrying its coefficient). -/
noncomputable def suffixGenerators {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (i : Fin Υ × Fin Γ) :
    Fin ((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).length → 𝔸 :=
  fun k => P.generator H (((evalIndexList Υ Γ).drop ((evalIndexList Υ Γ).idxOf i + 1)).get k)

/-- `evalIndexList` is the reversed canonical enumeration. -/
lemma evalIndexList_eq_ofFn :
    evalIndexList Υ Γ = List.ofFn (fun k : Fin (Υ * Γ) =>
      (Fin.revPerm k.divNat, Fin.revPerm k.modNat)) := by
  unfold ProductFormulaData.evalIndexList
  rw [List.finRange_reverse, List.finRange_reverse, List.finRange, List.finRange,
    List.map_ofFn, List.map_ofFn, product_ofFn]
  rfl

/-- Reindex the permutations so that coefficient-free summands match `evalIndexList` order.
Coefficients are unchanged; this is not a reversal of the full weighted product formula. -/
def reverseStages {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) : ProductFormulaData Υ Γ where
  coeff := P.coeff
  perm := fun υ => Fin.revPerm.trans (P.perm (Fin.revPerm υ))
  coeff_abs_le_one := P.coeff_abs_le_one

/-- The summands (coefficient dropped) in `evalIndexList` order, canonically indexed. -/
noncomputable def orderedSummandsEval {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    Fin (Υ * Γ) → 𝔸 :=
  fun k => H (P.perm (Fin.revPerm k.divNat) (Fin.revPerm k.modNat))

/-- `orderedSummands (reverseStages P) H = orderedSummandsEval P H`. -/
lemma orderedSummands_reverseStages {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    orderedSummands (reverseStages P) H = orderedSummandsEval P H := rfl

/-- The coefficient-free generators in `evalIndexList` order (each `H_{π_υ(γ)}` without its
coefficient `a_{(υ,γ)}`). -/
noncomputable def fullGenerators {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ)
    {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    Fin (evalIndexList Υ Γ).length → 𝔸 :=
  fun k => H (P.perm ((evalIndexList Υ Γ).get k).1 ((evalIndexList Υ Γ).get k).2)

/-- `evalIndexList` has length `Υ * Γ`. -/
lemma evalIndexList_length : (evalIndexList Υ Γ).length = Υ * Γ := by
  rw [evalIndexList_eq_ofFn]
  simp

/-- The `fullGenerators` are a `Fin.cast` reindexing of `orderedSummandsEval`. -/
lemma fullGenerators_eq_orderedSummandsEval {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    (fun i : Fin (Υ * Γ) => fullGenerators P H (Fin.cast (evalIndexList_length).symm i)) =
      orderedSummandsEval P H := by
  funext i
  simp [fullGenerators, orderedSummandsEval, evalIndexList_eq_ofFn]

/-- `evalIndexList` has no duplicates. -/
lemma evalIndexList_nodup : (evalIndexList Υ Γ).Nodup :=
  (List.nodup_reverse.mpr (List.nodup_finRange Υ)).product
    (List.nodup_reverse.mpr (List.nodup_finRange Γ))

/-- Every factor index occurs in `evalIndexList`. -/
lemma evalIndexList_mem (i : Fin Υ × Fin Γ) : i ∈ evalIndexList Υ Γ := by
  rcases i with ⟨a, b⟩
  simp [ProductFormulaData.evalIndexList]

/-- Identify a position in the evaluation list with its stage and summand indices. -/
def evalIndexEquiv (Υ Γ : ℕ) : Fin (evalIndexList Υ Γ).length ≃ Fin Υ × Fin Γ :=
  List.Nodup.getEquivOfForallMemList (evalIndexList Υ Γ) evalIndexList_nodup evalIndexList_mem

/-- Summing along the evaluation list visits every stage/summand index once. -/
lemma sum_evalIndexList {M : Type*} [AddCommMonoid M] (f : Fin Υ × Fin Γ → M) :
    ((evalIndexList Υ Γ).map f).sum = ∑ i : Fin Υ × Fin Γ, f i := by
  rw [← List.ofFn_getElem_eq_map (evalIndexList Υ Γ) f, List.sum_ofFn]
  exact (evalIndexEquiv Υ Γ).sum_comp f

/-- Sum any observable of the coefficient-free generators by summand, with stage multiplicity. -/
lemma sum_fullGenerators {𝔸 M : Type*} [AddCommMonoid M] (H : Fin Γ → 𝔸) (f : 𝔸 → M) :
    (∑ k, f (fullGenerators P H k)) = Υ • ∑ γ, f (H γ) := by
  change (∑ k, (fun i : Fin Υ × Fin Γ => f (H (P.perm i.1 i.2)))
    (evalIndexEquiv Υ Γ k)) = _
  rw [(evalIndexEquiv Υ Γ).sum_comp (fun i => f (H (P.perm i.1 i.2)))]
  exact P.sum_perm (fun γ => f (H γ))

/-- Evaluate the product formula as an ordered `Fin`-indexed product of generator exponentials. -/
lemma eval_eq_prod_orderedGenerators [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    P.eval H t = (List.ofFn (fun k => exp (t • orderedGenerators P H k))).prod := by
  unfold orderedGenerators
  simp only [List.get_eq_getElem]
  rw [List.ofFn_getElem_eq_map (evalIndexList Υ Γ) (fun i => exp (t • P.generator H i))]
  rfl

end TrotterError

namespace TrotterError

open Asymptotics
open scoped Topology

/-! ### The `p`-th order condition (`P.IsOrderOf`) -/

namespace ProductFormulaData

open NormedSpace

/-- `P` is a `p`-th order formula on summands `H` if `‖𝒮(t) − e^{tH}‖ = O(t^{p+1})`
as `t → 0` (`prelim.tex:150`). -/
def IsOrderOf {Υ Γ : ℕ} (P : ProductFormulaData Υ Γ) (p : ℕ) {𝔸 : Type*} [NormedRing 𝔸]
    [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) : Prop :=
  (fun t : ℝ => ‖P.eval H t - exp (t • ∑ γ : Fin Γ, H γ)‖)
    =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ (p + 1))

end ProductFormulaData

end TrotterError

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
    _ ≤ Real.exp (‖s • P.generator H i‖) := FQFP.norm_exp_le _
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

/-- Bound an ordered factor product by the commutative product of its scalar norms. -/
lemma norm_evalIndexList_prod_le {A : Type*} [NormedRing A] [NormOneClass A]
    {Υ Γ : ℕ} (g : Fin Υ × Fin Γ → A) :
    ‖((evalIndexList Υ Γ).map g).prod‖ ≤ ∏ i, ‖g i‖ := by
  calc
    _ ≤ ((evalIndexList Υ Γ).map (fun i ↦ ‖g i‖)).prod := by
      simpa [List.map_map, Function.comp_def] using
        List.norm_prod_le ((evalIndexList Υ Γ).map g)
    _ = _ := by
      rw [evalIndexList_map_prod (fun i ↦ ‖g i‖), nested_prod_eq_finset_prod (fun i ↦ ‖g i‖)]

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
    _ ≤ ∏ i : Fin Υ × Fin Γ, ‖g i‖ := norm_evalIndexList_prod_le g
    _ ≤ ∏ i : Fin Υ × Fin Γ,
          ‖H (P.perm i.1 i.2)‖ ^ q i * Real.exp (t * ‖H (P.perm i.1 i.2)‖) :=
        prod_le_prod₀ (fun i _ => norm_nonneg _)
          (fun i _ => norm_factor_le P H i (q i) u t ht hu0 hu1)

/-- `∑_{i : Fin Υ × Fin Γ} ‖H_{π_{i.1}(i.2)}‖ = Υ * ∑_γ ‖H_γ‖`. -/
lemma sum_norm_prod (H : Fin Γ → 𝔸) :
    (∑ i : Fin Υ × Fin Γ, ‖H (P.perm i.1 i.2)‖) = (Υ : ℝ) * ∑ γ : Fin Γ, ‖H γ‖ := by
  simpa only [nsmul_eq_mul] using P.sum_perm (fun γ => ‖H γ‖)

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
    _ = (l.map (fun j => ‖H (P.perm j.1 j.2)‖)).sum := by
      rw [← List.sum_ofFn]
      simpa using congrArg List.sum
        (List.ofFn_getElem_eq_map l (fun j => ‖H (P.perm j.1 j.2)‖))

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
  simpa only [nsmul_eq_mul] using
    P.sum_perm (fun γ => αCommConj (orderedSummandsEval P H) (H γ) p)

/-- `star (P.generator H j) = -(P.generator H j)` whenever each `H γ` is anti-Hermitian. -/
lemma star_generator_of_skew [NormedSpace ℝ 𝔸] [Star 𝔸] [StarModule ℝ 𝔸]
    (H : Fin Γ → 𝔸) (h_skew : ∀ γ, star (H γ) = -(H γ)) (j : Fin Υ × Fin Γ) :
    star (P.generator H j) = -(P.generator H j) := by
  unfold ProductFormulaData.generator
  exact star_smul_of_skew (h_skew (P.perm j.1 j.2))

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

namespace TrotterError

open NormedSpace Finset
open scoped Topology

variable {Υ Γ : ℕ}
variable {𝔸 : Type*} [NormedRing 𝔸]
variable (P : ProductFormulaData Υ Γ)

/-! ### The Lie-Trotter and Suzuki formulas (`prelim.tex:127-146`) -/

/-- The first-order Lie-Trotter formula `∏_{γ=1}^Γ e^{t K_γ} = e^{t K_{Γ-1}} ⋯ e^{t K_0}` (the
paper's `∏_{γ=1}^Γ A_γ = A_Γ ⋯ A_1` convention, in 0-based `Fin Γ`), defined by peeling the
innermost (rightmost) factor `K 0`. -/
noncomputable def lieTrotter {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => lieTrotter (fun i : Fin n => K i.succ) t * exp (t • K 0)

/-- The second-order Suzuki formula, defined recursively by peeling the outermost (index-`0`)
factor: `S₂(K, t) = e^{(t/2)K₀} · S₂(K ∘ Fin.succ, t) · e^{(t/2)K₀}`. This is the ordered product
`e^{(t/2)K₀} ⋯ e^{(t/2)K_{Γ-1}} · e^{(t/2)K_{Γ-1}} ⋯ e^{(t/2)K₀}` (the paper's
`∏_{γ=Γ}^1 e^{(t/2)K_γ} · ∏_{γ=1}^Γ e^{(t/2)K_γ}`, in anti-Hermitian-generator form). -/
noncomputable def suzuki2 {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {Γ : ℕ} (K : Fin Γ → 𝔸) (t : ℝ) : 𝔸 :=
  match Γ with
  | 0 => 1
  | n + 1 => exp ((t / 2) • K 0) * suzuki2 (fun i : Fin n => K i.succ) t * exp ((t / 2) • K 0)

/-- `u_k = 1 / (4 - 4^{1/(2k-1)})`, the `eq:pf2k` scaling constant (meaningful for `k ≥ 2`; the
recursion `suzuki (k+2)` below only applies it to an argument `≥ 2`). -/
noncomputable def suzukiU (k : ℕ) : ℝ :=
  (1 : ℝ) / (4 - 4 ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)))

/-- The higher-order Suzuki formula `S_{2k}` (`eq:pf2k`): `suzuki 1 = suzuki2`, and for `k ≥ 2`
`suzuki k K t = suzuki (k-1) K (u_k t)² · suzuki (k-1) K ((1-4u_k) t) · suzuki (k-1) K (u_k t)²`.
The `suzuki 0` case is a junk identity. -/
noncomputable def suzuki {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] :
    ℕ → {Γ : ℕ} → (Fin Γ → 𝔸) → ℝ → 𝔸
  | 0 => fun _ _ => 1
  | 1 => suzuki2
  | k + 2 => fun K t =>
      suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 *
        suzuki (k + 1) K ((1 - 4 * suzukiU (k + 2)) * t) *
        suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2

/-- The Lie-Trotter formula as a `ProductFormulaData`: `Υ = 1`, all coefficients `1`, identity
permutation (`eq:pf1`). -/
@[reducible] def lieTrotterData (Γ : ℕ) : ProductFormulaData 1 Γ where
  coeff := fun _ => 1
  perm := fun _ => Equiv.refl (Fin Γ)
  coeff_abs_le_one := by intro i; simp

/-- The second-order Suzuki formula as a `ProductFormulaData`: `Υ = 2`, all coefficients `1/2`,
stage `0` in order and stage `1` reversed (`eq:pf2k`). -/
@[reducible] noncomputable def suzuki2Data (Γ : ℕ) : ProductFormulaData 2 Γ where
  coeff := fun _ => (1 / 2 : ℝ)
  perm := fun υ => if υ = 0 then Equiv.refl (Fin Γ) else Fin.revPerm
  coeff_abs_le_one := by intro i; norm_num

/-- `lieTrotterData Γ`'s index list: the single stage `0` in reversed order. -/
lemma lieTrotterData_evalIndexList : ProductFormulaData.evalIndexList 1 Γ =
      ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 1), γ)) := by
  unfold ProductFormulaData.evalIndexList
  have h1 : (List.finRange 1).reverse = [0] := by decide
  rw [h1]
  simp [List.product]

/-- `lieTrotterData Γ` evaluates to `∏_{γ=Γ-1}^0 e^{t H_γ}`. -/
lemma lieTrotterData_eval_eq [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    (lieTrotterData Γ).eval H t =
      (((List.finRange Γ).reverse).map (fun γ => exp (t • H γ))).prod := by
  change ((ProductFormulaData.evalIndexList 1 Γ).map
      (fun i => (lieTrotterData Γ).evalFactor H i t)).prod =
    (((List.finRange Γ).reverse).map (fun γ => exp (t • H γ))).prod
  rw [lieTrotterData_evalIndexList]
  rw [List.map_map]
  congr 1
  congr 1
  funext γ
  simp [ProductFormulaData.evalFactor, ProductFormulaData.generator]

/-- `lieTrotter` equals the reversed `finRange` product. -/
lemma lieTrotter_eq_prod [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    lieTrotter K t = (((List.finRange Γ).reverse).map (fun γ => exp (t • K γ))).prod := by
  induction Γ with
  | zero => simp [lieTrotter]
  | succ n ih =>
      rw [lieTrotter, ih]
      have hfin : (List.finRange (n + 1)).reverse =
          ((List.finRange n).reverse).map Fin.succ ++ [0] := by
        rw [List.finRange_succ, List.reverse_cons, List.map_reverse]
      rw [hfin, List.map_append, List.prod_append]
      simp only [List.map_map, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Function.comp_def]

/-- `lieTrotter` is `(lieTrotterData Γ).eval` (`prelim.tex:127,142`). -/
theorem lieTrotter_eq_eval [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) : lieTrotter K t = (lieTrotterData Γ).eval K t := by
  rw [lieTrotter_eq_prod, lieTrotterData_eval_eq]

/-- `suzuki2Data Γ`'s index list: stage `1` (reversed) followed by stage `0` (in order). -/
lemma suzuki2Data_evalIndexList : ProductFormulaData.evalIndexList 2 Γ =
      ((List.finRange Γ).reverse).map (fun γ => ((1 : Fin 2), γ)) ++
        ((List.finRange Γ).reverse).map (fun γ => ((0 : Fin 2), γ)) := by
  unfold ProductFormulaData.evalIndexList
  have h2 : (List.finRange 2).reverse = [1, 0] := by decide
  rw [h2]
  simp [List.product]

/-- `suzuki2Data Γ` evaluates to the increasing-times-decreasing product. -/
lemma suzuki2Data_eval_eq [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    (suzuki2Data Γ).eval H t =
      (((List.finRange Γ).map (fun γ => exp ((t / 2) • H γ))).prod) *
        (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • H γ))).prod := by
  change ((ProductFormulaData.evalIndexList 2 Γ).map
    (fun i => (suzuki2Data Γ).evalFactor H i t)).prod =
    (((List.finRange Γ).map (fun γ => exp ((t / 2) • H γ))).prod) *
      (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • H γ))).prod
  rw [suzuki2Data_evalIndexList]
  rw [List.map_append, List.prod_append]
  congr 1
  · rw [List.map_map]
    have hfac : ((List.finRange Γ).reverse).map
        ((fun i => (suzuki2Data Γ).evalFactor H i t) ∘ (fun γ => ((1 : Fin 2), γ))) =
        ((List.finRange Γ).reverse).map ((fun γ : Fin Γ => exp ((t / 2) • H γ)) ∘ Fin.revPerm) := by
      apply congrArg (fun f : Fin Γ → 𝔸 => List.map f ((List.finRange Γ).reverse))
      funext γ
      simp [ProductFormulaData.evalFactor, ProductFormulaData.generator, smul_smul,
        div_eq_mul_inv]
    rw [hfac]
    rw [TrotterError.List.finRange_reverse_map_comp_revPerm
      (g := fun γ : Fin Γ => exp ((t / 2) • H γ))]
  · rw [List.map_map]
    congr 1
    apply congrArg (fun f : Fin Γ → 𝔸 => List.map f ((List.finRange Γ).reverse))
    funext γ
    simp [ProductFormulaData.evalFactor, ProductFormulaData.generator, smul_smul,
      div_eq_mul_inv]

/-- `suzuki2` equals the increasing-times-decreasing product. -/
lemma suzuki2_eq_prod [NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) :
    suzuki2 K t = (((List.finRange Γ).map (fun γ => exp ((t / 2) • K γ))).prod) *
        (((List.finRange Γ).reverse).map (fun γ => exp ((t / 2) • K γ))).prod := by
  induction Γ with
  | zero => simp [suzuki2]
  | succ n ih =>
      rw [suzuki2, ih]
      have hfwd : (List.finRange (n + 1)).map (fun γ => exp ((t / 2) • K γ)) =
          exp ((t / 2) • K 0) :: ((List.finRange n).map (fun γ => exp ((t / 2) • K γ.succ))) := by
        rw [List.finRange_succ]
        simp
      have hrev : (List.finRange (n + 1)).reverse.map (fun γ => exp ((t / 2) • K γ)) =
          ((List.finRange n).reverse.map (fun γ => exp ((t / 2) • K γ.succ))) ++
            [exp ((t / 2) • K 0)] := by
        rw [List.finRange_succ]
        simp
      rw [hfwd, hrev, List.prod_cons, List.prod_append, List.prod_singleton]
      noncomm_ring

/-- `suzuki2` is `(suzuki2Data Γ).eval` (`prelim.tex:136,142`). -/
theorem suzuki2_eq_eval [NormedAlgebra ℝ 𝔸]
    (K : Fin Γ → 𝔸) (t : ℝ) :
    suzuki2 K t = (suzuki2Data Γ).eval K t := by
  rw [suzuki2_eq_prod, suzuki2Data_eval_eq]

/-! ### The higher-order Suzuki formula as a `ProductFormulaData` -/

/-- For `k ≥ 2`, `4 ^ (1 / (2k-1)) ≤ 2`. -/
lemma suzukiU_rpow_le_two (k : ℕ) (hk : 2 ≤ k) :
    (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ 2 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : (1 : ℝ) / (2 * (k : ℝ) - 1) ≤ 1 / 2 := by
    have hdenom : 0 < 2 * (k : ℝ) - 1 := by nlinarith [hk']
    rw [div_le_iff₀ hdenom]
    nlinarith [hk']
  have hrpow : (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (4 : ℝ)) hx
  have h4half : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    have hsq : (√(4:ℝ)) ^ 2 = 2 ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (4:ℝ))]
      norm_num
    have hnn : 0 ≤ √(4:ℝ) := Real.sqrt_nonneg 4
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right (by intro h; linarith [hnn])
  calc
    (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) ≤ (4 : ℝ) ^ (1 / 2 : ℝ) := hrpow
    _ = 2 := h4half

/-- For `k ≥ 2`, the `suzukiU k` denominator is positive. -/
lemma suzukiU_denom_pos (k : ℕ) (hk : 2 ≤ k) :
    0 < (4 : ℝ) - (4 : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ) - 1)) := by
  have hle := suzukiU_rpow_le_two k hk
  linarith

/-- For `k ≥ 2`, `0 < suzukiU k`. -/
lemma suzukiU_pos (k : ℕ) (hk : 2 ≤ k) : 0 < suzukiU k := by
  unfold suzukiU
  exact div_pos (by norm_num : 0 < (1 : ℝ)) (suzukiU_denom_pos k hk)

/-- For `k ≥ 2`, `suzukiU k ≤ 1 / 2`. -/
lemma suzukiU_le_one_half (k : ℕ) (hk : 2 ≤ k) : suzukiU k ≤ 1 / 2 := by
  unfold suzukiU
  rw [div_le_iff₀ (suzukiU_denom_pos k hk)]
  have hle := suzukiU_rpow_le_two k hk
  nlinarith [hle]

/-- For `k ≥ 2`, `|suzukiU k| ≤ 1`. -/
lemma abs_suzukiU_le_one (k : ℕ) (hk : 2 ≤ k) : |suzukiU k| ≤ 1 := by
  have hpos : 0 ≤ suzukiU k := le_of_lt (suzukiU_pos k hk)
  have hle : suzukiU k ≤ 1 / 2 := suzukiU_le_one_half k hk
  rw [abs_of_nonneg hpos]
  linarith

/-- For `k ≥ 2`, `|1 - 4 * suzukiU k| ≤ 1`. -/
lemma abs_one_sub_four_mul_suzukiU_le_one (k : ℕ) (hk : 2 ≤ k) : |1 - 4 * suzukiU k| ≤ 1 := by
  have hpos : 0 ≤ suzukiU k := le_of_lt (suzukiU_pos k hk)
  have hle : suzukiU k ≤ 1 / 2 := suzukiU_le_one_half k hk
  have h0 : 0 ≤ 4 * suzukiU k := mul_nonneg (by norm_num) hpos
  have h2 : 4 * suzukiU k ≤ 2 := by nlinarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The number of stages `Υ = 2 · 5^{k-1}` of the `k`-th Suzuki formula (`eq:pf2k`). -/
def suzukiStages : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 5 * suzukiStages (k + 1)

/-- The five-fold stage sum produced by the `concat` recursion is `suzukiStages (k + 2)`. -/
lemma suzukiStages_five (k : ℕ) :
    ((((suzukiStages (k + 1) + suzukiStages (k + 1)) + suzukiStages (k + 1))
        + suzukiStages (k + 1)) + suzukiStages (k + 1)) = suzukiStages (k + 2) := by
  rw [show suzukiStages (k + 2) = 5 * suzukiStages (k + 1) from rfl]
  ring

/-- The higher-order Suzuki formula `S_{2k}` as a `ProductFormulaData` (`eq:pf2k`, with
`Υ = 2 · 5^{k-1}` stages and alternately reversed permutations). -/
noncomputable def suzukiData : (k : ℕ) → (Γ : ℕ) → ProductFormulaData (suzukiStages k) Γ
  | 0, Γ => lieTrotterData Γ
  | 1, Γ => suzuki2Data Γ
  | k + 2, Γ =>
      let u := suzukiU (k + 2)
      let P := suzukiData (k + 1) Γ
      let A := ProductFormulaData.scale P u (abs_suzukiU_le_one (k + 2) (by lia))
      let B := ProductFormulaData.scale P (1 - 4 * u)
        (abs_one_sub_four_mul_suzukiU_le_one (k + 2) (by lia))
      ProductFormulaData.castStages (suzukiStages_five k)
        (ProductFormulaData.concat A
          (ProductFormulaData.concat A
            (ProductFormulaData.concat B (ProductFormulaData.concat A A))))

/-- The `(k + 2)`-nd Suzuki data evaluates as the paper's `S_{2k}` recursion
(`eq:pf2k`): `S_{2k}(t) = S_{2k-2}(u_k t)² · S_{2k-2}((1-4u_k) t) · S_{2k-2}(u_k t)²`. -/
lemma suzukiData_succ_eval (k : ℕ) [NormedSpace ℝ 𝔸] (K : Fin Γ → 𝔸) (t : ℝ) :
    (suzukiData (k + 2) Γ).eval K t =
      (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 *
        (suzukiData (k + 1) Γ).eval K ((1 - 4 * suzukiU (k + 2)) * t) *
        (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 := by
  let u : ℝ := suzukiU (k + 2)
  let P : ProductFormulaData (suzukiStages (k + 1)) Γ := suzukiData (k + 1) Γ
  let A : ProductFormulaData (suzukiStages (k + 1)) Γ :=
    ProductFormulaData.scale P u (abs_suzukiU_le_one (k + 2) (by lia))
  let B : ProductFormulaData (suzukiStages (k + 1)) Γ :=
    ProductFormulaData.scale P (1 - 4 * u) (abs_one_sub_four_mul_suzukiU_le_one (k + 2) (by lia))
  change (ProductFormulaData.castStages (suzukiStages_five k)
    (ProductFormulaData.concat A
      (ProductFormulaData.concat A
        (ProductFormulaData.concat B (ProductFormulaData.concat A A))))).eval K t =
    (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2 *
      (suzukiData (k + 1) Γ).eval K ((1 - 4 * suzukiU (k + 2)) * t) *
      (suzukiData (k + 1) Γ).eval K (suzukiU (k + 2) * t) ^ 2
  rw [ProductFormulaData.castStages_eval]
  rw [ProductFormulaData.concat_eval, ProductFormulaData.concat_eval,
    ProductFormulaData.concat_eval, ProductFormulaData.concat_eval]
  dsimp only [A, B]
  simp only [ProductFormulaData.scale_eval]
  noncomm_ring

/-- `suzuki (k + 1)` is `(suzukiData (k + 1) Γ).eval`, by induction on `k`. -/
lemma suzuki_succ_eq_eval [NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (k : ℕ) (t : ℝ) :
    suzuki (k + 1) K t = (suzukiData (k + 1) Γ).eval K t := by
  induction k generalizing t with
  | zero =>
      change suzuki2 K t = (suzuki2Data Γ).eval K t
      exact suzuki2_eq_eval K t
  | succ k ih =>
      rw [show suzuki (k + 2) K t =
          suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 *
            suzuki (k + 1) K ((1 - 4 * suzukiU (k + 2)) * t) *
            suzuki (k + 1) K (suzukiU (k + 2) * t) ^ 2 from rfl]
      rw [ih (suzukiU (k + 2) * t), ih ((1 - 4 * suzukiU (k + 2)) * t)]
      rw [suzukiData_succ_eval]

/-- `suzuki` is `(suzukiData k Γ).eval` (`prelim.tex:136,142`), for the meaningful range `1 ≤ k`
(the `suzuki 0` case is a junk identity). -/
theorem suzuki_eq_eval [NormedAlgebra ℝ 𝔸] (K : Fin Γ → 𝔸) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    suzuki k K t = (suzukiData k Γ).eval K t := by
  cases k with
  | zero => lia
  | succ k => exact suzuki_succ_eq_eval K k t

end TrotterError
