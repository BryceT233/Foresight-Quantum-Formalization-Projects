/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

import FQFP.TrotterError.ListLemmas

/-!
# Product-formula data, evaluation, and operations

The data of a product formula, its ordered evaluation, coefficient scaling,
concatenation, and the index enumerations. Higher derivatives and error estimates
are provided by `FQFP.TrotterError.ProductFormula.Analysis`.

Products follow the paper's right-to-left order, using reversed lists.
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

/-- The evaluation-index equivalence sends a position to the list entry at that position. -/
lemma evalIndexEquiv_apply (k : Fin (evalIndexList Υ Γ).length) :
    evalIndexEquiv Υ Γ k = (evalIndexList Υ Γ).get k := rfl

/-- Summing along the evaluation list visits every stage/summand index once. -/
lemma sum_evalIndexList {M : Type*} [AddCommMonoid M] (f : Fin Υ × Fin Γ → M) :
    ((evalIndexList Υ Γ).map f).sum = ∑ i : Fin Υ × Fin Γ, f i := by
  rw [← ofFn_get_comp (evalIndexList Υ Γ) f, List.sum_ofFn]
  exact (evalIndexEquiv Υ Γ).sum_comp f

/-- The two coefficient-free enumerations give the same ordered list. -/
lemma ofFn_fullGenerators {𝔸 : Type*} (H : Fin Γ → 𝔸) :
    List.ofFn (fullGenerators P H) = List.ofFn (orderedSummandsEval P H) := by
  rw [List.ofFn_congr evalIndexList_length (fullGenerators P H),
    fullGenerators_eq_orderedSummandsEval P H]

/-- Sum any observable of the coefficient-free generators by summand, with stage multiplicity. -/
lemma sum_fullGenerators {𝔸 M : Type*} [AddCommMonoid M] (H : Fin Γ → 𝔸) (f : 𝔸 → M) :
    (∑ k, f (fullGenerators P H k)) = Υ • ∑ γ, f (H γ) := by
  change (∑ k, (fun i : Fin Υ × Fin Γ => f (H (P.perm i.1 i.2)))
    (evalIndexEquiv Υ Γ k)) = _
  rw [(evalIndexEquiv Υ Γ).sum_comp (fun i => f (H (P.perm i.1 i.2)))]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_congr rfl (fun υ _ => Equiv.sum_comp (P.perm υ) (fun γ => f (H γ)))]
  simp

/-- Evaluate the product formula as an ordered `Fin`-indexed product of generator exponentials. -/
lemma eval_eq_prod_orderedGenerators [NormedSpace ℝ 𝔸] (H : Fin Γ → 𝔸) (t : ℝ) :
    P.eval H t = (List.ofFn (fun k => exp (t • orderedGenerators P H k))).prod := by
  unfold orderedGenerators
  rw [ofFn_get_comp (evalIndexList Υ Γ) (fun i => exp (t • P.generator H i))]
  rfl

end TrotterError
