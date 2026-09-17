/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Norm bounds for products of words

Norm bounds for products of a finite family of elements of a normed ring, at arbitrary
length. These replace the arity-indexed families that the `Lean-BCH` project carried —
23 distinct lemma names with roughly 6.9k call sites, one lemma per arity
(`norm_5prod_le` … `norm_10prod_le`, `norm_three/four/five/six_word_le`,
`norm_sextic_word_le`, and the `deg7/8/9/10_smul_word_le` chain).

## Design

The **canonical product form is the paper's**, which is a right fold: the paper *A Theory of
Trotter Error* fixes `∏_{γ=1}^{Γ} A_γ = A_Γ ⋯ A_1`, and Mathlib's `List.prod` is likewise a
right fold. `ProductFormulaData.eval` uses exactly that convention. The main results below are
therefore stated over `List.prod`.

`Lean-BCH` instead writes its monomials associated to the **left**,
`(⋯ * w (n-2)) * w (n-1)`. That is a notational artefact — the norm layer is commutative, so
the association carries no mathematical content. `wordProd` is kept as the left-associated
form together with `wordProd_eq_prod`, so BCH-derived material can be stated without change;
it is a derived notion, not a second theory.

## Main results

* `norm_prod_le`: `‖l.prod‖ ≤ (l.map norm).prod` — the general form, an arity-free
  replacement for the whole unrolled family.
* `norm_word_le`: the same against a common scale `s`, as `≤ s ^ l.length`.
* `smul_prod`: homogeneity, `∏ i, (c • w i) = c ^ n • ∏ i, w i`.
* `norm_smul_word_le`: the scaled bound `‖c • ∏ i, w i‖ ≤ cb * s ^ n`.
* `norm_wordProd_le`, `norm_smul_wordProd_le`: the left-associated restatements.

## Implementation notes

`Finset.norm_prod_le` is stated in `section SeminormedCommGroup` and so does not apply to the
noncommutative products used here; Mathlib's `List.norm_prod_le` does, and everything below is
derived from it rather than reproving the induction.

Stating these for an arbitrary `List` (equivalently `Fin n → 𝔸`) rather than for each arity is
what removes the duplication: the per-branch `calc` blocks in the generated BCH files — one per
monomial, each repeating `norm_smul_le` → `norm_Nprod_le` → `gcongr` → `ring` — become one
application.

**Assisted by Deepseek Harness**
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP.BCH

noncomputable section

variable {𝕂 : Type*} [RCLike 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸]

/-! ### The norm of a product -/

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- The norm of a product is bounded by the product of the norms. This is the arity-free
form of the whole `norm_5prod_le` … `norm_10prod_le` family. -/
lemma norm_prod_le [NormOneClass 𝔸] (l : List 𝔸) : ‖l.prod‖ ≤ (l.map norm).prod :=
  List.norm_prod_le l

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- The norm of a product over an arbitrary index type, bounded by the product of the norms. -/
lemma norm_prod_le_ofFn [NormOneClass 𝔸] {n : ℕ} (w : Fin n → 𝔸) :
    ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := by
  calc ‖(List.ofFn w).prod‖ ≤ ((List.ofFn w).map norm).prod := norm_prod_le (List.ofFn w)
    _ = (List.ofFn fun i => ‖w i‖).prod := by rw [List.map_ofFn]; rfl
    _ = ∏ i, ‖w i‖ := List.prod_ofFn

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- The norm of a product is bounded by `s ^ n` when every factor has norm at most `s`. -/
lemma norm_word_le [NormOneClass 𝔸] {n : ℕ} (w : Fin n → 𝔸) {s : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ s) : ‖(List.ofFn w).prod‖ ≤ s ^ n := by
  calc ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := norm_prod_le_ofFn w
    _ ≤ ∏ _i : Fin n, s := prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hw i)
    _ = s ^ n := by simp

/-! ### Homogeneity -/

omit [NormedAlgebra ℚ 𝔸] in
/-- Homogeneity: scaling every factor by `c` scales the product by `c ^ n`. -/
lemma smul_prod {n : ℕ} (c : 𝕂) (w : Fin n → 𝔸) :
    (List.ofFn fun i => c • w i).prod = c ^ n • (List.ofFn w).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, smul_mul_assoc,
        mul_smul_comm, smul_smul, pow_succ']

omit [NormedAlgebra ℚ 𝔸] in
/-- The scaled word bound: if `‖c‖ ≤ cb` and every factor has norm at most `s`, then
`‖c • ∏ i, w i‖ ≤ cb * s ^ n`. This is the arity-free form of the
`deg7/deg8/deg9/deg10_smul_word_le` chain.

No hypothesis `0 ≤ s` is needed: for `n > 0` the hypothesis `hw` already forces
`s = ‖w 0‖ ≥ 0`, and for `n = 0` both sides are `cb` times `1`. -/
lemma norm_smul_word_le [NormOneClass 𝔸] {n : ℕ} (c : 𝕂) (w : Fin n → 𝔸) {s cb : ℝ}
    (hc : ‖c‖ ≤ cb) (hw : ∀ i, ‖w i‖ ≤ s) (hcb : 0 ≤ cb) :
    ‖c • (List.ofFn w).prod‖ ≤ cb * s ^ n := by
  calc ‖c • (List.ofFn w).prod‖ ≤ ‖c‖ * ‖(List.ofFn w).prod‖ := norm_smul_le _ _
    _ ≤ cb * ‖(List.ofFn w).prod‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ cb * s ^ n := mul_le_mul_of_nonneg_left (norm_word_le w hw) hcb

/-! ### The left-associated form

`Lean-BCH` writes monomials associated to the left. The results above are about `List.prod`,
which is a right fold, so the left-associated versions are recorded here as derived notions.
A call site holding a left-associated product rewrites with `wordProd_eq_prod`. -/

/-- The left-associated product `w 0 * w 1 * ⋯ * w (n - 1)`. This is the form in which
`Lean-BCH` writes its monomials; it agrees with `List.prod` only up to associativity. -/
def wordProd : {n : ℕ} → (Fin n → 𝔸) → 𝔸
  | 0, _ => 1
  | _ + 1, w => wordProd (fun i : Fin _ => w i.castSucc) * w (Fin.last _)

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
@[simp]
lemma wordProd_zero (w : Fin 0 → 𝔸) : wordProd w = 1 := rfl

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
@[simp]
lemma wordProd_succ {n : ℕ} (w : Fin (n + 1) → 𝔸) :
    wordProd w = wordProd (fun i : Fin n => w i.castSucc) * w (Fin.last n) := rfl

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- The left-associated product equals the right-associated one. This is the bridge that lets
`Lean-BCH`-style statements be served by the `List.prod` results above. -/
lemma wordProd_eq_prod {n : ℕ} (w : Fin n → 𝔸) :
    wordProd w = (List.ofFn w).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [wordProd_succ, ih, List.ofFn_succ', List.concat_eq_append, List.prod_append,
        List.prod_singleton]

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- The right-associated product equals the left-associated one, i.e. `wordProd_eq_prod`
read the other way. This is the direction a `Lean-BCH`-style goal needs. -/
lemma prod_eq_wordProd {n : ℕ} (w : Fin n → 𝔸) :
    (List.ofFn w).prod = wordProd w :=
  (wordProd_eq_prod w).symm

omit [NormedAlgebra ℚ 𝔸] [NormedAlgebra 𝕂 𝔸] in
/-- Left-associated restatement of `norm_prod_le_ofFn`. -/
lemma norm_wordProd_le [NormOneClass 𝔸] {n : ℕ} (w : Fin n → 𝔸) :
    ‖wordProd w‖ ≤ ∏ i, ‖w i‖ := by
  rw [wordProd_eq_prod]; exact norm_prod_le_ofFn w

omit [NormedAlgebra ℚ 𝔸] in
/-- Left-associated restatement of `norm_smul_word_le`. -/
lemma norm_smul_wordProd_le [NormOneClass 𝔸] {n : ℕ} (c : 𝕂) (w : Fin n → 𝔸) {s cb : ℝ}
    (hc : ‖c‖ ≤ cb) (hw : ∀ i, ‖w i‖ ≤ s) (hcb : 0 ≤ cb) :
    ‖c • wordProd w‖ ≤ cb * s ^ n := by
  rw [wordProd_eq_prod]; exact norm_smul_word_le c w hc hw hcb

omit [NormedAlgebra ℚ 𝔸] in
/-- Left-associated restatement of `smul_prod`. -/
lemma smul_wordProd {n : ℕ} (c : 𝕂) (w : Fin n → 𝔸) :
    wordProd (fun i => c • w i) = c ^ n • wordProd w := by
  rw [wordProd_eq_prod, wordProd_eq_prod]
  exact smul_prod c w

end

end FQFP.BCH
