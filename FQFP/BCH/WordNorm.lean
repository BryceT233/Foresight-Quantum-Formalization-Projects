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

## Main results

* `List.norm_prod_le` (Mathlib) is the general form, an arity-free replacement for the whole
  unrolled family, and `norm_prod_le_ofFn` is its `Fin n` restatement.
* `norm_word_le`: the same against a common scale `s`, as `≤ s ^ n`.
* `smul_prod`: homogeneity, `∏ i, (c • w i) = c ^ n • ∏ i, w i`.
* `norm_smul_word_le`: the scaled bound `‖c • ∏ i, w i‖ ≤ cb * s ^ n`.

## Implementation notes

`Finset.norm_prod_le` is stated in `section SeminormedCommGroup` and so does not apply to the
noncommutative products used here; Mathlib's `List.norm_prod_le` does, and everything below is
derived from it rather than reproving the induction.

Stating these for an arbitrary `List` (equivalently `Fin n → 𝔸`) rather than for each arity is
what removes the duplication: the per-branch `calc` blocks in the generated BCH files — one per
monomial, each repeating `norm_smul_le` → `norm_Nprod_le` → `gcongr` → `ring` — become one
application.

The scalar field is an arbitrary `NormedField 𝕂`, not the source's `RCLike 𝕂`: `RCLike ℚ` does not
exist, and the BCH layer states everything over `ℚ`, so a `RCLike` binder would make the scaling
lemmas unusable exactly where they are needed.
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP.BCH

/-! ### The norm of a product -/

section WordNorm

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The norm of a product over an arbitrary index type, bounded by the product of the norms. This is
the arity-free form of the whole `norm_5prod_le` … `norm_10prod_le` family. -/
lemma norm_prod_le_ofFn [NormOneClass 𝔸] {n : ℕ} (w : Fin n → 𝔸) :
    ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := by
  calc ‖(List.ofFn w).prod‖ ≤ ((List.ofFn w).map norm).prod := List.norm_prod_le _
    _ = (List.ofFn fun i => ‖w i‖).prod := by rw [List.map_ofFn]; rfl
    _ = ∏ i, ‖w i‖ := List.prod_ofFn

/-- The norm of a product is bounded by `s ^ n` when every factor has norm at most `s`. -/
lemma norm_word_le [NormOneClass 𝔸] {n : ℕ} (w : Fin n → 𝔸) {s : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ s) : ‖(List.ofFn w).prod‖ ≤ s ^ n := by
  calc ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := norm_prod_le_ofFn w
    _ ≤ ∏ _i : Fin n, s := prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hw i)
    _ = s ^ n := by simp

end WordNorm

/-! ### Homogeneity and the scaled word bound -/

section Scaling

variable {𝕂 : Type*} [NormedField 𝕂]
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Homogeneity: scaling every factor by `c` scales the product by `c ^ n`. -/
lemma smul_prod {n : ℕ} (c : 𝕂) (w : Fin n → 𝔸) :
    (List.ofFn fun i => c • w i).prod = c ^ n • (List.ofFn w).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, smul_mul_assoc,
        mul_smul_comm, smul_smul, pow_succ']

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

end Scaling

end FQFP.BCH
