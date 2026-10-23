/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Word
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Norm bounds for nonempty ordered products

The finite-family interfaces use Mathlib's `List.norm_prod_le'` and
`Finset.prod_le_prod₀`. Positive length avoids an unnecessary `NormOneClass`.
Separate bounds on selected positions support the finite Taylor remainder estimates.
-/

@[expose] public section

open Finset NormedSpace

namespace FQFP

/-! ### The norm of a product -/

section WordNorm

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- A nonempty ordered product is bounded by the product of the norms of its factors. -/
lemma norm_prod_le_ofFn_of_pos {n : ℕ} (hn : 0 < n) (w : Fin n → 𝔸) :
    ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := by
  calc
    ‖(List.ofFn w).prod‖ ≤ ((List.ofFn w).map norm).prod :=
      List.norm_prod_le' (by simpa using Nat.ne_of_gt hn)
    _ = (List.ofFn fun i ↦ ‖w i‖).prod := by rw [List.map_ofFn]; rfl
    _ = ∏ i, ‖w i‖ := List.prod_ofFn

/-- A nonempty product is bounded by the corresponding power of a common factor bound. -/
lemma norm_word_le_of_pos {n : ℕ} (hn : 0 < n) (w : Fin n → 𝔸) {s : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ s) : ‖(List.ofFn w).prod‖ ≤ s ^ n := by
  calc
    ‖(List.ofFn w).prod‖ ≤ ∏ i, ‖w i‖ := norm_prod_le_ofFn_of_pos hn w
    _ ≤ ∏ _i : Fin n, s := prod_le_prod₀ (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hw i)
    _ = s ^ n := by simp

/-- Bound a nonempty product with separate bounds on selected and remaining positions. -/
lemma norm_prod_piecewise_le_of_pos {n : ℕ} (hn : 0 < n) (s : Finset (Fin n))
    (u v : Fin n → 𝔸) {U V : ℝ} (hu : ∀ i ∈ s, ‖u i‖ ≤ U)
    (hv : ∀ i ∉ s, ‖v i‖ ≤ V) :
    ‖(List.ofFn (s.piecewise u v)).prod‖ ≤ U ^ s.card * V ^ (n - s.card) := by
  calc
    ‖(List.ofFn (s.piecewise u v)).prod‖ ≤ ∏ i, ‖s.piecewise u v i‖ :=
      norm_prod_le_ofFn_of_pos hn _
    _ ≤ ∏ i, s.piecewise (fun _ ↦ U) (fun _ ↦ V) i := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi, hu, hv]
    _ = U ^ s.card * V ^ (n - s.card) := by
      rw [Finset.prod_piecewise]
      simp [Finset.card_sdiff]

end WordNorm

end FQFP
