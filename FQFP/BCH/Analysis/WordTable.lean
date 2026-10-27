/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.WordTable
public import FQFP.BCH.Analysis.Word
public import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Norm bounds for integer word certificates

The coefficient budget of a word table bounds its evaluation whenever a common
bound on its monomials is available. This applies directly to the same table used
for coefficient checking; no rational table representation is introduced.

## Main results

* `FQFP.WordTable.norm_eval_le`: evaluation is bounded by the coefficient budget
  times a common monomial bound.
* `FQFP.WordTable.norm_eval_one_le_of_length`: a homogeneous table is bounded by
  its integer absolute-coefficient budget times a power of the letter bound.
* `List.norm_sum_map_smul_le`: weighted bounds for finite sums of scalar products.
-/

@[expose] public section

namespace FQFP.WordTable

/-- Bound a scalar-weighted list sum by the corresponding weighted scalar budget. -/
lemma _root_.List.norm_sum_map_smul_le {ι K B : Type*} [NormedField K]
    [NormedAddCommGroup B] [NormedSpace K B] (t : List ι)
    (c : ι → K) (f : ι → B) (b : ι → ℝ) {M : ℝ}
    (h : ∀ p ∈ t, ‖f p‖ ≤ b p * M) :
    ‖(t.map fun p ↦ c p • f p).sum‖ ≤ (t.map fun p ↦ ‖c p‖ * b p).sum * M := by
  induction t with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ (ih fun q hq ↦
      h q (List.mem_cons_of_mem p hq)))
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h p List.mem_cons_self) (norm_nonneg _)

variable {α 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- The sum of the norms of the scaled coefficients bounds evaluation when each
monomial has norm at most `M`. -/
lemma norm_eval_le (scale : ℚ) (letters : α → 𝔸) (t : Table α) {M : ℝ}
    (h : ∀ p ∈ t, ‖(p.1.map letters).prod‖ ≤ M) :
    ‖eval scale letters t‖ ≤
      (t.map fun p ↦ ‖(p.2 : ℚ) / scale ^ p.1.length‖).sum * M := by
  simpa only [eval, mul_one, one_mul] using
    List.norm_sum_map_smul_le t (fun p ↦ (p.2 : ℚ) / scale ^ p.1.length)
      (fun p ↦ (p.1.map letters).prod) (fun _ ↦ 1) (fun p hp ↦ by simpa using h p hp)

/-- A positive-degree homogeneous table is bounded by its integer absolute-coefficient
budget and a common bound on its letters, without a hypothesis on the norm of one. -/
lemma norm_eval_one_le_of_length (letters : α → 𝔸) (t : Table α) {n : ℕ} (hn : 0 < n)
    (hlen : ∀ p ∈ t, p.1.length = n) {M : ℝ} (hletters : ∀ i, ‖letters i‖ ≤ M) :
    ‖eval 1 letters t‖ ≤ (((t.map fun p ↦ p.2.natAbs).sum : ℕ) : ℝ) * M ^ n := by
  have hmon (p) (hp : p ∈ t) : ‖(p.1.map letters).prod‖ ≤ M ^ n := by
    rw [← hlen p hp, ← List.ofFn_getElem_eq_map p.1 letters]
    exact norm_word_le_of_pos (by rwa [hlen p hp])
      (fun i : Fin p.1.length ↦ letters p.1[i]) (fun _ ↦ hletters _)
  have hnorm (z : ℤ) : ‖(z : ℚ)‖ = (z.natAbs : ℝ) := by
    rw [← norm_natAbs]
    norm_num [← Rat.norm_cast_real]
  simpa only [one_pow, div_one, hnorm, Nat.cast_list_sum, List.map_map, Function.comp_def] using
    norm_eval_le 1 letters t hmon

end FQFP.WordTable
