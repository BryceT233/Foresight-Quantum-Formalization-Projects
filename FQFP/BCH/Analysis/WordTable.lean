/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.WordTable
public import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Norm bounds for integer word certificates

The coefficient budget of a word table bounds its evaluation whenever a common
bound on its monomials is available. This applies directly to the same table used
for coefficient checking; no rational table representation is introduced.

## Main results

* `FQFP.WordTable.norm_eval_le`: evaluation is bounded by the coefficient budget
  times a common monomial bound.
-/

@[expose] public section

namespace FQFP.WordTable

variable {α 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- The sum of the norms of the scaled coefficients bounds evaluation when each
monomial has norm at most `M`. -/
lemma norm_eval_le (scale : ℚ) (letters : α → 𝔸) (t : Table α) {M : ℝ}
    (h : ∀ p ∈ t, ‖(p.1.map letters).prod‖ ≤ M) :
    ‖eval scale letters t‖ ≤
      (t.map fun p ↦ ‖(p.2 : ℚ) / scale ^ p.1.length‖).sum * M := by
  induction t with
  | nil => simp [eval]
  | cons p t ih =>
      rw [eval_cons, List.map_cons, List.sum_cons, add_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ (ih fun q hq ↦
        h q (List.mem_cons_of_mem p hq)))
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (h p List.mem_cons_self) (norm_nonneg _)

end FQFP.WordTable
