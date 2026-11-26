/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.GroupedConjugation

/-!
# Signs in grouped conjugation remainder constants

Negating an adjoint generator changes only the sign of each iterated bracket.
Its norm is unchanged, while signed generators remain in the recursively
combined lower coefficients.

## Main results

* `norm_adPow_neg_eq`: outer generator signs disappear upon taking norms.
* `groupedConjBound_neg_eq_sum`: the sum with unsigned outer adjoint generators.
-/

@[expose] public noncomputable section

open Finset

namespace TrotterError

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- Negating the outer adjoint generator preserves the norm of each iterated bracket. -/
lemma norm_adPow_neg_eq (Z B : A) (n : ℕ) : ‖adPow (-Z) n B‖ = ‖adPow Z n B‖ := by
  rw [show -Z = (-1 : ℝ) • Z by simp, adPow_smul_left]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, one_smul]
  · rw [hn.neg_one_pow, neg_one_smul, norm_neg]

/-- Outer adjoint signs disappear from the grouped norm sum; the recursively
combined coefficients retain their original signed generators. -/
theorem groupedConjBound_neg_eq_sum {s : ℕ} (Z K : Fin s → A) (B : A) (p : ℕ) :
    groupedConjBound (fun i ↦ -Z i) K B p =
      ∑ j : Fin s, ∑ k ∈ range p, ‖adPow (Z j) (p - k)
        (groupedConjCoeff ((fun i ↦ -Z i) ∘ Fin.castLE (Nat.le_of_lt j.isLt))
          (K ∘ Fin.castLE (Nat.le_of_lt j.isLt)) B k)‖ /
            (Nat.factorial (p - k) : ℝ) := by
  rw [groupedConjBound_eq_sum]
  simp only [norm_adPow_neg_eq]

end TrotterError
