/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.BigOperators.Group.List.Fin
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Differentiation and smoothness of ordered list products

The pointwise product of finitely many algebra-valued functions satisfies the
ordered product rule and preserves differentiability classes.

## Main results

* `TrotterError.List.hasDerivAt_list_prod_at` gives the ordered product rule at a point.
* `TrotterError.List.contDiff_list_prod` shows that finite ordered products preserve smoothness.
-/

@[expose] public section

namespace TrotterError

open scoped Topology ContDiff

/-- `ContDiffAt` for the pointwise product of a finite list of functions. -/
lemma contDiffAt_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) (n : ℕ∞ω) (t : ℝ)
    (hf : ∀ i ∈ l, ContDiffAt ℝ n (f i) t) :
    ContDiffAt ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℝ => (1 : 𝔸)) t)
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ContDiffAt.mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

namespace List

/-- The ordered product rule, assuming derivatives only at the evaluation point. -/
lemma hasDerivAt_list_prod_at {ι 𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (l : List ι) (f : ι → ℝ → 𝔸) (Df : ι → 𝔸) (t : ℝ)
    (hf : ∀ i ∈ l, HasDerivAt (f i) (Df i) t) :
    HasDerivAt (fun s : ℝ => (l.map (fun i => f i s)).prod)
      (∑ k : Fin l.length,
        ((l.take (k : ℕ)).map (fun i => f i t)).prod * Df (l.get k) *
          ((l.drop ((k : ℕ) + 1)).map (fun i => f i t)).prod) t := by
  induction l with
  | nil => simpa using (hasDerivAt_const t (1 : 𝔸))
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      have htail := ih (fun i hi => hf i (List.mem_cons_of_mem a hi))
      refine ((hf a List.mem_cons_self).mul htail).congr_deriv ?_
      simp only [List.length_cons, Fin.sum_univ_succ, Finset.mul_sum]
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro k _
        simp [mul_assoc]

/-- The pointwise product of a finite list of `C^n` functions is `C^n`. -/
lemma contDiff_list_prod {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {ι : Type*} (l : List ι) (f : ι → ℝ → 𝔸) {n : ℕ∞ω}
    (hf : ∀ i ∈ l, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun t : ℝ => (l.map (fun i => f i t)).prod) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact contDiffAt_list_prod l f n t (fun i hi => (hf i hi).contDiffAt)

end List

end TrotterError
