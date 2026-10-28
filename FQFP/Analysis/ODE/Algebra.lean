/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Uniqueness of algebra-valued linear evolution

Continuous left-multiplication coefficients give uniqueness, including identical forcing.

## Main results

* `TrotterError.ode_solution_unique`, `TrotterError.ode_inhomogeneous_solution_unique`.
-/

@[expose] public section

namespace TrotterError

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedSpace ℝ 𝔸]

/-- Uniqueness of solutions to the ODE `U' = H·U`: two functions solving `U' = H·U` pointwise and
agreeing at one time `t₀` agree everywhere. The continuity of `H` is used only to obtain a uniform
Lipschitz constant on the compact interval between `t₀` and each target point. -/
lemma ode_solution_unique (H : ℝ → 𝔸) (hH : Continuous H) {f g : ℝ → 𝔸}
    (hf : ∀ t, HasDerivAt f (H t * f t) t) (hg : ∀ t, HasDerivAt g (H t * g t) t)
    (t₀ : ℝ) (heq : f t₀ = g t₀) : f = g := by
  funext t
  let a : ℝ := min t t₀ - 1
  let b : ℝ := max t t₀ + 1
  have ht₀ : t₀ ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_right t t₀, le_max_right t t₀]
  have ht : t ∈ Set.Ioo a b := by
    constructor <;> linarith [min_le_left t t₀, le_max_left t t₀]
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨t₀, ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩⟩ (hH.norm.continuousOn)
  let M : NNReal := ⟨‖H x‖, norm_nonneg (H x)⟩
  have hM : ∀ s ∈ Set.Icc a b, ‖H s‖ ≤ (M : ℝ) := fun s hs => (isMaxOn_iff.mp hmax) s hs
  have hv : ∀ s ∈ Set.Ioo a b, LipschitzOnWith M (fun y : 𝔸 => H s * y) Set.univ := by
    intro s hs
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    calc
      dist (H s * x) (H s * y) = ‖H s * (x - y)‖ := by
          rw [dist_eq_norm, mul_sub]
      _ ≤ ‖H s‖ * ‖x - y‖ := norm_mul_le _ _
      _ ≤ (M : ℝ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (hM s (Set.Ioo_subset_Icc_self hs)) (norm_nonneg (x - y))
      _ = M * dist x y := by simp [dist_eq_norm]
  have hres := ODE_solution_unique_of_mem_Ioo
    (v := fun s y => H s * y) (s := fun _ => Set.univ) (K := M)
    (f := f) (g := g) (a := a) (b := b) (t₀ := t₀) hv ht₀
    (fun s hs => ⟨hf s, trivial⟩) (fun s hs => ⟨hg s, trivial⟩) heq
  exact hres ht

/-- Two solutions of `U' = H·U + R` with the same forcing term and the same value at
one time agree everywhere. Only the coefficient `H` needs to be continuous. -/
lemma ode_inhomogeneous_solution_unique (H R : ℝ → 𝔸) (hH : Continuous H)
    {f g : ℝ → 𝔸} (hf : ∀ t, HasDerivAt f (H t * f t + R t) t)
    (hg : ∀ t, HasDerivAt g (H t * g t + R t) t) (t₀ : ℝ) (heq : f t₀ = g t₀) :
    f = g := by
  have hd : ∀ t, HasDerivAt (fun s => f s - g s) (H t * (f t - g t)) t := by
    intro t
    have hderiv_eq : (H t * f t + R t) - (H t * g t + R t) = H t * (f t - g t) := by
      rw [mul_sub]
      abel
    exact hderiv_eq ▸ ((hf t).sub (hg t))
  have hzero : ∀ t, HasDerivAt (fun _ : ℝ => (0 : 𝔸)) (H t * (0 : 𝔸)) t := by
    intro t
    simpa using (hasDerivAt_const (x := t) (c := (0 : 𝔸)))
  have hd0 : f t₀ - g t₀ = 0 := by rw [heq, sub_self]
  have huniq := ode_solution_unique H hH hd hzero t₀ hd0
  funext t
  exact sub_eq_zero.mp (congr_fun huniq t)

end TrotterError
