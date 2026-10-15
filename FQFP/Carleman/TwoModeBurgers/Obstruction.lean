/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Leading
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Infinite-dimensional polynomial closure of the coordinates

For nonzero coupling, iterated Lie derivatives of either state coordinate
have unbounded total degree. A finite-dimensional polynomial subspace has a
uniform degree bound, so it cannot contain the coordinate and be invariant.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

private def boundedDegree (N : ℕ) : Submodule ℝ (MvPolynomial (Fin 2) ℝ) where
  carrier := {p | p.totalDegree ≤ N}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    exact (totalDegree_add p q).trans (max_le hp hq)
  smul_mem' := by
    intro c p hp
    exact (totalDegree_smul_le c p).trans hp

/-- Every finite-dimensional polynomial subspace has a uniform total-degree bound. -/
theorem finiteDimensional_totalDegree_bounded (V : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    [FiniteDimensional ℝ V] : ∃ N : ℕ, ∀ p ∈ V, p.totalDegree ≤ N := by
  have hfg : V.FG := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hfg
  let N := hs.toFinset.sup (fun p : MvPolynomial (Fin 2) ℝ => p.totalDegree)
  have hsbound : s ⊆ boundedDegree N := by
    intro p hp
    change p.totalDegree ≤ N
    exact Finset.le_sup (hs.mem_toFinset.mpr hp)
  have hV : V ≤ boundedDegree N := by
    rw [← hspan]
    exact Submodule.span_le.mpr hsbound
  exact ⟨N, fun p hp => hV hp⟩

/-- An invariant subspace contains every Lie iterate of each of its elements. -/
lemma lieIterate_mem_invariant (α γ β : ℝ) (V : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    (hV : ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V)
    {p : MvPolynomial (Fin 2) ℝ} (hp : p ∈ V)
    (n : ℕ) : ((mkDerivation ℝ (vectorField α γ β))^[n]) (p) ∈ V := by
  induction n with
  | zero => simpa using hp
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hV _ ih

/-- No finite-dimensional invariant polynomial space contains the first coordinate. -/
theorem no_finite_polynomial_closure_first (α γ β : ℝ) (hβ : β ≠ 0) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ (X 0 : MvPolynomial (Fin 2) ℝ) ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  rintro ⟨V, hfin, hfirst, hV⟩
  have : FiniteDimensional ℝ V := hfin
  obtain ⟨N, hN⟩ := finiteDimensional_totalDegree_bounded V
  have hmem := lieIterate_mem_invariant α γ β V hV hfirst (N + 1)
  have hdegree := hN _ hmem
  rw [lieIterate_first_totalDegree α γ β hβ] at hdegree
  lia

/-- No finite-dimensional invariant polynomial space contains the second coordinate. -/
theorem no_finite_polynomial_closure_second (α γ β : ℝ) (hβ : β ≠ 0) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ (X 1 : MvPolynomial (Fin 2) ℝ) ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  rintro ⟨V, hfin, hsecond, hV⟩
  have : FiniteDimensional ℝ V := hfin
  obtain ⟨N, hN⟩ := finiteDimensional_totalDegree_bounded V
  have hmem := lieIterate_mem_invariant α γ β V hV hsecond (N + 1)
  have hdegree := hN _ hmem
  rw [lieIterate_second_totalDegree α γ β hβ] at hdegree
  lia

end TwoModeBurgers
