/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Carleman.TwoModeBurgers.Leading
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

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

/-- Every finite-dimensional polynomial subspace has a uniform total-degree bound. -/
theorem finiteDimensional_totalDegree_bounded (V : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    [FiniteDimensional ℝ V] : ∃ N : ℕ, ∀ p ∈ V, p.totalDegree ≤ N := by
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional V).2 inferInstance
  let N := s.sup totalDegree
  have hV : V ≤ restrictTotalDegree (Fin 2) ℝ N := by
    rw [← hs, Submodule.span_le]
    exact fun p hp ↦ (mem_restrictTotalDegree _ _ p).2 (Finset.le_sup hp)
  exact ⟨N, fun p hp ↦ (mem_restrictTotalDegree _ _ p).1 (hV hp)⟩

/-- An invariant subspace contains every Lie iterate of each of its elements. -/
lemma lieIterate_mem_invariant (α γ β : ℝ) (V : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    (hV : ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V)
    {p : MvPolynomial (Fin 2) ℝ} (hp : p ∈ V)
    (n : ℕ) : ((mkDerivation ℝ (vectorField α γ β))^[n]) (p) ∈ V := by
  have hmap : Set.MapsTo (mkDerivation ℝ (vectorField α γ β)) V V := fun {_} hx ↦ hV _ hx
  exact hmap.iterate n hp

/-- The span of the Lie iterates is finite-dimensional exactly when the observable
belongs to a finite-dimensional invariant polynomial space. -/
theorem finiteDimensional_span_lieIterate_iff (α γ β : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun n : ℕ ↦
      ((mkDerivation ℝ (vectorField α γ β))^[n]) p)) ↔
    ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ), FiniteDimensional ℝ V ∧ p ∈ V ∧
      ∀ q ∈ V, (mkDerivation ℝ (vectorField α γ β)) q ∈ V := by
  let D := mkDerivation ℝ (vectorField α γ β)
  let V := Submodule.span ℝ (Set.range fun n : ℕ ↦ D^[n] p)
  constructor
  · intro hfin
    have hmem (n : ℕ) : D^[n] p ∈ V := Submodule.subset_span ⟨n, rfl⟩
    have hV : V ≤ V.comap D.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      change D (D^[n] p) ∈ V
      simpa only [Function.iterate_succ_apply'] using hmem (n + 1)
    exact ⟨V, hfin, hmem 0, fun _ hq ↦ hV hq⟩
  · rintro ⟨W, hfin, hp, hW⟩
    apply Submodule.finiteDimensional_of_le (S₂ := W)
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact lieIterate_mem_invariant α γ β W hW hp n

/-- Unbounded total degree along the Lie iterates of an observable rules out
a finite-dimensional invariant polynomial space containing it. -/
theorem no_finite_polynomial_closure_of_unbounded_totalDegree (α γ β : ℝ)
    (p : MvPolynomial (Fin 2) ℝ)
    (hunbounded : ∀ N : ℕ, ∃ n : ℕ,
      N < (((mkDerivation ℝ (vectorField α γ β))^[n]) p).totalDegree) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ), FiniteDimensional ℝ V ∧ p ∈ V ∧
      ∀ q ∈ V, (mkDerivation ℝ (vectorField α γ β)) q ∈ V := by
  rintro ⟨V, hfin, hp, hV⟩
  obtain ⟨N, hN⟩ := finiteDimensional_totalDegree_bounded V
  obtain ⟨n, hn⟩ := hunbounded N
  exact hn.not_ge (hN _ (lieIterate_mem_invariant α γ β V hV hp n))

/-- No finite-dimensional invariant polynomial space contains the first coordinate. -/
theorem no_finite_polynomial_closure_first (α γ β : ℝ) (hβ : β ≠ 0) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ (X 0 : MvPolynomial (Fin 2) ℝ) ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  apply no_finite_polynomial_closure_of_unbounded_totalDegree
  intro N
  exact ⟨N, by simp [lieIterate_first_totalDegree α γ β hβ]⟩

/-- No finite-dimensional invariant polynomial space contains the second coordinate. -/
theorem no_finite_polynomial_closure_second (α γ β : ℝ) (hβ : β ≠ 0) :
    ¬ ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ (X 1 : MvPolynomial (Fin 2) ℝ) ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α γ β)) p ∈ V := by
  apply no_finite_polynomial_closure_of_unbounded_totalDegree
  intro N
  refine ⟨N + 1, ?_⟩
  rw [lieIterate_second_totalDegree α γ β hβ]
  lia

end TwoModeBurgers
