/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.PDE.Operators

/-!
# The linear multipoint hierarchy of a quadratic PDE

The state is a product over all levels, without a finite-support requirement.
The hierarchy operator is an algebraic linear map on the common domains of
its spatial blocks. Given a field satisfying the quadratic PDE, its true
multipoint lift satisfies this hierarchy at each fixed spatial coordinate.

No boundedness, function-space norm, global existence, or uniqueness of the
infinite hierarchy is asserted. Spatial operators retain their explicit domains.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Carleman.PDE

/-- An infinite sequence of multipoint fields, with no finite-support restriction. -/
abbrev Hierarchy (m n : ℕ) := ∀ k, MultipointField m n k

/-- The true multipoint lift at every level, including the constant level zero. -/
def liftHierarchy {m n : ℕ} (u : SpatialField m n) : Hierarchy m n :=
  fun _ => multipointLift u

/-- States admissible for every positive-level linear and quadratic spatial block. -/
def hierarchyDomain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) : Submodule ℝ (Hierarchy m n) :=
  (⨅ k, (blockDomain (slotSlice (k := k + 1)) S₁).comap (LinearMap.proj (k + 1))) ⊓
    ⨅ k, (blockDomain (pairSlice (k := k + 1)) S₂).comap (LinearMap.proj (k + 2))

lemma mem_hierarchyDomain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (Y : Hierarchy m n) :
    Y ∈ hierarchyDomain S₁ S₂ ↔
      (∀ k, Y (k + 1) ∈ blockDomain slotSlice S₁) ∧
        ∀ k, Y (k + 2) ∈ blockDomain pairSlice S₂ := by
  simp [hierarchyDomain]

/-- Read a level of an admissible hierarchy in the domain of its linear block. -/
def hierarchyLinearProjection {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (k : ℕ) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] blockDomain (slotSlice (k := k + 1)) S₁ :=
  ((LinearMap.proj (k + 1)).comp (hierarchyDomain S₁ S₂).subtype).codRestrict _
    (fun Y => ((mem_hierarchyDomain S₁ S₂ Y).mp Y.property).1 k)

/-- Read the next level in the domain of a quadratic hierarchy block. -/
def hierarchyQuadraticProjection {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (k : ℕ) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] blockDomain (pairSlice (k := k + 1)) S₂ :=
  ((LinearMap.proj (k + 2)).comp (hierarchyDomain S₁ S₂).subtype).codRestrict _
    (fun Y => ((mem_hierarchyDomain S₁ S₂ Y).mp Y.property).2 k)

/-- The tridiagonal linear hierarchy, with zero derivative at the constant level. -/
def hierarchyOperator {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (c : SpatialField m n)
    (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] Hierarchy m n :=
  LinearMap.pi fun
    | 0 => 0
    | k + 1 => (forcingBlock c).comp
        ((LinearMap.proj k).comp (hierarchyDomain S₁ S₂).subtype) +
      (linearBlock S₁ L).comp (hierarchyLinearProjection S₁ S₂ k) +
      (quadraticBlock S₂ Q).comp (hierarchyQuadraticProjection S₁ S₂ k)

lemma hierarchyOperator_zero {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (c : SpatialField m n)
    (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) : hierarchyOperator S₁ S₂ c L Q Y 0 = 0 := rfl

lemma hierarchyOperator_succ {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (c : SpatialField m n)
    (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) (k : ℕ) :
    hierarchyOperator S₁ S₂ c L Q Y (k + 1) =
      forcingBlock c ((Y : Hierarchy m n) k) +
        linearBlock S₁ L (hierarchyLinearProjection S₁ S₂ k Y) +
        quadraticBlock S₂ Q (hierarchyQuadraticProjection S₁ S₂ k Y) := rfl

lemma liftHierarchy_mem_domain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (u : S₁)
    (hu : (multipointLift (u : SpatialField m n) : MultipointField m n 2) ∈ S₂) :
    liftHierarchy (u : SpatialField m n) ∈ hierarchyDomain S₁ S₂ := by
  rw [mem_hierarchyDomain]
  exact ⟨fun _ => multipointLift_mem_linearBlockDomain S₁ u,
    fun _ => multipointLift_mem_quadraticBlockDomain S₂ _ hu⟩

/-- On true lifts, the linear hierarchy reads the PDE right-hand side in each factor. -/
lemma hierarchyOperator_liftHierarchy {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : SpatialField m n) (hL : u ∈ S₁)
    (hu : (multipointLift u : MultipointField m n 2) ∈ S₂)
    (xs : Fin (k + 1) → (Fin m → ℝ)) (js : Fin (k + 1) → Fin n) :
    hierarchyOperator S₁ S₂ c L Q
        ⟨liftHierarchy u, liftHierarchy_mem_domain S₁ S₂ ⟨u, hL⟩ hu⟩
        (k + 1) xs js =
      ∑ p : Fin (k + 1),
        (c (xs p) (js p) + L ⟨u, hL⟩ (xs p) (js p) +
          Q ⟨multipointLift u, hu⟩ (xs p) (js p)) *
          ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  change forcingBlock c (multipointLift u) xs js +
    linearBlock S₁ L
      ⟨multipointLift u, multipointLift_mem_linearBlockDomain S₁ ⟨u, hL⟩⟩ xs js +
    quadraticBlock S₂ Q
      ⟨multipointLift u,
        multipointLift_mem_quadraticBlockDomain S₂ _ hu⟩ xs js = _
  rw [forcingBlock_multipointLift,
    linearBlock_multipointLift S₁ L ⟨u, hL⟩ xs js,
    quadraticBlock_multipointLift S₂ Q u hu xs js]
  simp only [add_mul, Finset.sum_add_distrib]

/-- The zero-level lift is constant without any differentiability assumption on the field. -/
lemma hasDerivWithinAt_liftHierarchy_zero {m n : ℕ} (u : ℝ → SpatialField m n)
    (xs : Fin 0 → (Fin m → ℝ)) (js : Fin 0 → Fin n) (I : Set ℝ) (t : ℝ) :
    HasDerivWithinAt (fun s => liftHierarchy (u s) 0 xs js) 0 I t := by
  simpa only [liftHierarchy, multipointLift_zero] using hasDerivWithinAt_const t I (1 : ℝ)

/-- A solution of the quadratic PDE lifts to the linear hierarchy, including interval endpoints. -/
lemma hasDerivWithinAt_liftHierarchy {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : ℝ → SpatialField m n) (I : Set ℝ) (t : ℝ) (hL : u t ∈ S₁)
    (hQ : (multipointLift (u t) : MultipointField m n 2) ∈ S₂)
    (hu : ∀ x j, HasDerivWithinAt (fun s => u s x j)
      (c x j + L ⟨u t, hL⟩ x j + Q ⟨multipointLift (u t), hQ⟩ x j) I t)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    HasDerivWithinAt (fun s => liftHierarchy (u s) k xs js)
      (hierarchyOperator S₁ S₂ c L Q
        ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩ k xs js) I t := by
  cases k with
  | zero =>
    exact hasDerivWithinAt_liftHierarchy_zero u xs js I t
  | succ k =>
    rw [hierarchyOperator_liftHierarchy S₁ S₂ c L Q (u t) hL hQ xs js]
    exact hasDerivWithinAt_multipointLift u
      (c + L ⟨u t, hL⟩ + Q ⟨multipointLift (u t), hQ⟩) xs js I t
      (fun p => hu (xs p) (js p))

/-- A pointwise classical solution of the quadratic PDE lifts to the linear hierarchy. -/
lemma hasDerivAt_liftHierarchy {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : ℝ → SpatialField m n) (t : ℝ) (hL : u t ∈ S₁)
    (hQ : (multipointLift (u t) : MultipointField m n 2) ∈ S₂)
    (hu : ∀ x j, HasDerivAt (fun s => u s x j)
      (c x j + L ⟨u t, hL⟩ x j + Q ⟨multipointLift (u t), hQ⟩ x j) t)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    HasDerivAt (fun s => liftHierarchy (u s) k xs js)
      (hierarchyOperator S₁ S₂ c L Q
        ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩ k xs js) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_liftHierarchy S₁ S₂ c L Q u Set.univ t hL hQ
    (fun x j => (hu x j).hasDerivWithinAt) xs js

end Carleman.PDE
