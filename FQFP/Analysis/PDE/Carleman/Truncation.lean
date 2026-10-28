/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.PDE.Carleman.Hierarchy
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Finite-level truncation and the discarded coupling

Truncation retains levels `0, ..., N`, including the constant level, and extends
the remaining levels by zero. Its spatial domain is the preimage of the infinite
hierarchy domain under this extension. The compressed operator is `π_N A ι_N`.
The exact projected hierarchy differs from this operator only by the quadratic
coupling from level `N + 1` into the highest retained positive level.

Each level is still a field on continuous spatial coordinates. No finite-dimensional spatial
discretization, boundedness, existence theorem, or convergence estimate is assumed.

## Main definitions

* `Carleman.PDE.truncatedHierarchyOperator`: the finite-level compressed operator.
* `Carleman.PDE.truncationResidual`: the exact discarded coupling.

## Main results

* `Carleman.PDE.hasDerivWithinAt_truncationError`: the error against a truncated solution.
-/

@[expose] public noncomputable section

namespace Carleman.PDE

/-- The dependent product of multipoint fields at levels zero through `N`. -/
abbrev TruncatedHierarchy (m n N : ℕ) := ∀ k : Fin (N + 1), MultipointField m n k.val

/-- Retain the first `N + 1` levels of an infinite hierarchy. -/
def hierarchyProjection {m n : ℕ} (N : ℕ) :
    Hierarchy m n →ₗ[ℝ] TruncatedHierarchy m n N :=
  LinearMap.pi fun k => LinearMap.proj k.val

/-- Extend a finite hierarchy by zero above level `N`. -/
def hierarchyExtension {m n : ℕ} (N : ℕ) :
    TruncatedHierarchy m n N →ₗ[ℝ] Hierarchy m n :=
  LinearMap.pi fun k =>
    if h : k < N + 1 then LinearMap.proj (⟨k, h⟩ : Fin (N + 1)) else 0

@[simp]
lemma hierarchyProjection_apply {m n N : ℕ} (Y : Hierarchy m n) (k : Fin (N + 1)) :
    hierarchyProjection N Y k = Y k.val := rfl

lemma hierarchyExtension_apply {m n N : ℕ} (Z : TruncatedHierarchy m n N) (k : ℕ) :
    hierarchyExtension N Z k = if h : k < N + 1 then Z ⟨k, h⟩ else 0 := by
  simp only [hierarchyExtension, LinearMap.pi_apply]
  by_cases h : k < N + 1
  · rw [dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

@[simp]
lemma hierarchyProjection_extension {m n N : ℕ} (Z : TruncatedHierarchy m n N) :
    hierarchyProjection N (hierarchyExtension N Z) = Z := by
  funext k
  simp [hierarchyExtension_apply, k.isLt]

lemma hierarchyExtension_projection_apply {m n N : ℕ} (Y : Hierarchy m n) (k : ℕ) :
    hierarchyExtension N (hierarchyProjection N Y) k =
      if k < N + 1 then Y k else 0 := by
  rw [hierarchyExtension_apply]
  split_ifs <;> rfl

/-- A finite state is admissible precisely when its zero extension is admissible. -/
def truncatedHierarchyDomain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) :
    Submodule ℝ (TruncatedHierarchy m n N) :=
  (hierarchyDomain S₁ S₂).comap (hierarchyExtension N)

lemma mem_truncatedHierarchyDomain {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (Z : TruncatedHierarchy m n N) :
    Z ∈ truncatedHierarchyDomain S₁ S₂ N ↔
      (∀ k (h : k + 1 < N + 1), Z ⟨k + 1, h⟩ ∈ blockDomain slotSlice S₁) ∧
        ∀ k (h : k + 2 < N + 1), Z ⟨k + 2, h⟩ ∈ blockDomain pairSlice S₂ := by
  change hierarchyExtension N Z ∈ hierarchyDomain S₁ S₂ ↔ _
  rw [mem_hierarchyDomain]
  simp only [hierarchyExtension_apply]
  constructor
  · rintro ⟨hL, hQ⟩
    exact ⟨fun k h => by simpa [h] using hL k,
      fun k h => by simpa [h] using hQ k⟩
  · rintro ⟨hL, hQ⟩
    constructor
    · intro k
      split_ifs with h
      · exact hL k h
      · exact Submodule.zero_mem _
    · intro k
      split_ifs with h
      · exact hQ k h
      · exact Submodule.zero_mem _

lemma hierarchyProjection_mem_domain {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (Y : hierarchyDomain S₁ S₂) :
    hierarchyProjection N (Y : Hierarchy m n) ∈ truncatedHierarchyDomain S₁ S₂ N := by
  rw [mem_truncatedHierarchyDomain]
  exact ⟨fun k _ => ((mem_hierarchyDomain S₁ S₂ Y).mp Y.property).1 k,
    fun k _ => ((mem_hierarchyDomain S₁ S₂ Y).mp Y.property).2 k⟩

/-- Projection with the finite spatial domain recorded in its codomain. -/
def hierarchyProjectionDomain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] truncatedHierarchyDomain S₁ S₂ N :=
  ((hierarchyProjection N).comp (hierarchyDomain S₁ S₂).subtype).codRestrict _
    (hierarchyProjection_mem_domain S₁ S₂)

/-- Zero extension with the infinite spatial domain recorded in its codomain. -/
def hierarchyExtensionDomain {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) :
    truncatedHierarchyDomain S₁ S₂ N →ₗ[ℝ] hierarchyDomain S₁ S₂ :=
  ((hierarchyExtension N).comp (truncatedHierarchyDomain S₁ S₂ N).subtype).codRestrict _
    (fun Z => Z.property)

/-- The admissible tail discarded by projection and zero extension. -/
def hierarchyTail {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] hierarchyDomain S₁ S₂ :=
  LinearMap.id - (hierarchyExtensionDomain S₁ S₂ N).comp
    (hierarchyProjectionDomain S₁ S₂ N)

lemma hierarchyTail_apply {m n N : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (Y : hierarchyDomain S₁ S₂) (k : ℕ) :
    (hierarchyTail S₁ S₂ N Y : Hierarchy m n) k =
      if k < N + 1 then 0 else (Y : Hierarchy m n) k := by
  change (Y : Hierarchy m n) k - hierarchyExtension N (hierarchyProjection N Y) k = _
  rw [hierarchyExtension_projection_apply]
  split_ifs <;> simp

/-- The compressed hierarchy operator `π_N A ι_N`, with explicit spatial domain. -/
def truncatedHierarchyOperator {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) (c : SpatialField m n)
    (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n) :
    truncatedHierarchyDomain S₁ S₂ N →ₗ[ℝ] TruncatedHierarchy m n N :=
  (hierarchyProjection N).comp ((hierarchyOperator S₁ S₂ c L Q).comp
    (hierarchyExtensionDomain S₁ S₂ N))

/-- The projected action of the discarded tail, as an exact linear residual. -/
def truncationResidual {m n : ℕ} (S₁ : Submodule ℝ (SpatialField m n))
    (S₂ : Submodule ℝ (MultipointField m n 2)) (N : ℕ) (c : SpatialField m n)
    (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n) :
    hierarchyDomain S₁ S₂ →ₗ[ℝ] TruncatedHierarchy m n N :=
  (hierarchyProjection N).comp ((hierarchyOperator S₁ S₂ c L Q).comp
    (hierarchyTail S₁ S₂ N))

lemma hierarchyProjection_operator {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) :
    hierarchyProjection N (hierarchyOperator S₁ S₂ c L Q Y) =
      truncatedHierarchyOperator S₁ S₂ N c L Q (hierarchyProjectionDomain S₁ S₂ N Y) +
        truncationResidual S₁ S₂ N c L Q Y := by
  change hierarchyProjection N (hierarchyOperator S₁ S₂ c L Q Y) =
    hierarchyProjection N (hierarchyOperator S₁ S₂ c L Q _) +
      hierarchyProjection N (hierarchyOperator S₁ S₂ c L Q (Y - _))
  rw [map_sub, map_sub]
  simp only [LinearMap.comp_apply]
  abel

/-- The constant level is stationary in the truncated system. -/
lemma truncatedHierarchyOperator_zero {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Z : truncatedHierarchyDomain S₁ S₂ N) :
    truncatedHierarchyOperator S₁ S₂ N c L Q Z 0 = 0 := rfl

lemma truncationResidual_zero {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) : truncationResidual S₁ S₂ N c L Q Y 0 = 0 := rfl

/-- Every positive row strictly below the cutoff has zero residual. -/
lemma truncationResidual_below {m n N k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) (h : k + 1 < N) :
    truncationResidual S₁ S₂ N c L Q Y ⟨k + 1, by lia⟩ = 0 := by
  have hprev : (hierarchyTail S₁ S₂ N Y : Hierarchy m n) k = 0 := by
    rw [hierarchyTail_apply, ite_eq_left (by lia)]
  have hL : hierarchyLinearProjection S₁ S₂ k (hierarchyTail S₁ S₂ N Y) = 0 := by
    apply Subtype.ext
    change (hierarchyTail S₁ S₂ N Y : Hierarchy m n) (k + 1) = 0
    rw [hierarchyTail_apply, ite_eq_left (by lia)]
  have hQ : hierarchyQuadraticProjection S₁ S₂ k (hierarchyTail S₁ S₂ N Y) = 0 := by
    apply Subtype.ext
    change (hierarchyTail S₁ S₂ N Y : Hierarchy m n) (k + 2) = 0
    rw [hierarchyTail_apply, ite_eq_left (by lia)]
  change hierarchyOperator S₁ S₂ c L Q (hierarchyTail S₁ S₂ N Y) (k + 1) = 0
  rw [hierarchyOperator_succ, hprev, hL, hQ]
  simp only [map_zero, add_zero]

/-- At a positive cutoff, the residual is exactly the discarded quadratic coupling. -/
lemma truncationResidual_last {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) :
    truncationResidual S₁ S₂ (k + 1) c L Q Y ⟨k + 1, by lia⟩ =
      quadraticBlock S₂ Q (hierarchyQuadraticProjection S₁ S₂ k Y) := by
  have hprev : (hierarchyTail S₁ S₂ (k + 1) Y : Hierarchy m n) k = 0 := by
    rw [hierarchyTail_apply, ite_eq_left (by lia)]
  have hL : hierarchyLinearProjection S₁ S₂ k (hierarchyTail S₁ S₂ (k + 1) Y) = 0 := by
    apply Subtype.ext
    change (hierarchyTail S₁ S₂ (k + 1) Y : Hierarchy m n) (k + 1) = 0
    rw [hierarchyTail_apply, ite_eq_left (by lia)]
  have hQ : hierarchyQuadraticProjection S₁ S₂ k (hierarchyTail S₁ S₂ (k + 1) Y) =
      hierarchyQuadraticProjection S₁ S₂ k Y := by
    apply Subtype.ext
    change (hierarchyTail S₁ S₂ (k + 1) Y : Hierarchy m n) (k + 2) = _
    rw [hierarchyTail_apply, ite_eq_right (by lia)]
    rfl
  change hierarchyOperator S₁ S₂ c L Q (hierarchyTail S₁ S₂ (k + 1) Y) (k + 1) = _
  rw [hierarchyOperator_succ, hprev, hL, hQ]
  simp only [map_zero, zero_add]

/-- Away from the highest retained level the residual vanishes, including level zero. -/
lemma truncationResidual_eq_zero_of_ne {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) (i : Fin (N + 1)) (h : i.val ≠ N) :
    truncationResidual S₁ S₂ N c L Q Y i = 0 := by
  obtain ⟨i, hi⟩ := i
  cases i with
  | zero => exact truncationResidual_zero S₁ S₂ c L Q Y
  | succ k => exact truncationResidual_below S₁ S₂ c L Q Y (by lia)

/-- Truncation at level zero discards no coupling into the constant level. -/
lemma truncationResidual_order_zero {m n : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) : truncationResidual S₁ S₂ 0 c L Q Y = 0 := by
  funext i; fin_cases i; rfl

/-- The top row of the compressed operator has no upward quadratic block. -/
lemma truncatedHierarchyOperator_last {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Z : truncatedHierarchyDomain S₁ S₂ (k + 1)) :
    truncatedHierarchyOperator S₁ S₂ (k + 1) c L Q Z ⟨k + 1, by lia⟩ =
      forcingBlock c ((Z : TruncatedHierarchy m n (k + 1)) ⟨k, by lia⟩) +
        linearBlock S₁ L (hierarchyLinearProjection S₁ S₂ k
          (hierarchyExtensionDomain S₁ S₂ (k + 1) Z)) := by
  have hprev : (hierarchyExtensionDomain S₁ S₂ (k + 1) Z : Hierarchy m n) k =
      (Z : TruncatedHierarchy m n (k + 1)) ⟨k, by lia⟩ := by
    change hierarchyExtension (k + 1) (Z : TruncatedHierarchy m n (k + 1)) k = _
    rw [hierarchyExtension_apply, dite_eq_left (by lia)]
  have hQ : hierarchyQuadraticProjection S₁ S₂ k
      (hierarchyExtensionDomain S₁ S₂ (k + 1) Z) = 0 := by
    apply Subtype.ext
    change hierarchyExtension (k + 1) (Z : TruncatedHierarchy m n (k + 1)) (k + 2) = 0
    rw [hierarchyExtension_apply, dite_eq_right (by lia)]
  change hierarchyOperator S₁ S₂ c L Q (hierarchyExtensionDomain S₁ S₂ (k + 1) Z)
    (k + 1) = _
  rw [hierarchyOperator_succ, hprev, hQ, map_zero, add_zero]

/-- Projecting an admissible hierarchy preserves every operator row below the cutoff. -/
lemma truncatedHierarchyOperator_projection_below {m n N k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : hierarchyDomain S₁ S₂) (h : k + 1 < N) :
    truncatedHierarchyOperator S₁ S₂ N c L Q (hierarchyProjectionDomain S₁ S₂ N Y)
        ⟨k + 1, by lia⟩ = hierarchyOperator S₁ S₂ c L Q Y (k + 1) := by
  have heq := congrFun (hierarchyProjection_operator S₁ S₂ c L Q Y)
    (⟨k + 1, by lia⟩ : Fin (N + 1))
  simp only [hierarchyProjection_apply, Pi.add_apply] at heq
  rw [truncationResidual_below S₁ S₂ c L Q Y h, add_zero] at heq
  exact heq.symm

/-- True lifts express the top residual by applying the quadratic PDE term in each factor. -/
lemma truncationResidual_liftHierarchy_last {m n k : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : SpatialField m n) (hL : u ∈ S₁)
    (hQ : (multipointLift u : MultipointField m n 2) ∈ S₂)
    (xs : Fin (k + 1) → (Fin m → ℝ)) (js : Fin (k + 1) → Fin n) :
    truncationResidual S₁ S₂ (k + 1) c L Q
        ⟨liftHierarchy u, liftHierarchy_mem_domain S₁ S₂ ⟨u, hL⟩ hQ⟩
        ⟨k + 1, by lia⟩ xs js =
      ∑ p : Fin (k + 1), Q ⟨multipointLift u, hQ⟩ (xs p) (js p) *
        ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  rw [truncationResidual_last]
  exact quadraticBlock_multipointLift S₂ Q u hQ xs js

/-- An affine field equation has no discarded upward coupling at any cutoff. -/
lemma truncationResidual_quadratic_zero {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Y : hierarchyDomain S₁ S₂) :
    truncationResidual S₁ S₂ N c L 0 Y = 0 := by
  funext i
  by_cases hi : i.val = N
  · cases N with
    | zero =>
      rw [truncationResidual_order_zero]
    | succ k =>
      have heq : i = ⟨k + 1, by lia⟩ := Fin.ext hi
      subst i
      rw [truncationResidual_last]
      funext xs js
      simp [quadraticBlock, slotBlock, slicedAction]
  · exact truncationResidual_eq_zero_of_ne S₁ S₂ c L 0 Y i hi

/-- Projected true lifts always have constant value one at level zero. -/
lemma hierarchyProjection_liftHierarchy_zero {m n N : ℕ} (u : SpatialField m n)
    (xs : Fin 0 → (Fin m → ℝ)) (js : Fin 0 → Fin n) :
    hierarchyProjection N (liftHierarchy u) 0 xs js = 1 := multipointLift_zero u xs js

/-- A given hierarchy trajectory satisfies the exact truncated equation with residual. -/
lemma hasDerivWithinAt_projectedHierarchy {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : ℝ → Hierarchy m n) (I : Set ℝ) (t : ℝ) (hY : Y t ∈ hierarchyDomain S₁ S₂)
    (hderiv : ∀ k xs js, HasDerivWithinAt (fun s => Y s k xs js)
      (hierarchyOperator S₁ S₂ c L Q ⟨Y t, hY⟩ k xs js) I t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivWithinAt (fun s => hierarchyProjection N (Y s) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q
        (hierarchyProjectionDomain S₁ S₂ N ⟨Y t, hY⟩) +
          truncationResidual S₁ S₂ N c L Q ⟨Y t, hY⟩) i xs js) I t := by
  rw [← hierarchyProjection_operator]
  exact hderiv i.val xs js

/-- The projected hierarchy equation at an ordinary time-derivative point. -/
lemma hasDerivAt_projectedHierarchy {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : ℝ → Hierarchy m n) (t : ℝ) (hY : Y t ∈ hierarchyDomain S₁ S₂)
    (hderiv : ∀ k xs js, HasDerivAt (fun s => Y s k xs js)
      (hierarchyOperator S₁ S₂ c L Q ⟨Y t, hY⟩ k xs js) t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivAt (fun s => hierarchyProjection N (Y s) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q
        (hierarchyProjectionDomain S₁ S₂ N ⟨Y t, hY⟩) +
          truncationResidual S₁ S₂ N c L Q ⟨Y t, hY⟩) i xs js) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_projectedHierarchy S₁ S₂ c L Q Y Set.univ t hY
    (fun k xs js => (hderiv k xs js).hasDerivWithinAt) i xs js

/-- A true PDE lift satisfies the truncated equation with its exact discarded coupling. -/
lemma hasDerivWithinAt_truncatedLiftHierarchy {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : ℝ → SpatialField m n) (I : Set ℝ) (t : ℝ) (hL : u t ∈ S₁)
    (hQ : (multipointLift (u t) : MultipointField m n 2) ∈ S₂)
    (hu : ∀ x j, HasDerivWithinAt (fun s => u s x j)
      (c x j + L ⟨u t, hL⟩ x j + Q ⟨multipointLift (u t), hQ⟩ x j) I t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivWithinAt (fun s => hierarchyProjection N (liftHierarchy (u s)) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q (hierarchyProjectionDomain S₁ S₂ N
        ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩) +
          truncationResidual S₁ S₂ N c L Q
            ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩)
        i xs js) I t := by
  exact hasDerivWithinAt_projectedHierarchy S₁ S₂ c L Q (fun s => liftHierarchy (u s))
    I t (liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ)
    (fun _ xs js => hasDerivWithinAt_liftHierarchy S₁ S₂ c L Q u I t hL hQ hu xs js)
    i xs js

/-- The exact finite-level PDE lift equation at an ordinary time-derivative point. -/
lemma hasDerivAt_truncatedLiftHierarchy {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (u : ℝ → SpatialField m n) (t : ℝ) (hL : u t ∈ S₁)
    (hQ : (multipointLift (u t) : MultipointField m n 2) ∈ S₂)
    (hu : ∀ x j, HasDerivAt (fun s => u s x j)
      (c x j + L ⟨u t, hL⟩ x j + Q ⟨multipointLift (u t), hQ⟩ x j) t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivAt (fun s => hierarchyProjection N (liftHierarchy (u s)) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q (hierarchyProjectionDomain S₁ S₂ N
        ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩) +
          truncationResidual S₁ S₂ N c L Q
            ⟨liftHierarchy (u t), liftHierarchy_mem_domain S₁ S₂ ⟨u t, hL⟩ hQ⟩)
        i xs js) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_truncatedLiftHierarchy S₁ S₂ c L Q u Set.univ t hL hQ
    (fun x j => (hu x j).hasDerivWithinAt) i xs js

/-- The error against any given truncated solution satisfies `E' = A_N E + r_N`. -/
lemma hasDerivWithinAt_truncationError {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : ℝ → Hierarchy m n) (Z : ℝ → TruncatedHierarchy m n N)
    (I : Set ℝ) (t : ℝ) (hY : Y t ∈ hierarchyDomain S₁ S₂)
    (hZ : Z t ∈ truncatedHierarchyDomain S₁ S₂ N)
    (hderivY : ∀ k xs js, HasDerivWithinAt (fun s => Y s k xs js)
      (hierarchyOperator S₁ S₂ c L Q ⟨Y t, hY⟩ k xs js) I t)
    (hderivZ : ∀ i xs js, HasDerivWithinAt (fun s => Z s i xs js)
      (truncatedHierarchyOperator S₁ S₂ N c L Q ⟨Z t, hZ⟩ i xs js) I t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivWithinAt (fun s => (hierarchyProjection N (Y s) - Z s) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q
        (hierarchyProjectionDomain S₁ S₂ N ⟨Y t, hY⟩ - ⟨Z t, hZ⟩) +
          truncationResidual S₁ S₂ N c L Q ⟨Y t, hY⟩) i xs js) I t := by
  have h := HasDerivWithinAt.sub
    (hasDerivWithinAt_projectedHierarchy S₁ S₂ c L Q Y I t hY hderivY i xs js)
    (hderivZ i xs js)
  convert h using 1
  rw [map_sub]
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The finite-level error equation at an ordinary time-derivative point. -/
lemma hasDerivAt_truncationError {m n N : ℕ}
    (S₁ : Submodule ℝ (SpatialField m n)) (S₂ : Submodule ℝ (MultipointField m n 2))
    (c : SpatialField m n) (L : S₁ →ₗ[ℝ] SpatialField m n) (Q : S₂ →ₗ[ℝ] SpatialField m n)
    (Y : ℝ → Hierarchy m n) (Z : ℝ → TruncatedHierarchy m n N)
    (t : ℝ) (hY : Y t ∈ hierarchyDomain S₁ S₂)
    (hZ : Z t ∈ truncatedHierarchyDomain S₁ S₂ N)
    (hderivY : ∀ k xs js, HasDerivAt (fun s => Y s k xs js)
      (hierarchyOperator S₁ S₂ c L Q ⟨Y t, hY⟩ k xs js) t)
    (hderivZ : ∀ i xs js, HasDerivAt (fun s => Z s i xs js)
      (truncatedHierarchyOperator S₁ S₂ N c L Q ⟨Z t, hZ⟩ i xs js) t)
    (i : Fin (N + 1)) (xs : Fin i.val → (Fin m → ℝ)) (js : Fin i.val → Fin n) :
    HasDerivAt (fun s => (hierarchyProjection N (Y s) - Z s) i xs js)
      ((truncatedHierarchyOperator S₁ S₂ N c L Q
        (hierarchyProjectionDomain S₁ S₂ N ⟨Y t, hY⟩ - ⟨Z t, hZ⟩) +
          truncationResidual S₁ S₂ N c L Q ⟨Y t, hY⟩) i xs js) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_truncationError S₁ S₂ c L Q Y Z Set.univ t hY hZ
    (fun k xs js => (hderivY k xs js).hasDerivWithinAt)
    (fun i xs js => (hderivZ i xs js).hasDerivWithinAt) i xs js

end Carleman.PDE
