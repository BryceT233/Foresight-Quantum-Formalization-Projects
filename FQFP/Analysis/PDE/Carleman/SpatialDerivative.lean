/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.PDE.Carleman.Operators
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Spatial derivatives on an explicit domain

Each component must be differentiable in its spatial variable. The partial
derivative is an algebraic linear map from that submodule to spatial fields.
It does not assert that the resulting field is differentiable again or that
the derivative operator is bounded in a Banach norm.

## Main definitions

* `Carleman.PDE.differentiableFields`: the submodule of componentwise differentiable fields.
* `Carleman.PDE.spatialDerivative`: a coordinate derivative on that domain.
* `Carleman.PDE.diagonalSpatialDerivative`: differentiation before diagonal restriction.
-/

@[expose] public noncomputable section

namespace Carleman.PDE

/-- Spatial fields with differentiable scalar components. -/
def differentiableFields (m n : ℕ) : Submodule ℝ (SpatialField m n) where
  carrier := {u | ∀ j, Differentiable ℝ (fun x => u x j)}
  zero_mem' := fun _ => differentiable_const _
  add_mem' hu hv := fun j => (hu j).add (hv j)
  smul_mem' a _ hu := fun j => (hu j).const_smul a

lemma mem_differentiableFields {m n : ℕ} (u : SpatialField m n) :
    u ∈ differentiableFields m n ↔ ∀ j, Differentiable ℝ (fun x => u x j) := Iff.rfl

/-- The spatial derivative along a coordinate direction, on differentiable fields. -/
def spatialDerivative {m n : ℕ} (i : Fin m) :
    differentiableFields m n →ₗ[ℝ] SpatialField m n where
  toFun u x j := fderiv ℝ (fun y => (u : SpatialField m n) y j) x (Pi.single i 1)
  map_add' u v := by
    ext x j
    change (fderiv ℝ ((fun y => (u : SpatialField m n) y j) +
      (fun y => (v : SpatialField m n) y j)) x) (Pi.single i 1) = _
    rw [fderiv_add (u.property j x) (v.property j x)]
    rfl
  map_smul' a u := by
    ext x j
    change (fderiv ℝ (a • (fun y => (u : SpatialField m n) y j)) x) (Pi.single i 1) = _
    rw [fderiv_const_smul (u.property j x) a]
    rfl

/-- A known Fréchet derivative determines the spatial coordinate derivative. -/
lemma spatialDerivative_eq {m n : ℕ} (u : differentiableFields m n)
    (x : Fin m → ℝ) (j : Fin n) (i : Fin m) (D : (Fin m → ℝ) →L[ℝ] ℝ)
    (hu : HasFDerivAt (fun y => (u : SpatialField m n) y j) D x) :
    spatialDerivative i u x j = D (Pi.single i 1) :=
  congrArg (fun A : (Fin m → ℝ) →L[ℝ] ℝ => A (Pi.single i 1)) hu.fderiv

/-- Differentiate the first point before restricting the second point to its diagonal.
The second component is fixed; the first component remains the output component. -/
def diagonalSpatialDerivative {m n : ℕ} (i : Fin m) (c : Fin n) :
    sliceDomain (slotSlice (m := m) (n := n) (0 : Fin 2)) (differentiableFields m n) →ₗ[ℝ]
      SpatialField m n :=
  LinearMap.pi fun x => LinearMap.pi fun j =>
    (LinearMap.proj j).comp ((LinearMap.proj x).comp
      ((spatialDerivative i).comp
        (domainSlice (slotSlice (0 : Fin 2)) (differentiableFields m n) ![x, x] ![j, c])))

/-- Differentiating one factor before diagonal restriction produces no extra chain-rule term. -/
lemma diagonalSpatialDerivative_multipointLift {m n : ℕ}
    (u : differentiableFields m n) (i : Fin m) (c j : Fin n) (x : Fin m → ℝ) :
    diagonalSpatialDerivative i c
        ⟨multipointLift (u : SpatialField m n),
          multipointLift_mem_slotDomain (differentiableFields m n) u (0 : Fin 2)⟩ x j =
      spatialDerivative i u x j * (u : SpatialField m n) x c := by
  have h := slicedAction_slotSlice_multipointLift (differentiableFields m n)
    (spatialDerivative i) u (0 : Fin 2) ![x, x] ![j, c]
  simpa [slicedAction, diagonalSpatialDerivative, Finset.univ_fin2] using h

end Carleman.PDE
