/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Operator
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The operator norm on qudit operators

Finite dimensionality identifies the linear endomorphisms of a qudit with its bounded
operators. Transporting the Hilbert operator norm along this equivalence equips the existing
operator algebra with its complete C⋆-norm.
-/

@[expose] public section

namespace Qudit.Operator

noncomputable section

variable (H : Qudit)

/-- The Hilbert-space operator norm on qudit endomorphisms. -/
instance : NormedRing (Operator H) :=
  NormedRing.induced _ _ (Module.End.toContinuousLinearMap H.state)
    (Module.End.toContinuousLinearMap H.state).injective

instance : NormedAlgebra ℂ (Operator H) :=
  NormedAlgebra.induced ℂ _ _ (Module.End.toContinuousLinearMap H.state)

instance : CompleteSpace (Operator H) := FiniteDimensional.complete ℂ _

instance : CStarRing (Operator H) where
  norm_mul_self_le A := CStarRing.norm_mul_self_le (LinearMap.toContinuousLinearMap A)

instance : CStarAlgebra (Operator H) where

/-- The Loewner order on operators is the order of their C⋆-algebra. -/
instance : StarOrderedRing (Operator H) :=
  StarOrderedRing.of_nonneg_iff' (fun h z => add_le_add_right h z) fun A => by
    constructor
    · intro h
      obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
        (show 0 ≤ LinearMap.toContinuousLinearMap A from h)
      exact ⟨B.toLinearMap, congrArg ContinuousLinearMap.toLinearMap hB⟩
    · rintro ⟨B, rfl⟩
      exact star_mul_self_nonneg (LinearMap.toContinuousLinearMap B)

/-- Viewing a qudit operator as a continuous linear map preserves the operator norm. -/
def continuousLinearMapEquiv : Operator H ≃ₗᵢ[ℂ] (H.state →L[ℂ] H.state) where
  toLinearEquiv := (Module.End.toContinuousLinearMap H.state).toLinearEquiv
  norm_map' _ := rfl

/-- Mathlib's operator norm agrees with the norm on qudit operators. -/
@[simp] theorem norm_toContinuousLinearMap {H : Qudit} (A : Operator H) :
    ‖LinearMap.toContinuousLinearMap A‖ = ‖A‖ := rfl

end

end Qudit.Operator
