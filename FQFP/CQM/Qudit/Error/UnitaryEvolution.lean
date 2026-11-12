/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Error.TraceDistance

/-!
# Unitary evolution in the Hilbert operator algebra

This module connects unitary elements of the continuous operator algebra to qudit morphisms
and density-state evolution. The operator norm is the Hilbert-space operator norm throughout.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory

namespace Qudit

noncomputable section

variable {H : Qudit}

/-- A unitary element of the Hilbert operator algebra as a qudit endomorphism. -/
def unitaryHom (U : unitary (H.state →L[ℂ] H.state)) : H ⟶ H := ofHom U.val.toLinearMap

/-- A Hilbert operator unitary is unitary for the categorical dagger. -/
instance (U : unitary (H.state →L[ℂ] H.state)) : IsUnitary (unitaryHom U) := by
  rw [isUnitary_iff]
  constructor
  · apply hom_ext
    exact congrArg ContinuousLinearMap.toLinearMap (Unitary.star_mul_self_of_mem U.property)
  · apply hom_ext
    exact congrArg ContinuousLinearMap.toLinearMap (Unitary.mul_star_self_of_mem U.property)

namespace Density

/-- Unitary evolution, expressed in the Hilbert continuous-operator algebra. -/
def evolve (ρ : Density H) (U : unitary (H.state →L[ℂ] H.state)) : Density H :=
  ρ.map (unitaryHom U)

/-- Unitary evolution is conjugation of the density operator. -/
lemma op_evolve (ρ : Density H) (U : unitary (H.state →L[ℂ] H.state)) :
    (ρ.evolve U).op = U.val.toLinearMap * ρ.op * U.val.toLinearMap.adjoint := rfl

/-- The trace-norm error of unitary evolution is at most twice the operator error. -/
lemma traceNorm_evolve_sub_le (ρ : Density H) (U V : unitary (H.state →L[ℂ] H.state)) :
    LinearMap.traceNorm ((ρ.evolve U).op - (ρ.evolve V).op) ≤ 2 * ‖U.val - V.val‖ :=
  ρ.traceNorm_map_sub_le (unitaryHom U) (unitaryHom V)

/-- The trace distance of unitary outputs is bounded by their operator-norm difference. -/
lemma traceDistance_evolve_le_opNorm (ρ : Density H)
    (U V : unitary (H.state →L[ℂ] H.state)) :
    (ρ.evolve U).traceDistance (ρ.evolve V) ≤ ‖U.val - V.val‖ :=
  ρ.traceDistance_map_le_opNorm (unitaryHom U) (unitaryHom V)

/-- Transfer a supplied unitary operator error bound to trace distance. -/
lemma traceDistance_evolve_le (ρ : Density H)
    (U V : unitary (H.state →L[ℂ] H.state)) {ε : ℝ} (hε : ‖U.val - V.val‖ ≤ ε) :
    (ρ.evolve U).traceDistance (ρ.evolve V) ≤ ε :=
  (ρ.traceDistance_evolve_le_opNorm U V).trans hε

end Density

namespace POVM

/-- Transfer a supplied unitary operator error bound to each POVM probability. -/
lemma abs_probability_evolve_sub_le {ι : Type*} [Fintype ι] (M : POVM H ι)
    (ρ : Density H) (U V : unitary (H.state →L[ℂ] H.state)) {ε : ℝ}
    (hε : ‖U.val - V.val‖ ≤ ε) (i : ι) :
    |M.probability (ρ.evolve U) i - M.probability (ρ.evolve V) i| ≤ ε :=
  (M.abs_probability_sub_le_traceDistance _ _ i).trans (ρ.traceDistance_evolve_le U V hε)

end POVM

end

end Qudit
