/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.QuditCat.Composite
public import FQFP.CQM.QuditCat.Teleportation

/-!
# The density operator of the Bell resource

The Bell resource already used by the teleportation protocol determines a pure density
operator. Both reduced states are the maximally mixed qubit state, with operator `I / 2`.
This is the two-dimensional case of Watrous, *The Theory of Quantum Information*,
Example 2.8, equations (2.35)--(2.37).
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace QuditCat

noncomputable section

/-- The pure density operator of the existing normalized Bell resource. -/
def bellDensity : Density (Qubit ⊗ Qubit) := Density.pure (UnitState.ofBasis bellBasis 0)

/-- The Bell density uses precisely the state vector of the teleportation resource. -/
lemma bellDensity_op_eq_outer_bellState :
    bellDensity.op = Operator.outer (bellState (1 : ℂ)) (bellState (1 : ℂ)) := by
  rw [bellState_eq_ketArrow]
  change Operator.outer (bellBasis 0) (bellBasis 0) =
    Operator.outer ((1 : ℂ) • bellBasis 0) ((1 : ℂ) • bellBasis 0)
  rw [one_smul]

/-- The Bell density is one half times the outer square of the unnormalized Bell vector. -/
lemma bellDensity_op : bellDensity.op = (1 / 2 : ℂ) •
    Operator.outer (∑ i, ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 i)
      (∑ i, ZBasis 2 i ⊗ₜ[ℂ] ZBasis 2 i) := by
  rw [bellDensity_op_eq_outer_bellState, bellState_apply, one_smul,
    Operator.outer_smul_self, ← Complex.mul_conj', conj_bellFactor, bellFactor_mul_self]

/-- Discarding the right Bell qubit gives the identity divided by two. -/
lemma bellDensity_partialTraceRight_op :
    bellDensity.partialTraceRight.op = (1 / 2 : ℂ) • (1 : Operator Qubit) := by
  rw [Density.op_partialTraceRight, bellDensity_op, map_smul,
    Operator.partialTraceRight_outer_sum_basis]

/-- Discarding the left Bell qubit gives the identity divided by two. -/
lemma bellDensity_partialTraceLeft_op :
    bellDensity.partialTraceLeft.op = (1 / 2 : ℂ) • (1 : Operator Qubit) := by
  rw [Density.op_partialTraceLeft, bellDensity_op, map_smul,
    Operator.partialTraceLeft_outer_sum_basis]

/-- The left Bell marginal is the maximally mixed density state. -/
lemma bellDensity_partialTraceRight : bellDensity.partialTraceRight =
    Density.maximallyMixed Qubit (by simp [Qubit]) := by
  apply Density.ext
  rw [bellDensity_partialTraceRight_op, Density.op_maximallyMixed]
  simp [Qubit]

/-- The right Bell marginal is the maximally mixed density state. -/
lemma bellDensity_partialTraceLeft : bellDensity.partialTraceLeft =
    Density.maximallyMixed Qubit (by simp [Qubit]) := by
  apply Density.ext
  rw [bellDensity_partialTraceLeft_op, Density.op_maximallyMixed]
  simp [Qubit]

end

end QuditCat
