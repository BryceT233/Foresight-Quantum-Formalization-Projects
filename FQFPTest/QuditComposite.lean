/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Composite-state regressions

These clients check the direction of reduction with unequal factor dimensions, pure-state
compatibility, zero-dimensional discarded factors, basis-independent local Bell statistics,
and a forbidden joint Bell outcome. In particular, uniform marginals do not assert that
the joint state is an independent product.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Qudit
open scoped TensorProduct

noncomputable section

local notation "ρ₀" => Density.pure (UnitState.ofBasis (ZBasis 2) (0 : Fin 2))
local notation "σ₂" => Density.pure (UnitState.ofBasis (ZBasis 3) (2 : Fin 3))
local notation "E₀" => Operator.outer (ZBasis 2 0) (ZBasis 2 0)
local notation "E₁" => Operator.outer (ZBasis 2 1) (ZBasis 2 1)

-- The right subsystem is the qutrit, so discarding it leaves the qubit.
example : ((ρ₀).tensor σ₂).partialTraceRight = ρ₀ := by simp

example : ((ρ₀).tensor σ₂).partialTraceLeft = σ₂ := by simp

-- The pure embedding uses the same Hilbert tensor product as the existing category.
example {H K : Qudit} (v : UnitState H) (w : UnitState K) :
    (Density.pure (v.tensor w)).partialTraceRight = Density.pure v := by
  rw [← Density.tensor_pure]
  simp

-- Partial trace acts on all operators, including a zero-dimensional discarded factor.
example {H : Qudit} (A : Operator H) :
    Operator.partialTraceRight (Operator.tensor A (1 : Operator (std 0))) = 0 := by
  simp [Operator.trace, LinearMap.trace_one]

-- Even after discarding half of a mixture of entangled and product states, mass stays one.
example (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (Density.mix p hp₀ hp₁ bellDensity ((ρ₀).tensor ρ₀)).partialTraceRight =
      Density.mix p hp₀ hp₁ bellDensity.partialTraceRight ρ₀ := by
  rw [Density.partialTraceRight_mix]
  simp

-- Every orthonormal measurement basis sees probability 1/2 on either Bell marginal.
example (b : OrthonormalBasis (Fin 2) ℂ Qubit.state) (i : Fin 2) :
    bellDensity.partialTraceRight.expectation (Operator.outer (b i) (b i)) = 1 / 2 := by
  unfold Density.expectation Density.expectationComplex
  rw [bellDensity_partialTraceRight_op, mul_smul_comm, mul_one]
  simp [Operator.trace, Operator.outer, LinearMap.trace_smulRight, bra]

example (b : OrthonormalBasis (Fin 2) ℂ Qubit.state) (i : Fin 2) :
    bellDensity.partialTraceLeft.expectation (Operator.outer (b i) (b i)) = 1 / 2 := by
  unfold Density.expectation Density.expectationComplex
  rw [bellDensity_partialTraceLeft_op, mul_smul_comm, mul_one]
  simp [Operator.trace, Operator.outer, LinearMap.trace_smulRight, bra]

-- The mismatched joint outcome (0,1) has probability zero in the Bell state.
example : bellDensity.expectation (Operator.tensor E₀ E₁) = 0 := by
  rw [bellDensity, Density.expectation_pure]
  simp [bellBasis_apply, bellVector, Operator.tensor_apply, Operator.outer_apply]

-- The maximally mixed constructor exposes the correct dimension to clients.
example : (Density.maximallyMixed (std 3) (by simp)).op =
    (1 / 3 : ℂ) • (1 : Operator (std 3)) := by simp

end
