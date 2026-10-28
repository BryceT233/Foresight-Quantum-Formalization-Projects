/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Matrix exponential trajectories

## Main results

* `Matrix.hasDerivAt_exp_smul_mulVec`: the matrix exponential solves the matrix-vector ODE.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Matrix

lemma hasDerivAt_exp_smul_mulVec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v₀ : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => (NormedSpace.exp (s • A)).mulVec v₀)
      (A.mulVec ((NormedSpace.exp (t • A)).mulVec v₀)) t := by
  let : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  let f : Matrix ι ι ℝ →L[ℝ] (ι → ℝ) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecBilin ℝ ℝ).flip v₀)
  convert f.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t) using 1
  · rfl
  · exact Matrix.mulVec_mulVec v₀ A (NormedSpace.exp (t • A))

end Matrix
