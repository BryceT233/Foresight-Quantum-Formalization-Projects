/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.Approximant
public import FQFP.Analysis.ODE.Matrix

/-!
# Matrix formula for the Carleman approximant

## Main results

* `MvPolynomial.carlemanLiftedApproximant_matrix_exp`: evolution in any finite observable basis.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace MvPolynomial
variable {σ : Type*} [Finite σ]

lemma carlemanLiftedApproximant_matrix_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : σ → MvPolynomial σ ℝ) (x₀ : σ → ℝ) (N : ℕ)
    (B : Module.Basis ι ℝ (truncTotal σ ℝ (N + 1)).range) (t : ℝ) :
    (fun i => carlemanLiftedApproximant F x₀ N t (B i)) =
      (NormedSpace.exp
        (t • (LinearMap.toMatrix B B
          (compressedDerivation (mkDerivation ℝ F) (N + 1))).transpose)).mulVec
        (fun i => aeval x₀ (B i : MvPolynomial σ ℝ)) :=
  LinearMap.dualTrajectory_matrix_exp B _ _ _ (carlemanLiftedApproximant_initial F x₀ N)
    (carlemanLiftedApproximant_hasDerivAt F x₀ N) t

end MvPolynomial
