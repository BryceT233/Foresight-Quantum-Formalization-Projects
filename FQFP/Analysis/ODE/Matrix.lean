/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.ODE.Linear
public import FQFP.Analysis.Normed.Algebra.MatrixExponential
public import FQFP.LinearAlgebra.Matrix.Dual

/-!
# Finite-coordinate formulas for linear dual evolution

## Main results

* `LinearMap.dualTrajectory_matrix_exp`: the trajectory in any finite basis is a matrix
  exponential with the transposed generator.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace LinearMap
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma dualTrajectory_matrix_exp (B : Module.Basis ι ℝ E) (T : Module.End ℝ E)
    (ℓ₀ : Module.Dual ℝ E) (Y : ℝ → Module.Dual ℝ E) (hinit : Y 0 = ℓ₀)
    (hode : ∀ t p, HasDerivAt (fun s => Y s p) (T.dualMap (Y t) p) t) (t : ℝ) :
    (fun i => Y t (B i)) =
      (NormedSpace.exp (t • (LinearMap.toMatrix B B T).transpose)).mulVec
        (fun i => ℓ₀ (B i)) := by
  let A := (LinearMap.toMatrix B B T).transpose
  let L := LinearMap.toContinuousLinearMap A.mulVecLin
  have hY (s : ℝ) : HasDerivAt (fun s i => Y s (B i)) (L (fun i => Y s (B i))) s := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [L, LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply,
      A, dualMap_coordinates] using hode s (B i)
  have heq := ODE_solution_unique_univ (s := fun _ => Set.univ)
    (v := fun _ v => L v) (K := ‖L‖₊) (t₀ := 0)
    (fun _ => L.lipschitzWith.lipschitzOnWith)
    (fun s => ⟨hY s, Set.mem_univ _⟩)
    (fun s => ⟨Matrix.hasDerivAt_exp_smul_mulVec A (fun i => ℓ₀ (B i)) s,
      Set.mem_univ _⟩) (by simp [hinit])
  exact congrFun heq t

end LinearMap
