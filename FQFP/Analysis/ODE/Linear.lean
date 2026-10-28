/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Global autonomous linear evolution

The Banach-space trajectory theorem uses the operator exponential. The finite algebraic dual
trajectory theorem works in basis coordinates without imposing a norm on the observable space.

## Main results

* `ContinuousLinearMap.existsUnique_trajectory`: global Banach-space existence and uniqueness.
* `LinearMap.existsUnique_dualTrajectory`: the finite algebraic dual version.
-/

@[expose] public section
noncomputable section

namespace ContinuousLinearMap
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma existsUnique_trajectory (A : V →L[ℝ] V) (v₀ : V) :
    ∃! y : ℝ → V, y 0 = v₀ ∧ ∀ t, HasDerivAt y (A (y t)) t := by
  refine ⟨fun t => NormedSpace.exp (t • A) v₀, ⟨by simp, ?_⟩, ?_⟩
  · intro t
    simpa using (hasDerivAt_exp_smul_const' A t).clm_apply
      (hasDerivAt_const t v₀)
  · intro y hy
    apply ODE_solution_unique_univ (s := fun _ => Set.univ)
      (v := fun _ v => A v) (K := ‖A‖₊) (t₀ := 0)
    · intro t
      exact A.lipschitzWith.lipschitzOnWith
    · intro t
      exact ⟨hy.2 t, Set.mem_univ _⟩
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      simpa using (hasDerivAt_exp_smul_const' A t).clm_apply (hasDerivAt_const t v₀)
    · simpa using hy.1

end ContinuousLinearMap

namespace LinearMap
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]

lemma existsUnique_dualTrajectory (T : Module.End ℝ E) (ℓ₀ : Module.Dual ℝ E) :
    ∃! Y : ℝ → Module.Dual ℝ E,
      Y 0 = ℓ₀ ∧ ∀ t p, HasDerivAt (fun s => Y s p) (T.dualMap (Y t) p) t := by
  let B := Module.finBasis ℝ E
  let e := B.dualBasis.equivFun
  let A := LinearMap.toContinuousLinearMap (e.conj T.dualMap)
  obtain ⟨y, hy, huniq⟩ := A.existsUnique_trajectory (e ℓ₀)
  refine ⟨fun t => e.symm (y t), ⟨?_, ?_⟩, ?_⟩
  · simp [hy.1, e.symm_apply_apply]
  · intro t p
    let f := LinearMap.toContinuousLinearMap
      ((Module.Dual.eval ℝ E p).comp e.symm.toLinearMap)
    convert f.hasFDerivAt.comp_hasDerivAt t (hy.2 t) using 1
    · rfl
    · simp [f, A, LinearEquiv.conj_apply]
  · intro Y hY
    have hcoords : (fun t => e (Y t)) = y := by
      apply huniq
      refine ⟨by rw [hY.1], fun t ↦ ?_⟩
      apply hasDerivAt_pi.mpr
      intro i
      simpa [A, e, Module.Basis.dualBasis_equivFun, LinearEquiv.conj_apply] using hY.2 t (B i)
    funext t
    exact e.injective (by simpa using congrFun hcoords t)

end LinearMap
