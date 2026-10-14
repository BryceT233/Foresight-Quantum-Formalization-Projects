/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.Approximant
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Dual

/-! # Matrix exponential formula in any finite observable basis -/

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

namespace LinearMap
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma dualMap_coordinates (B : Module.Basis ι ℝ E) (T : Module.End ℝ E)
    (ℓ : Module.Dual ℝ E) (i : ι) :
    ((LinearMap.toMatrix B B T).transpose).mulVec (fun j => ℓ (B j)) i =
      T.dualMap ℓ (B i) := by
  change _ = ℓ (T (B i))
  calc
    _ = ∑ j, B.repr (T (B i)) j * ℓ (B j) := by
      simp [Matrix.mulVec, dotProduct, toMatrix_apply]
    _ = ℓ (∑ j, B.repr (T (B i)) j • B j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ℓ (T (B i)) := congrArg ℓ (B.sum_repr (T (B i)))

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
