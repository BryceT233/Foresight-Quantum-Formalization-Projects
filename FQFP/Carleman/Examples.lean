/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman

/-! # Boundary cases and the scalar quadratic truncation

For `x' = x²` and degree-two truncation, the retained generator sends `X` to
`X²` and `X²` to zero. The discarded derivative of `X²` is `2X³`.
-/

@[expose] public section
noncomputable section
open MvPolynomial
open scoped BigOperators Matrix

namespace Carleman

example : truncTotal Unit ℝ 0 = 0 := truncTotal_zero

example (p : MvPolynomial Unit ℝ) :
    truncTotal Unit ℝ 3 (truncTotal Unit ℝ 3 p) = truncTotal Unit ℝ 3 p :=
  truncTotal_idempotent 3 p

example :
    (compressedDerivation (mkDerivation ℝ (fun _ : Unit => (X () : MvPolynomial Unit ℝ) ^ 2)) 3
      ((truncTotal Unit ℝ 3).rangeRestrict (X ()))) =
        (truncTotal Unit ℝ 3).rangeRestrict ((X ()) ^ 2) := by
  apply Subtype.ext
  change truncTotal Unit ℝ 3 (mkDerivation ℝ _ (truncTotal Unit ℝ 3 (X ()))) = _
  rw [truncTotal_X 3 (by norm_num), mkDerivation_X]
  rfl

example :
    (compressedDerivation (mkDerivation ℝ (fun _ : Unit => (X () : MvPolynomial Unit ℝ) ^ 2)) 3
      ((truncTotal Unit ℝ 3).rangeRestrict ((X ()) ^ 2))) = 0 := by
  have h₂ : ((X () : MvPolynomial Unit ℝ) ^ 2).IsHomogeneous 2 := by
    simpa using (isHomogeneous_X ℝ ()).pow 2
  have h₃ : ((X () : MvPolynomial Unit ℝ) ^ 3).IsHomogeneous 3 := by
    simpa using (isHomogeneous_X ℝ ()).pow 3
  apply Subtype.ext
  change truncTotal Unit ℝ 3 (mkDerivation ℝ _ (truncTotal Unit ℝ 3 ((X ()) ^ 2))) = 0
  rw [truncTotal_of_isHomogeneous 3 2 h₂, ite_eq_left (by norm_num : 2 < 3)]
  have hD : mkDerivation ℝ (fun _ : Unit => (X () : MvPolynomial Unit ℝ) ^ 2)
      ((X ()) ^ 2) = (2 : ℝ) • (X ()) ^ 3 := by
    simp [Derivation.leibniz, pow_succ, Algebra.smul_def, algebraMap_eq, map_ofNat]
    ring
  rw [hD, map_smul, truncTotal_of_isHomogeneous 3 3 h₃]
  simp

example (x₀ : Unit → ℝ) (t : ℝ) :
    carlemanApproximant (fun _ : Unit => (X () : MvPolynomial Unit ℝ) ^ 2) x₀ 0 t = 0 :=
  carlemanApproximant_zero_order _ _ _

end Carleman

namespace Carleman.ScalarQuadratic

example (a t : ℝ) : carlemanApproximant vectorField (fun _ => a) 1 t () = a := by
  simp [carlemanApproximant_eq_sum]

example (a t : ℝ) :
    carlemanApproximant vectorField (fun _ => a) 2 t () = a + t * a ^ 2 := by
  simp [carlemanApproximant_eq_sum, Finset.sum_range_succ]
  ring

example (N : ℕ) (t : ℝ) :
    carlemanApproximant vectorField (fun _ => 0) N t () = 0 := by
  simp [carlemanApproximant_eq_sum]

example : TendstoUniformlyOn
    (fun N t => carlemanApproximant vectorField (fun _ => (1 : ℝ)) N t ())
    (solution 1) Filter.atTop (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  exact tendstoUniformlyOn_carlemanApproximant 1 (1 / 2) (by norm_num) (by norm_num)

end Carleman.ScalarQuadratic

namespace Carleman

-- A nonzero forcing with zero generator exercises the division-free `K = 0` case.
example (T t : ℝ) (ht : t ∈ Set.Icc 0 T) : ‖t‖ ≤ t := by
  have h := ContinuousLinearMap.norm_le_mul_exp_of_forced_zero_initial
    (0 : ℝ →L[ℝ] ℝ) (fun s => s) (fun _ => 1) 0 T 0 1
    continuous_id.continuousOn
    (fun s hs => by
      convert (hasDerivAt_id s).hasDerivWithinAt using 1 <;> first | rfl | simp)
    rfl (by simp) (by norm_num) (fun _ _ => by norm_num) t ht
  simpa using h

-- Signed entries give absolute row sums three and seven.
example : ‖LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin (!![1, 2; -3, 4] : Matrix (Fin 2) (Fin 2) ℝ))‖ ≤ 7 := by
  apply Matrix.norm_mulVec_toContinuousLinearMap_le_of_row_sum_le _ 7 (by norm_num)
  intro i
  fin_cases i <;> norm_num [Fin.sum_univ_two]

end Carleman
