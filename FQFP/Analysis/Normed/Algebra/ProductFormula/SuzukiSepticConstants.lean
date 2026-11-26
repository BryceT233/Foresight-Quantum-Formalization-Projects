/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticLocalError
public import FQFP.Analysis.Normed.Algebra.ProductFormula.GroupedConjugationConstants

/-!
# Explicit grouped ninth-order Suzuki constants

The ninth-order constant is the paper's unsigned outer commutator sum. The
negative half-generators remain in every recursively combined coefficient.

## Main results

* `suzukiNonicConstant_eq_sum`: the original formula for `2 B₈ᶠ / 9`.
-/

@[expose] public noncomputable section

open TrotterError Finset

namespace FQFP.BCH

variable {A : Type*} [NormedRing A] [Algebra ℝ A]

/-- The ninth-order constant equals the original grouped sum with positive
outer half-generators and signed complete lower defect coefficients. -/
theorem suzukiNonicConstant_eq_sum (a b : A) (p : ℝ) :
    let Z := fiveStageStrangHalfGenerator a b p
    suzukiNonicConstant a b p =
      2 / 9 * ∑ j : Fin 6, ∑ k ∈ range 8, ‖adPow (Z j) (8 - k)
        (groupedConjCoeff ((fun i ↦ -Z i) ∘ Fin.castLE (Nat.le_of_lt j.isLt))
          (Z ∘ Fin.castLE (Nat.le_of_lt j.isLt)) (-(1 / 2 : ℝ) • (a + b)) k)‖ /
            (Nat.factorial (8 - k) : ℝ) := by
  dsimp only
  rw [suzukiNonicConstant, groupedConjBound_neg_eq_sum]
  ring

end FQFP.BCH
