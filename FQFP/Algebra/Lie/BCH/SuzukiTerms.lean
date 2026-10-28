/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.CommutatorFamily

/-!
# The quintic Suzuki combination of Childs commutators

The eight quadratic scalar polynomials use the source projection with zero
coefficients at indices two and six. Their linear combination of the Childs
commutators is defined over an arbitrary field algebra, without analytic assumptions.

## Main definitions

* `suzukiQuinticCoeff`: the eight signed coefficient polynomials.
* `suzukiQuinticTerm`: their linear combination of the Childs commutators.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- The signed quintic Suzuki coefficients in the eight-element Childs family. -/
def suzukiQuinticCoeff {K : Type*} [Field K] (p : K) : Fin 8 → K :=
  ![127 * p ^ 2 / 144000 + 13 * p / 36000 - 1 / 24000,
    p ^ 2 / 12000 + 13 * p / 6000 - 1 / 4000,
    0,
    -61 * p ^ 2 / 9000 + 13 * p / 3000 - 1 / 2000,
    31 * p ^ 2 / 9000 - 13 * p / 18000 + 1 / 12000,
    31 * p ^ 2 / 3000 - 13 * p / 6000 + 1 / 4000,
    0,
    p ^ 2 / 18000 + 13 * p / 9000 - 1 / 6000]

/-- The quintic Childs-basis combination for an arbitrary Suzuki parameter. -/
def suzukiQuinticTerm {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (a b : A) (p : K) : A :=
  ∑ i : Fin 8, suzukiQuinticCoeff p i • childsComm a b i

end FQFP.BCH
