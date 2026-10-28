/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Calculus.Deriv.MvPolynomial
public import FQFP.RingTheory.MvPolynomial.DerivationCompression

/-!
# Derivative residual for truncated polynomial observables

## Main results

* `MvPolynomial.hasDerivAt_aeval_compressed_with_residual`: compression leaves exactly the
  evaluation of the discarded part as derivative residual.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ : Type*}

lemma hasDerivAt_aeval_compressed_with_residual
    (F : σ → MvPolynomial σ ℝ) (x : ℝ → σ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (n : ℕ) (p : (truncTotal σ ℝ n).range) :
    let D := mkDerivation ℝ F
    let Y := (aeval (x t)).toLinearMap.comp (truncTotal σ ℝ n).range.subtype
    HasDerivAt (fun s => aeval (x s) (p : MvPolynomial σ ℝ))
      ((compressedDerivation D n).dualMap Y p +
        aeval (x t) (D p - truncTotal σ ℝ n (D p))) t := by
  simpa [LinearMap.dualMap_apply, compressedDerivation, map_sub] using
    hasDerivAt_aeval_of_hasDerivAt_coordinates F x t hx p

end MvPolynomial
