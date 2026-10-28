/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Derivatives of multivariate polynomial evaluations

Polynomial observables satisfy the chain rule along coordinate ODE solutions.
No finiteness hypothesis on the variables is needed.

## Main results

* `MvPolynomial.hasDerivWithinAt_aeval_of_hasDerivWithinAt_coordinates`: the within-set rule.
* `MvPolynomial.hasDerivAt_aeval_of_hasDerivAt_coordinates`: the pointwise rule.
-/

@[expose] public section
noncomputable section
namespace MvPolynomial
variable {σ : Type*}

lemma hasDerivWithinAt_aeval_of_hasDerivWithinAt_coordinates
    (F : σ → MvPolynomial σ ℝ) (x : ℝ → σ → ℝ) (I : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun s => x s i) (aeval (x t) (F i)) I t)
    (p : MvPolynomial σ ℝ) :
    HasDerivWithinAt (fun s => aeval (x s) p)
      (aeval (x t) (mkDerivation ℝ F p)) I t := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using hasDerivWithinAt_const t I r
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext s
      simp
    · simp
  | mul_X p i hp =>
    convert hp.mul (hx i) using 1
    · ext s
      simp
    · simp [Derivation.leibniz, smul_eq_mul]
      ring

lemma hasDerivAt_aeval_of_hasDerivAt_coordinates
    (F : σ → MvPolynomial σ ℝ) (x : ℝ → σ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (aeval (x t) (F i)) t)
    (p : MvPolynomial σ ℝ) :
    HasDerivAt (fun s => aeval (x s) p) (aeval (x t) (mkDerivation ℝ F p)) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_aeval_of_hasDerivWithinAt_coordinates F x Set.univ t
    (fun i => (hx i).hasDerivWithinAt) p

end MvPolynomial
