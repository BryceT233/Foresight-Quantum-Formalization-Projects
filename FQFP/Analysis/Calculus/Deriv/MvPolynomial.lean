/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
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
variable {σ 𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The chain rule along a polynomial vector field, restricted to a set of times. -/
lemma hasDerivWithinAt_aeval_of_hasDerivWithinAt_coordinates
    (F : σ → MvPolynomial σ 𝕜) (x : 𝕜 → σ → 𝕜) (I : Set 𝕜) (t : 𝕜)
    (hx : ∀ i, HasDerivWithinAt (fun s ↦ x s i) (aeval (x t) (F i)) I t)
    (p : MvPolynomial σ 𝕜) :
    HasDerivWithinAt (fun s ↦ aeval (x s) p)
      (aeval (x t) (mkDerivation 𝕜 F p)) I t := by
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

/-- The derivative of a polynomial observable is its derivation evaluated along the trajectory. -/
lemma hasDerivAt_aeval_of_hasDerivAt_coordinates
    (F : σ → MvPolynomial σ 𝕜) (x : 𝕜 → σ → 𝕜) (t : 𝕜)
    (hx : ∀ i, HasDerivAt (fun s ↦ x s i) (aeval (x t) (F i)) t)
    (p : MvPolynomial σ 𝕜) :
    HasDerivAt (fun s ↦ aeval (x s) p) (aeval (x t) (mkDerivation 𝕜 F p)) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_aeval_of_hasDerivWithinAt_coordinates F x Set.univ t
    (fun i ↦ (hx i).hasDerivWithinAt) p

end MvPolynomial
