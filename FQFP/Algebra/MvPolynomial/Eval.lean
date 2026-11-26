/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic

/-!
# Constant coefficients after polynomial translation

## Main results

* `MvPolynomial.constantCoeff_comp_aeval_translate` identifies translation followed by taking
  the constant coefficient with evaluation at the translation point.
* `MvPolynomial.constantCoeff_aeval_translate` applies the identity to a polynomial family.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ : Type*}

/-- Translation followed by taking the constant coefficient evaluates a polynomial at `q`. -/
lemma constantCoeff_comp_aeval_translate {R : Type*} [CommSemiring R] (q : σ → R) :
    (constantCoeff : MvPolynomial σ R →+* R).comp
      (aeval (fun j ↦ C (q j) + X j)).toRingHom = (aeval (R := R) q).toRingHom := by
  apply ringHom_ext <;> intro j <;> simp

/-- The constant coefficient of a translated component is its value at the translation point. -/
lemma constantCoeff_aeval_translate
    (F : σ → MvPolynomial σ ℝ) (q : σ → ℝ) (i : σ) :
    constantCoeff (aeval (fun j ↦ C (q j) + X j) (F i)) = aeval q (F i) :=
  RingHom.congr_fun (constantCoeff_comp_aeval_translate q) (F i)

end MvPolynomial
