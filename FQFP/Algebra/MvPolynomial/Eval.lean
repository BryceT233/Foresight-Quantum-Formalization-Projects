/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Real.Basic

/-!
# Constant coefficients after polynomial translation

## Main results

* `MvPolynomial.constantCoeff_aeval_translate`: the translated constant coefficient is
  evaluation at the translation point.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ : Type*}

lemma constantCoeff_aeval_translate
    (F : σ → MvPolynomial σ ℝ) (q : σ → ℝ) (i : σ) :
    constantCoeff (aeval (fun j => C (q j) + X j) (F i)) = aeval q (F i) := by
  have h : (constantCoeff : MvPolynomial σ ℝ →+* ℝ).comp
      (aeval (fun j => C (q j) + X j)).toRingHom = (aeval (R := ℝ) q).toRingHom := by
    apply ringHom_ext <;> intro j <;> simp
  exact RingHom.congr_fun h (F i)

end MvPolynomial
