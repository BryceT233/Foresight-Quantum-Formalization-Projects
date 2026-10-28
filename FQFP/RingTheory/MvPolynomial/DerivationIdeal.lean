/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.Derivation.Ideal
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Polynomial derivations preserving the augmentation ideal

## Main results

* `MvPolynomial.mem_idealOfVars_iff_constantCoeff_eq_zero`: augmentation-ideal membership.
* `MvPolynomial.mkDerivation_preserves_idealOfVars_pow`: origin-preserving vector fields
  preserve every power of that ideal.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ R : Type*} [CommSemiring R]

lemma mem_idealOfVars_iff_constantCoeff_eq_zero (p : MvPolynomial σ R) :
    p ∈ idealOfVars σ R ↔ constantCoeff p = 0 := by
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff']
  simp [Finsupp.degree_eq_zero_iff, constantCoeff_eq]

lemma mkDerivation_preserves_idealOfVars_pow (F : σ → MvPolynomial σ R)
    (hF : ∀ i, constantCoeff (F i) = 0) (n : ℕ) :
    ∀ p ∈ idealOfVars σ R ^ n, mkDerivation R F p ∈ idealOfVars σ R ^ n := by
  apply Derivation.mapsTo_ideal_pow
  intro p hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    rw [mkDerivation_X]
    exact (mem_idealOfVars_iff_constantCoeff_eq_zero (F i)).mpr (hF i)
  | zero => simp
  | add p q hp hq ihp ihq =>
    rw [map_add]
    exact Ideal.add_mem _ ihp ihq
  | smul a p hp ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ a ih) (Ideal.mul_mem_right _ _ hp)

end MvPolynomial
