/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Invariant ideals and the origin-preserving case -/

@[expose] public section
noncomputable section
namespace Derivation
section CommSemiring
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

lemma mapsTo_ideal_mul (D : Derivation R A A) (I J : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (hJ : ∀ a ∈ J, D a ∈ J) :
    ∀ a ∈ I * J, D a ∈ I * J := by
  intro a ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y ihx ihy => ?_)
  · rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_mul hx (hJ y hy))
      (Ideal.mul_mem_mul_rev (hI x hx) hy)
  · rw [map_add]
    exact Ideal.add_mem _ ihx ihy

lemma mapsTo_ideal_pow (D : Derivation R A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (n : ℕ) :
    ∀ a ∈ I ^ n, D a ∈ I ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact D.mapsTo_ideal_mul (I ^ n) I ih hI

end CommSemiring

section CommRing
variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

lemma existsUnique_quotient (D : Derivation R A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) :
    ∃! Dbar : Derivation R (A ⧸ I) (A ⧸ I),
      ∀ a, Dbar (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (D a) := by
  let f := Ideal.Quotient.mkₐ R I
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hd (a : A) (ha : f a = 0) : f (D a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hI a (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  refine ⟨Derivation.liftOfSurjective hf hd, ?_, ?_⟩
  · intro a
    exact Derivation.liftOfSurjective_apply hf hd a
  · intro Dbar hDbar
    apply Derivation.ext
    intro a
    obtain ⟨a, rfl⟩ := hf a
    change Dbar (Ideal.Quotient.mk I a) = _
    rw [hDbar]
    exact (Derivation.liftOfSurjective_apply hf hd a).symm

end CommRing
end Derivation

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
