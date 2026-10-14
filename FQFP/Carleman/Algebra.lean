/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Dual.Defs

/-! # Polynomial vector-field derivations and their degree bounds -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/- `F : σ → MvPolynomial σ R` specifies the polynomial vector field in each coordinate.
`mkDerivation R F` is the unique derivation satisfying `D (X i) = F i`.
`mkDerivationEquiv` already gives a linear equivalence between component data and derivations.
No additional `PolynomialVectorField` or `CarlemanOperator` type is needed.
-/

/-- For finitely many variables, the vector-field derivation is `∑ i, F i ∂ᵢ`.
The proof uses uniqueness of the existing construction. -/
lemma mkDerivation_eq_sum_pderiv [Fintype σ] (F : σ → MvPolynomial σ R) :
    mkDerivation R F = ∑ i, F i • pderiv i := by
  classical
  apply derivation_ext
  intro j
  simp [pderiv_X, Pi.single_apply]

/- These examples illustrate the existing API without additional wrappers.
`D.toLinearMap.dualMap` acts on the algebraic dual by `ℓ.comp D.toLinearMap`.
This is the algebraic content of linearization. -/

example (F : σ → MvPolynomial σ R) :
    Module.End R (Module.Dual R (MvPolynomial σ R)) :=
  (mkDerivation R F).toLinearMap.dualMap

example (x : σ → R) : Module.Dual R (MvPolynomial σ R) :=
  (aeval x).toLinearMap

example (F : σ → MvPolynomial σ R) (x : σ → R) (p : MvPolynomial σ R) :
    (mkDerivation R F).toLinearMap.dualMap (aeval x).toLinearMap p =
      aeval x (mkDerivation R F p) := rfl

/-! ## Degree behavior of derivations -/

/-- A homogeneous vector field of degree `r` sends positive degree `k + 1` to degree `k + r`.
Successor degrees avoid the degree-zero exception and natural-number subtraction.
Constant polynomials have zero derivative, as in `Derivation.map_algebraMap`.
Related API: `mkDerivation_monomial` and `IsHomogeneous.pderiv`. -/
lemma IsHomogeneous.mkDerivation {F : σ → MvPolynomial σ R}
    {p : MvPolynomial σ R} {k r : ℕ} (hp : p.IsHomogeneous (k + 1))
    (hF : ∀ i, (F i).IsHomogeneous r) :
    (mkDerivation R F p).IsHomogeneous (k + r) := by
  classical
  have hD : MvPolynomial.mkDerivation R F p = ∑ i ∈ p.vars, F i * pderiv i p := by
    calc
      MvPolynomial.mkDerivation R F p = (∑ i ∈ p.vars, F i • pderiv i) p := by
        apply derivation_eq_of_forall_mem_vars
        intro i hi
        simp [hi, pderiv_X, Pi.single_apply]
      _ = _ := by simp [smul_eq_mul]
  rw [hD]
  apply IsHomogeneous.sum
  intro i hi
  simpa [Nat.add_sub_cancel, Nat.add_comm] using (hF i).mul (hp.pderiv (i := i))

/-- If each vector-field component has degree at most `d`, the resulting total degree is
bounded by `p.totalDegree + d - 1`. Since `totalDegree 0 = 0`, this includes zero and constants. -/
lemma totalDegree_mkDerivation_le (F : σ → MvPolynomial σ R) (d : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ d) (p : MvPolynomial σ R) :
    (mkDerivation R F p).totalDegree ≤ p.totalDegree + d - 1 := by
  classical
  by_cases hp : p.totalDegree = 0
  · rw [totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, derivation_C, totalDegree_zero]
    exact Nat.zero_le _
  have hD : mkDerivation R F p = ∑ i ∈ p.vars, F i * pderiv i p := by
    calc
      mkDerivation R F p = (∑ i ∈ p.vars, F i • pderiv i) p := by
        apply derivation_eq_of_forall_mem_vars
        intro i hi
        simp [hi, pderiv_X, Pi.single_apply]
      _ = _ := by simp [smul_eq_mul]
  have hpartial (i : σ) : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    apply Finset.sup_le
    intro s hs
    have hs' : p.coeff (s + Finsupp.single i 1) ≠ 0 := by
      have h := mem_support_iff.mp hs
      rw [coeff_pderiv] at h
      exact left_ne_zero_of_mul h
    have hdegree := le_totalDegree (mem_support_iff.mpr hs')
    change (s + Finsupp.single i 1).degree ≤ p.totalDegree at hdegree
    change s.degree ≤ p.totalDegree - 1
    simp only [map_add, Finsupp.degree_single] at hdegree
    lia
  rw [hD]
  apply totalDegree_finsetSum_le
  intro i hi
  have hmul := totalDegree_mul (F i) (pderiv i p)
  have hFi := hF i
  have hpi := hpartial i
  lia

/-- For a homogeneous vector field of degree `r`, only the degree block
`k + 1 → k + r` can be nonzero. -/
lemma homogeneousComponent_mkDerivation_eq_zero
    (F : σ → MvPolynomial σ R) (k r m : ℕ)
    (hF : ∀ i, (F i).IsHomogeneous r) (hm : m ≠ k + r)
    (p : MvPolynomial σ R) :
    homogeneousComponent m (mkDerivation R F (homogeneousComponent (k + 1) p)) = 0 := by
  have h := (homogeneousComponent_isHomogeneous (k + 1) p).mkDerivation hF
  simpa [hm] using homogeneousComponent_of_mem (m := m) h

/-- A quadratic vector field couples only three adjacent degree blocks; degree zero has
zero derivative. This describes the observable operator, whose dual gives the block
structure of the Carleman state. -/
lemma homogeneousComponent_mkDerivation_quadratic_eq_zero
    (F : σ → MvPolynomial σ R) (hF : ∀ i, (F i).totalDegree ≤ 2)
    (k m : ℕ) (hm : m + 1 < k ∨ k + 1 < m) (p : MvPolynomial σ R) :
    homogeneousComponent m (mkDerivation R F (homogeneousComponent k p)) = 0 := by
  classical
  obtain _ | k := k
  · simp [homogeneousComponent_zero]
  have hsplit (i : σ) :
      (∑ r ∈ Finset.range 3, homogeneousComponent r (F i)) = F i := by
    ext s
    by_cases hs : s.degree < 3
    · simp [coeff_homogeneousComponent, hs]
    · have hz : (F i).coeff s = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt
        change (F i).totalDegree < s.degree
        have hi := hF i
        lia
      simp [coeff_homogeneousComponent, hz]
  have hD : mkDerivation R F =
      ∑ r ∈ Finset.range 3, mkDerivation R (fun i => homogeneousComponent r (F i)) := by
    apply derivation_ext
    intro i
    simpa using (hsplit i).symm
  rw [hD]
  simp only [← Derivation.coeFn_coe, Derivation.coe_sum_linearMap,
    LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro r hr
  apply homogeneousComponent_mkDerivation_eq_zero _ k r m
  · intro i
    exact homogeneousComponent_isHomogeneous r (F i)
  · have hr' := Finset.mem_range.mp hr
    lia

end MvPolynomial
