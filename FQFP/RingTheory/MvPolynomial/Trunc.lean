/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.LinearAlgebra.Basis.Submodule

/-! # Total-degree projection and finite observable spaces

The threshold `n` retains degrees strictly below `n`. The image is a submodule,
with its canonical monomial basis and finite-generation property.

## Main definitions

* `MvPolynomial.truncTotal`: projection onto degrees strictly below a threshold.
* `MvPolynomial.basisRangeTruncTotal`: the monomial basis of its range.

## Main results

* `MvPolynomial.truncTotal_idempotent`: idempotence of the projection.
* `MvPolynomial.finite_range_truncTotal`: finite generation for finitely many variables.
* `MvPolynomial.coeff_eq_basis_repr`: coefficients in a monomial basis.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace MvPolynomial
variable {σ R : Type*} [CommSemiring R]

/-- Projection onto monomials of total degree strictly below `n`. -/
def truncTotal (σ R : Type*) [CommSemiring R] (n : ℕ) :
    Module.End R (MvPolynomial σ R) :=
  ∑ k ∈ Finset.range n, homogeneousComponent k

lemma coeff_truncTotal (n : ℕ) (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (truncTotal σ R n p).coeff d = if d.degree < n then p.coeff d else 0 := by
  classical
  simp [truncTotal, coeff_homogeneousComponent]

@[simp] lemma truncTotal_zero : truncTotal σ R 0 = 0 := by
  simp [truncTotal]

lemma truncTotal_monomial (n : ℕ) (d : σ →₀ ℕ) (r : R) :
    truncTotal σ R n (monomial d r) = if d.degree < n then monomial d r else 0 := by
  classical
  by_cases h : d.degree < n
  · ext e
    by_cases he : d = e
    · subst e
      simp [coeff_truncTotal, h]
    · simp [coeff_truncTotal, coeff_monomial, h, he]
  · ext e
    by_cases he : d = e
    · subst e
      simp [coeff_truncTotal, h]
    · simp [coeff_truncTotal, coeff_monomial, h, he]

lemma truncTotal_X (n : ℕ) (hn : 1 < n) (i : σ) :
    truncTotal σ R n (X i) = X i := by
  simpa [X, Finsupp.degree_single, hn] using
    truncTotal_monomial (R := R) n (Finsupp.single i 1) 1

lemma truncTotal_of_isHomogeneous (n k : ℕ) {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous k) :
    truncTotal σ R n p = if k < n then p else 0 := by
  classical
  simp [truncTotal, homogeneousComponent_of_mem hp]

lemma truncTotal_comp (m n : ℕ) :
    (truncTotal σ R m).comp (truncTotal σ R n) = truncTotal σ R (min m n) := by
  ext p d
  simp only [LinearMap.comp_apply, coeff_truncTotal, lt_min_iff]
  split_ifs <;> simp_all

@[simp] lemma truncTotal_idempotent (n : ℕ) (p : MvPolynomial σ R) :
    truncTotal σ R n (truncTotal σ R n p) = truncTotal σ R n p := by
  simpa using LinearMap.congr_fun (truncTotal_comp (σ := σ) (R := R) n n) p

lemma truncTotal_eq_powerSeries_truncTotal [Finite σ] (n : ℕ)
    (p : MvPolynomial σ R) :
    truncTotal σ R n p = MvPowerSeries.truncTotal n p.toMvPowerSeries := by
  ext d
  simp [coeff_truncTotal, MvPowerSeries.coeff_truncTotal_eq_ite]

lemma truncTotal_eq_self_iff (n : ℕ) (hn : n ≠ 0) (p : MvPolynomial σ R) :
    truncTotal σ R n p = p ↔ p.totalDegree < n := by
  classical
  constructor
  · intro h
    apply (Finset.sup_lt_iff (Nat.pos_of_ne_zero hn)).mpr
    intro d hd
    change d.degree < n
    by_contra hdn
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff d) h
    rw [coeff_truncTotal, ite_eq_right hdn] at hc
    exact mem_support_iff.mp hd hc.symm
  · intro h
    ext d
    by_cases hd : d.degree < n
    · simp [coeff_truncTotal, hd]
    · have hz : p.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt
        (show p.totalDegree < d.degree by lia)
      simp [coeff_truncTotal, hd, hz]

lemma mem_range_truncTotal_iff (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (truncTotal σ R n).range ↔ ∀ d, n ≤ d.degree → p.coeff d = 0 := by
  constructor
  · rintro ⟨q, rfl⟩ d hd
    simp [coeff_truncTotal, not_lt.mpr hd]
  · intro h
    refine ⟨p, ?_⟩
    ext d
    by_cases hd : d.degree < n
    · simp [coeff_truncTotal, hd]
    · simp [coeff_truncTotal, hd, h d (not_lt.mp hd)]

lemma truncTotal_eq_self_of_mem_range (n : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ (truncTotal σ R n).range) : truncTotal σ R n p = p := by
  obtain ⟨q, rfl⟩ := hp
  exact truncTotal_idempotent n q

lemma range_truncTotal_eq_restrictSupport (n : ℕ) :
    (truncTotal σ R n).range = restrictSupport R {d : σ →₀ ℕ | d.degree < n} := by
  ext p
  rw [mem_range_truncTotal_iff, mem_restrictSupport_iff]
  constructor
  · intro h d hd
    by_contra hdn
    exact mem_support_iff.mp hd (h d (not_lt.mp hdn))
  · intro h d hd
    by_contra hc
    exact (not_lt.mpr hd) (h (mem_support_iff.mpr hc))

/-- The canonical monomial basis of the projected observable space. -/
def basisRangeTruncTotal (n : ℕ) :
    Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range :=
  (basisRestrictSupport R {d : σ →₀ ℕ | d.degree < n}).map
    (LinearEquiv.ofEq _ _ (range_truncTotal_eq_restrictSupport n).symm)

@[simp] lemma basisRangeTruncTotal_apply (n : ℕ) (d : {d : σ →₀ ℕ // d.degree < n}) :
    (basisRangeTruncTotal (R := R) n d : MvPolynomial σ R) = monomial d.val 1 := by
  simp only [basisRangeTruncTotal, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  change ((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R)
    {d : σ →₀ ℕ | d.degree < n}).symm (Finsupp.single d 1) : MvPolynomial σ R) = _
  apply AddMonoidAlgebra.coeff_injective
  change ((Finsupp.supportedEquivFinsupp (M := R) (R := R)
    {d : σ →₀ ℕ | d.degree < n}).symm (Finsupp.single d 1) : (σ →₀ ℕ) →₀ R) = _
  exact Finsupp.supportedEquivFinsupp_symm_single ..

lemma exists_basis_range_truncTotal (n : ℕ) :
    ∃ B : Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range,
      ∀ d, (B d : MvPolynomial σ R) = monomial d.val 1 :=
  ⟨basisRangeTruncTotal n, basisRangeTruncTotal_apply n⟩

lemma finite_range_truncTotal [Finite σ] (n : ℕ) :
    Module.Finite R (truncTotal σ R n).range := by
  let : Finite {d : σ →₀ ℕ // d.degree < n} := (Finsupp.finite_of_degree_lt n).to_subtype
  exact Module.Finite.of_basis (basisRangeTruncTotal n)

lemma coeff_eq_basis_repr (n : ℕ)
    (B : Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range)
    (hB : ∀ d, (B d : MvPolynomial σ R) = monomial d.val 1)
    (p : (truncTotal σ R n).range) (e : {d : σ →₀ ℕ // d.degree < n}) :
    (p : MvPolynomial σ R).coeff e.val = B.repr p e := by
  classical
  conv_lhs => rw [← B.linearCombination_repr p]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
    Submodule.coe_smul, hB, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
  simp only [Subtype.coe_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff]
  exact Eq.symm

end MvPolynomial
