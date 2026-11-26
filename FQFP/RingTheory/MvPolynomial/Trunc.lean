/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
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
* `MvPolynomial.range_truncTotal_succ`: the image below `d + 1` is `restrictTotalDegree σ R d`.
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

lemma truncTotal_of_isHomogeneous (n k : ℕ) {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous k) :
    truncTotal σ R n p = if k < n then p else 0 := by
  classical
  simp [truncTotal, homogeneousComponent_of_mem hp]

/-- Homogeneous polynomials at or above the cutoff have zero projected observable. -/
lemma truncTotal_rangeRestrict_eq_zero_of_isHomogeneous (n : ℕ)
    {p : MvPolynomial σ R} {k : ℕ} (hp : p.IsHomogeneous k) (hk : n ≤ k) :
    (truncTotal σ R n).rangeRestrict p = 0 :=
  Subtype.ext ((truncTotal_of_isHomogeneous n k hp).trans (ite_eq_right (not_lt.mpr hk)))

lemma truncTotal_monomial (n : ℕ) (d : σ →₀ ℕ) (r : R) :
    truncTotal σ R n (monomial d r) = if d.degree < n then monomial d r else 0 :=
  truncTotal_of_isHomogeneous n d.degree (isHomogeneous_monomial r rfl)

/-- Truncation retains a power of a variable exactly when its exponent is below the cutoff. -/
lemma truncTotal_X_pow (n k : ℕ) (i : σ) :
    truncTotal σ R n (X i ^ k) = if k < n then X i ^ k else 0 :=
  truncTotal_of_isHomogeneous n k (isHomogeneous_X_pow i k)

lemma truncTotal_X (n : ℕ) (hn : 1 < n) (i : σ) :
    truncTotal σ R n (X i) = X i := by
  simpa only [pow_one, ite_eq_left hn] using truncTotal_X_pow (R := R) n 1 i

lemma truncTotal_comp (m n : ℕ) :
    (truncTotal σ R m).comp (truncTotal σ R n) = truncTotal σ R (min m n) := by
  ext p d
  simp only [LinearMap.comp_apply, coeff_truncTotal, lt_min_iff]
  split_ifs <;> simp_all

/-- Total-degree truncation is an idempotent linear endomorphism. -/
lemma isIdempotentElem_truncTotal (n : ℕ) : IsIdempotentElem (truncTotal σ R n) := by
  simpa [IsIdempotentElem, Module.End.mul_eq_comp] using
    (truncTotal_comp (σ := σ) (R := R) n n)

@[simp] lemma truncTotal_idempotent (n : ℕ) (p : MvPolynomial σ R) :
    truncTotal σ R n (truncTotal σ R n p) = truncTotal σ R n p :=
  LinearMap.congr_fun (isIdempotentElem_truncTotal n).eq p

lemma truncTotal_eq_powerSeries_truncTotal [Finite σ] (n : ℕ)
    (p : MvPolynomial σ R) :
    truncTotal σ R n p = MvPowerSeries.truncTotal n p.toMvPowerSeries := by
  ext d
  simp [coeff_truncTotal, MvPowerSeries.coeff_truncTotal_eq_ite]

lemma mem_range_truncTotal_iff (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ (truncTotal σ R n).range ↔ ∀ d, n ≤ d.degree → p.coeff d = 0 := by
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_truncTotal n),
    MvPolynomial.ext_iff]
  simp only [coeff_truncTotal, ite_eq_left_iff, not_lt, eq_comm (a := (0 : R))]

lemma truncTotal_eq_self_of_mem_range (n : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ (truncTotal σ R n).range) : truncTotal σ R n p = p :=
  (LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_truncTotal n)).mp hp

lemma range_truncTotal_eq_restrictSupport (n : ℕ) :
    (truncTotal σ R n).range = restrictSupport R {d : σ →₀ ℕ | d.degree < n} := by
  ext p
  rw [mem_range_truncTotal_iff, restrictSupport, AddMonoidAlgebra.mem_supported']
  simp

/-- The image of truncation below `d + 1` is the total-degree-`≤ d` submodule. -/
lemma range_truncTotal_succ (d : ℕ) :
    (truncTotal σ R (d + 1)).range = restrictTotalDegree σ R d := by
  rw [range_truncTotal_eq_restrictSupport, restrictTotalDegree]
  simp only [Nat.lt_succ_iff]
  rfl

/-- Truncating below `d + 1` has as its range the polynomials of total degree at most `d`. -/
lemma mem_range_truncTotal_succ_iff (d : ℕ) (p : MvPolynomial σ R) :
    p ∈ (truncTotal σ R (d + 1)).range ↔ p.totalDegree ≤ d := by
  rw [range_truncTotal_succ, mem_restrictTotalDegree]

lemma truncTotal_eq_self_iff (n : ℕ) (hn : n ≠ 0) (p : MvPolynomial σ R) :
    truncTotal σ R n p = p ↔ p.totalDegree < n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_truncTotal (d + 1)),
    mem_range_truncTotal_succ_iff, Nat.lt_succ_iff]

/-- The canonical monomial basis of the projected observable space. -/
def basisRangeTruncTotal (n : ℕ) :
    Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range :=
  (basisRestrictSupport R {d : σ →₀ ℕ | d.degree < n}).map
    (LinearEquiv.ofEq _ _ (range_truncTotal_eq_restrictSupport n).symm)

@[simp] lemma basisRangeTruncTotal_apply (n : ℕ) (d : {d : σ →₀ ℕ // d.degree < n}) :
    (basisRangeTruncTotal (R := R) n d : MvPolynomial σ R) = monomial d.val 1 := by
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.supportedEquivFinsupp_symm_single (R := R) {d : σ →₀ ℕ | d.degree < n} d 1

/-- Coordinates in the truncated monomial basis are the coefficients at the retained exponents. -/
lemma basisRangeTruncTotal_repr (n : ℕ) (p : (truncTotal σ R n).range)
    (e : {d : σ →₀ ℕ // d.degree < n}) :
    (basisRangeTruncTotal n).repr p e = (p : MvPolynomial σ R).coeff e := rfl

lemma exists_basis_range_truncTotal (n : ℕ) :
    ∃ B : Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range,
      ∀ d, (B d : MvPolynomial σ R) = monomial d.val 1 :=
  ⟨basisRangeTruncTotal n, basisRangeTruncTotal_apply n⟩

instance finite_range_truncTotal [Finite σ] (n : ℕ) :
    Module.Finite R (truncTotal σ R n).range := by
  let : Finite {d : σ →₀ ℕ // d.degree < n} := (Finsupp.finite_of_degree_lt n).to_subtype
  exact Module.Finite.of_basis (basisRangeTruncTotal n)

lemma coeff_eq_basis_repr (n : ℕ)
    (B : Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range)
    (hB : ∀ d, (B d : MvPolynomial σ R) = monomial d.val 1)
    (p : (truncTotal σ R n).range) (e : {d : σ →₀ ℕ // d.degree < n}) :
    (p : MvPolynomial σ R).coeff e.val = B.repr p e := by
  have h : B = basisRangeTruncTotal n := DFunLike.ext _ _ fun d =>
    Subtype.ext ((hB d).trans (basisRangeTruncTotal_apply n d).symm)
  rw [h, basisRangeTruncTotal_repr]

end MvPolynomial
