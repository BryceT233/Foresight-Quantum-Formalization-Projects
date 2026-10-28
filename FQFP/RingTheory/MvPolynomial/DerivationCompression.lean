/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.RingTheory.MvPolynomial.Derivation
public import FQFP.RingTheory.MvPolynomial.Trunc

/-!
# Degree compression of polynomial derivations

Compression is projection after applying a derivation to the included polynomial.

## Main definitions

* `MvPolynomial.compressedDerivation`: the endomorphism of the truncated polynomial submodule.

## Main results

* `MvPolynomial.compressedDerivation_basis_repr`: its entries in a monomial basis.
* `MvPolynomial.dualMap_restriction_sub_compressed`: the algebraic dual residual.
* `MvPolynomial.mkDerivation_mem_range_truncTotal_of_totalDegree_le_one`: affine invariance.
-/

@[expose] public section
noncomputable section

namespace MvPolynomial
variable {σ R : Type*} [CommSemiring R]

/-- Compression `πₙ ∘ D ∘ ιₙ` on the observable submodule. -/
def compressedDerivation (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (n : ℕ) : Module.End R (truncTotal σ R n).range :=
  (truncTotal σ R n).rangeRestrict.comp
    (D.toLinearMap.comp (truncTotal σ R n).range.subtype)

lemma compressedDerivation_apply
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ)
    (p : (truncTotal σ R n).range) :
    (compressedDerivation D n p : MvPolynomial σ R) = truncTotal σ R n (D p) := rfl

lemma compressedDerivation_basis_repr
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (n : ℕ)
    (B : Module.Basis {d : σ →₀ ℕ // d.degree < n} R (truncTotal σ R n).range)
    (hB : ∀ d, (B d : MvPolynomial σ R) = monomial d.val 1)
    (d e : {d : σ →₀ ℕ // d.degree < n}) :
    B.repr (compressedDerivation D n (B d)) e =
      (D (monomial d.val 1)).coeff e.val := by
  rw [← coeff_eq_basis_repr n B hB, compressedDerivation_apply,
    coeff_truncTotal, ite_eq_left e.property, hB]

/-- Affine vector fields preserve every total-degree observable truncation. -/
lemma mkDerivation_mem_range_truncTotal_of_totalDegree_le_one
    (F : σ → MvPolynomial σ R) (hF : ∀ i, (F i).totalDegree ≤ 1)
    (n : ℕ) {p : MvPolynomial σ R} (hp : p ∈ (truncTotal σ R n).range) :
    mkDerivation R F p ∈ (truncTotal σ R n).range := by
  by_cases hn : n = 0
  · subst n
    have hpzero : p = 0 := by simpa using hp
    simp [hpzero]
  · have hpdeg : p.totalDegree < n :=
      (truncTotal_eq_self_iff n hn p).mp (truncTotal_eq_self_of_mem_range n hp)
    have hDdeg : (mkDerivation R F p).totalDegree < n :=
      lt_of_le_of_lt (by simpa using totalDegree_mkDerivation_le F 1 hF p) hpdeg
    exact ⟨mkDerivation R F p, (truncTotal_eq_self_iff n hn _).mpr hDdeg⟩

section CommRing
variable {S : Type*} [CommRing S]

lemma dualMap_restriction_sub_compressed
    (D : Derivation S (MvPolynomial σ S) (MvPolynomial σ S)) (n : ℕ)
    (ℓ : Module.Dual S (MvPolynomial σ S)) :
    (D.toLinearMap.dualMap ℓ).comp (truncTotal σ S n).range.subtype -
        (compressedDerivation D n).dualMap
          (ℓ.comp (truncTotal σ S n).range.subtype) =
      ℓ.comp ((LinearMap.id - truncTotal σ S n).comp
        (D.toLinearMap.comp (truncTotal σ S n).range.subtype)) := by
  ext p
  simp [LinearMap.dualMap_apply, compressedDerivation, map_sub]

end CommRing

end MvPolynomial
