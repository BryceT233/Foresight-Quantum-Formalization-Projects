/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Monomials
public import FQFP.RingTheory.MvPolynomial.Trunc
public import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Monomial dictionaries for the truncated two-mode Burgers system

`MvPolynomial.truncTotal` is the paper's `π_N` when its threshold is `N + 1`.
`AddMonoidAlgebra.supported` is the span of the monomials in a dictionary.
The truncated operator is linear, although it is generally not a derivation.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

private lemma index_decompose (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext k
  fin_cases k <;> simp

private lemma monomial_decompose (d : Fin 2 →₀ ℕ) :
    (monomial d (1 : ℝ) : MvPolynomial (Fin 2) ℝ) =
      X 0 ^ (d 0) * X 1 ^ (d 1) := by
  conv_lhs => rw [index_decompose d]
  simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]

private lemma index_degree (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum]
  simp only [Fin.sum_univ_two]

private lemma pair_degree (i j : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree = i + j := by
  simp [index_degree]

private lemma pair_eq_pair_iff (i j k l : ℕ) :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j =
      Finsupp.single 0 k + Finsupp.single 1 l) ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have h₀ := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
    have h₁ := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
    exact ⟨by simpa using h₀, by simpa using h₁⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma pow_mul_pow_eq_monomial (i j : ℕ) :
    (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j =
      monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 := by
  simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]

private lemma pow_mul_pow_mem_supported (S : Set (Fin 2 →₀ ℕ))
    (i j : ℕ) (h : Finsupp.single 0 i + Finsupp.single 1 j ∈ S) :
    (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j ∈
      AddMonoidAlgebra.supported ℝ ℝ S := by
  have hmon : (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j =
      monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 := by
    simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [hmon]
  rw [AddMonoidAlgebra.supported_eq_span_single]
  apply Submodule.subset_span
  exact ⟨_, h, rfl⟩

/-- The paper's odd-exponent dictionary for the first coordinate. -/
def firstDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | d 0 % 2 = 1 ∧ d.degree ≤ N}

/-- The paper's even-exponent dictionary for the second coordinate. -/
def secondDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | d = Finsupp.single 1 1 ∨
    (0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N)}

/-- The paper's even-exponent dictionary for the energy observable. -/
def energyDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | d = Finsupp.single 1 2 ∨
    (0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N)}

/-- The truncated Lie operator `π_N D` on the ambient polynomial ring. -/
def truncatedLie (α γ β : ℝ) (N : ℕ) :
    Module.End ℝ (MvPolynomial (Fin 2) ℝ) :=
  (truncTotal (Fin 2) ℝ (N + 1)).comp
    (mkDerivation ℝ (vectorField α γ β)).toLinearMap

private lemma truncTotal_pow_mul_pow (N i j : ℕ) :
    truncTotal (Fin 2) ℝ (N + 1)
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j) =
      if i + j ≤ N then X 0 ^ i * X 1 ^ j else 0 := by
  have h : (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j =
      monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 := by
    simp only [X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [h, truncTotal_monomial]
  simp only [map_add, Finsupp.degree_single]
  simp only [Nat.lt_add_one_iff]

private lemma truncTotal_C_mul (N : ℕ) (c : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    truncTotal (Fin 2) ℝ (N + 1) (C c * p) =
      C c * truncTotal (Fin 2) ℝ (N + 1) p := by
  simpa only [Algebra.smul_def, C_eq_algebraMap] using
    (map_smul (truncTotal (Fin 2) ℝ (N + 1)) c p)

/-- The truncated operator sends a monomial to its three retained transitions. -/
theorem truncatedLie_pow_mul_pow (α γ β : ℝ) (N i j : ℕ) :
    truncatedLie α γ β N
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j) =
      -C (α * (i : ℝ) + γ * (j : ℝ)) *
          (if i + j ≤ N then X 0 ^ i * X 1 ^ j else 0) +
        C (β * (i : ℝ)) *
          (if i + j + 1 ≤ N then X 0 ^ i * X 1 ^ (j + 1) else 0) -
        C (β * (j : ℝ)) *
          (if i + 2 + (j - 1) ≤ N then X 0 ^ (i + 2) * X 1 ^ (j - 1) else 0) := by
  change truncTotal (Fin 2) ℝ (N + 1)
      ((mkDerivation ℝ (vectorField α γ β)) (X 0 ^ i * X 1 ^ j)) = _
  rw [lieDerivation_pow_mul_pow, map_sub, map_add]
  simp only [mul_assoc, neg_mul, map_neg, truncTotal_C_mul,
    truncTotal_pow_mul_pow]
  simp only [add_assoc]

private lemma truncatedLie_rise_coefficient (α γ β : ℝ) (N i j : ℕ)
    (hdegree : i + j + 1 ≤ N) :
    (truncatedLie α γ β N
      ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j)).coeff
        (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = β * (i : ℝ) := by
  rw [truncatedLie_pow_mul_pow]
  rw [pow_mul_pow_eq_monomial i j,
    pow_mul_pow_eq_monomial i (j + 1),
    pow_mul_pow_eq_monomial (i + 2) (j - 1)]
  have hbase : i + j ≤ N := by lia
  rw [ite_eq_left hbase, ite_eq_left hdegree]
  have hneq : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) ≠
      (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) := by
    intro h
    have hj := ((pair_eq_pair_iff i j i (j + 1)).mp h).2
    lia
  have hzero :
      (C (α * (i : ℝ) + γ * (j : ℝ)) *
        monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 :
          MvPolynomial (Fin 2) ℝ).coeff
            (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = 0 := by
    rw [coeff_C_mul, coeff_monomial, ite_eq_right hneq]
    simp
  have hfirst :
      (-C (α * (i : ℝ) + γ * (j : ℝ)) *
        monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1 :
          MvPolynomial (Fin 2) ℝ).coeff
            (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = 0 := by
    rw [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.coe_neg,
      Pi.neg_apply, hzero]
    simp
  have hsecond :
      (C (β * (i : ℝ)) *
        monomial (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) 1 :
          MvPolynomial (Fin 2) ℝ).coeff
            (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = β * (i : ℝ) := by
    rw [coeff_C_mul, coeff_monomial]
    simp
  have hnelast : (Finsupp.single (0 : Fin 2) (i + 2) +
      Finsupp.single 1 (j - 1)) ≠
        (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) := by
    intro h
    have hi := ((pair_eq_pair_iff (i + 2) (j - 1) i (j + 1)).mp h).1
    lia
  have hlast :
      (C (β * (j : ℝ)) *
        (if i + 2 + (j - 1) ≤ N then
          monomial (Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1)) 1
        else 0) : MvPolynomial (Fin 2) ℝ).coeff
          (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = 0 := by
    split_ifs
    · rw [coeff_C_mul, coeff_monomial, ite_eq_right hnelast]
      simp
    · simp
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply]
  rw [hfirst, hsecond, hlast]
  ring

private lemma truncatedLie_shift_coefficient (α γ β : ℝ) (N i j : ℕ)
    (hj : 0 < j) (hdegree : i + 2 + (j - 1) ≤ N) :
    (truncatedLie α γ β N
      ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j)).coeff
        (Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1)) =
      -(β * (j : ℝ)) := by
  rw [truncatedLie_pow_mul_pow]
  rw [pow_mul_pow_eq_monomial i j,
    pow_mul_pow_eq_monomial i (j + 1),
    pow_mul_pow_eq_monomial (i + 2) (j - 1)]
  have hbase : i + j ≤ N := by lia
  have hrise : i + j + 1 ≤ N := by lia
  rw [ite_eq_left hbase, ite_eq_left hrise, ite_eq_left hdegree]
  have hnebase : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j) ≠
      (Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1)) := by
    intro h
    have hi := ((pair_eq_pair_iff i j (i + 2) (j - 1)).mp h).1
    lia
  have hnerise : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 (j + 1)) ≠
      (Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1)) := by
    intro h
    have hi := ((pair_eq_pair_iff i (j + 1) (i + 2) (j - 1)).mp h).1
    lia
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, neg_mul,
    AddMonoidAlgebra.coeff_neg, Finsupp.coe_neg, Pi.neg_apply,
    coeff_C_mul, coeff_monomial]
  rw [ite_eq_right hnebase, ite_eq_right hnerise]
  simp

/-- A monomial support closed under the two retained nonlinear transitions is
invariant under the truncated Lie operator. -/
theorem supported_truncatedLie_invariant (α γ β : ℝ) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hrise : ∀ i j, Finsupp.single 0 i + Finsupp.single 1 j ∈ S →
      0 < i → i + j + 1 ≤ N →
        Finsupp.single 0 i + Finsupp.single 1 (j + 1) ∈ S)
    (hshift : ∀ i j, Finsupp.single 0 i + Finsupp.single 1 j ∈ S →
      0 < j → i + 2 + (j - 1) ≤ N →
        Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1) ∈ S) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S := by
  let V := AddMonoidAlgebra.supported ℝ ℝ S
  have hscalar (c : ℝ) {p : MvPolynomial (Fin 2) ℝ} (hp : p ∈ V) :
      C c * p ∈ V := by
    simpa only [Algebra.smul_def, C_eq_algebraMap] using V.smul_mem c hp
  have hgen (d : Fin 2 →₀ ℕ) (hd : d ∈ S) :
      truncatedLie α γ β N (monomial d 1) ∈ V := by
    rw [monomial_decompose d, truncatedLie_pow_mul_pow]
    have hd' : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) ∈ S := by
      simpa only [← index_decompose d] using hd
    have hbase : (if d 0 + d 1 ≤ N then
        (X 0 : MvPolynomial (Fin 2) ℝ) ^ (d 0) * X 1 ^ (d 1) else 0) ∈ V := by
      split_ifs
      · exact pow_mul_pow_mem_supported S _ _ hd'
      · exact V.zero_mem
    have hnext : C (β * (d 0 : ℝ)) *
        (if d 0 + d 1 + 1 ≤ N then
          (X 0 : MvPolynomial (Fin 2) ℝ) ^ (d 0) * X 1 ^ (d 1 + 1) else 0) ∈ V := by
      by_cases hi : d 0 = 0
      · simp [hi]
      · apply hscalar
        split_ifs with hdegree
        · exact pow_mul_pow_mem_supported S _ _
            (hrise _ _ hd' (Nat.pos_of_ne_zero hi) hdegree)
        · exact V.zero_mem
    have hlast : C (β * (d 1 : ℝ)) *
        (if d 0 + 2 + (d 1 - 1) ≤ N then
          (X 0 : MvPolynomial (Fin 2) ℝ) ^ (d 0 + 2) * X 1 ^ (d 1 - 1) else 0) ∈ V := by
      by_cases hj : d 1 = 0
      · simp [hj]
      · apply hscalar
        split_ifs with hdegree
        · exact pow_mul_pow_mem_supported S _ _
            (hshift _ _ hd' (Nat.pos_of_ne_zero hj) hdegree)
        · exact V.zero_mem
    have hfirst : -C (α * (d 0 : ℝ) + γ * (d 1 : ℝ)) *
        (if d 0 + d 1 ≤ N then
          (X 0 : MvPolynomial (Fin 2) ℝ) ^ (d 0) * X 1 ^ (d 1) else 0) ∈ V := by
      simpa only [neg_mul] using
        V.neg_mem (hscalar (α * (d 0 : ℝ) + γ * (d 1 : ℝ)) hbase)
    exact V.sub_mem (V.add_mem hfirst hnext) hlast
  have hle : Submodule.span ℝ
      ((fun d : Fin 2 →₀ ℕ => monomial d (1 : ℝ)) '' S) ≤
      V.comap (truncatedLie α γ β N) := by
    apply Submodule.span_le.mpr
    rintro p ⟨d, hd, rfl⟩
    exact hgen d hd
  intro p hp
  apply hle
  simpa only [AddMonoidAlgebra.supported_eq_span_single,
    MvPolynomial.single_eq_monomial] using hp

/-- The odd-exponent dictionary is invariant under the truncated operator. -/
theorem firstDictionary_invariant (α γ β : ℝ) (N : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (firstDictionary N),
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ (firstDictionary N) := by
  apply supported_truncatedLie_invariant
  · intro i j hs _ hdegree
    constructor
    · simpa [firstDictionary] using hs.1
    · simp only [pair_degree]
      exact hdegree
  · intro i j hs _ hdegree
    constructor
    · have hodd : i % 2 = 1 := by simpa using hs.1
      simpa [firstDictionary, Nat.add_mod] using hodd
    · simpa only [pair_degree] using hdegree

private theorem evenDictionary_invariant (α γ β : ℝ) (N k : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ
        {d : Fin 2 →₀ ℕ | d = Finsupp.single 1 k ∨
          (0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N)},
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ
          {d : Fin 2 →₀ ℕ | d = Finsupp.single 1 k ∨
            (0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N)} := by
  apply supported_truncatedLie_invariant
  · intro i j hs hi hdegree
    rcases hs with hseed | htail
    · have hi0 : i = 0 := by
        have h := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hseed
        simpa using h
      lia
    · right
      refine ⟨by simpa using htail.1, ?_, ?_⟩
      · simpa using htail.2.1
      · simpa only [pair_degree, add_assoc] using hdegree
  · intro i j hs hj hdegree
    rcases hs with hseed | htail
    · have hi0 : i = 0 := by
        have h := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hseed
        simpa using h
      right
      have hval : (Finsupp.single (0 : Fin 2) (i + 2) +
          Finsupp.single 1 (j - 1) : Fin 2 →₀ ℕ) 0 =
          i + 2 := by simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hval]; lia
      · rw [hval]; simp [hi0]
      · simpa only [pair_degree] using hdegree
    · right
      have hval : (Finsupp.single (0 : Fin 2) (i + 2) +
          Finsupp.single 1 (j - 1) : Fin 2 →₀ ℕ) 0 =
          i + 2 := by simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hval]; lia
      · have heven : i % 2 = 0 := by simpa using htail.2.1
        rw [hval]
        simpa [Nat.add_mod] using heven
      · simpa only [pair_degree] using hdegree

/-- The second-coordinate dictionary is invariant under truncation. -/
theorem secondDictionary_invariant (α γ β : ℝ) (N : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N),
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N) := by
  exact evenDictionary_invariant α γ β N 1

/-- The energy dictionary is invariant under truncation. -/
theorem energyDictionary_invariant (α γ β : ℝ) (N : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N),
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N) := by
  exact evenDictionary_invariant α γ β N 2

/-- The odd-exponent dictionary contains the first coordinate. -/
theorem first_mem_firstDictionary (N : ℕ) (hN : 1 ≤ N) :
    (X 0 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ (firstDictionary N) := by
  have h : Finsupp.single 0 1 + Finsupp.single 1 0 ∈ firstDictionary N := by
    constructor
    · simp
    · simpa only [pair_degree] using hN
  simpa using pow_mul_pow_mem_supported (firstDictionary N) 1 0 h

/-- The even-exponent dictionary contains the second coordinate. -/
theorem second_mem_secondDictionary (N : ℕ) :
    (X 1 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N) := by
  have h : Finsupp.single 0 0 + Finsupp.single 1 1 ∈ secondDictionary N := by
    left
    simp
  simpa using pow_mul_pow_mem_supported (secondDictionary N) 0 1 h

/-- The even-exponent dictionary contains the energy observable. -/
theorem energy_mem_energyDictionary (N : ℕ) (hN : 2 ≤ N) :
    energy ∈ AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N) := by
  let V := AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N)
  have ha : (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 ∈ V := by
    have h : Finsupp.single 0 2 + Finsupp.single 1 0 ∈ energyDictionary N := by
      right
      refine ⟨by simp, by simp, ?_⟩
      simpa only [pair_degree] using hN
    simpa using pow_mul_pow_mem_supported (energyDictionary N) 2 0 h
  have hb : (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2 ∈ V := by
    have h : Finsupp.single 0 0 + Finsupp.single 1 2 ∈ energyDictionary N := by
      left
      simp
    simpa using pow_mul_pow_mem_supported (energyDictionary N) 0 2 h
  change C (1 / 2 : ℝ) * (X 0 ^ 2 + X 1 ^ 2) ∈ V
  rw [mul_add]
  apply V.add_mem
  · simpa only [Algebra.smul_def, C_eq_algebraMap] using V.smul_mem (1 / 2 : ℝ) ha
  · simpa only [Algebra.smul_def, C_eq_algebraMap] using V.smul_mem (1 / 2 : ℝ) hb

private lemma index_mem_of_supported {S : Set (Fin 2 →₀ ℕ)}
    {p : MvPolynomial (Fin 2) ℝ} {d : Fin 2 →₀ ℕ}
    (hp : p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (hc : p.coeff d ≠ 0) : d ∈ S := by
  by_contra hd
  exact hc ((AddMonoidAlgebra.mem_supported' (R := ℝ) (S := ℝ)).mp hp d hd)

private lemma pair_mem_of_pow_mul_pow_supported {S : Set (Fin 2 →₀ ℕ)}
    (i j : ℕ)
    (h : (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j ∈
      AddMonoidAlgebra.supported ℝ ℝ S) :
    Finsupp.single 0 i + Finsupp.single 1 j ∈ S := by
  apply index_mem_of_supported h
  rw [pow_mul_pow_eq_monomial, coeff_monomial]
  simp

/-- In a truncated invariant monomial dictionary, the first nonlinear
transition must be present whenever its coefficient is nonzero. -/
theorem dictionary_contains_rise (α γ β : ℝ) (hβ : β ≠ 0) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (i j : ℕ) (hi : 0 < i) (hdegree : i + j + 1 ≤ N)
    (hsource : Finsupp.single 0 i + Finsupp.single 1 j ∈ S) :
    Finsupp.single 0 i + Finsupp.single 1 (j + 1) ∈ S := by
  apply index_mem_of_supported
    (hInv _ (pow_mul_pow_mem_supported S i j hsource))
  rw [truncatedLie_rise_coefficient α γ β N i j hdegree]
  exact mul_ne_zero hβ (by exact_mod_cast (Nat.ne_of_gt hi))

/-- In a truncated invariant monomial dictionary, the second nonlinear
transition must be present whenever its coefficient is nonzero. -/
theorem dictionary_contains_shift (α γ β : ℝ) (hβ : β ≠ 0) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (i j : ℕ) (hj : 0 < j) (hdegree : i + 2 + (j - 1) ≤ N)
    (hsource : Finsupp.single 0 i + Finsupp.single 1 j ∈ S) :
    Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1) ∈ S := by
  apply index_mem_of_supported
    (hInv _ (pow_mul_pow_mem_supported S i j hsource))
  rw [truncatedLie_shift_coefficient α γ β N i j hj hdegree]
  exact neg_ne_zero.mpr (mul_ne_zero hβ (by exact_mod_cast (Nat.ne_of_gt hj)))

private lemma dictionary_contains_b_powers (α γ β : ℝ) (hβ : β ≠ 0)
    (N : ℕ) (S : Set (Fin 2 →₀ ℕ))
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (i : ℕ) (hi : 0 < i)
    (hseed : Finsupp.single 0 i + Finsupp.single 1 0 ∈ S) :
    ∀ j, i + j ≤ N → Finsupp.single 0 i + Finsupp.single 1 j ∈ S := by
  intro j
  induction j with
  | zero =>
    intro _
    exact hseed
  | succ j ih =>
    intro hdegree
    exact dictionary_contains_rise α γ β hβ N S hInv i j hi (by lia)
      (ih (by lia))

private lemma dictionary_contains_positive_tail (α γ β : ℝ) (hβ : β ≠ 0)
    (N : ℕ) (S : Set (Fin 2 →₀ ℕ))
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (k : ℕ) (hk : 0 < k)
    (hseed : Finsupp.single 0 k + Finsupp.single 1 0 ∈ S) :
    ∀ r j, k + 2 * r + j ≤ N →
      Finsupp.single 0 (k + 2 * r) + Finsupp.single 1 j ∈ S := by
  have hpure : ∀ r, k + 2 * r ≤ N →
      Finsupp.single 0 (k + 2 * r) + Finsupp.single 1 0 ∈ S := by
    intro r
    induction r with
    | zero =>
      intro _
      simpa using hseed
    | succ r ih =>
      intro hdegree
      have hprev := ih (by lia)
      have hnext := dictionary_contains_rise α γ β hβ N S hInv
        (k + 2 * r) 0 (by lia) (by lia) hprev
      have hshift := dictionary_contains_shift α γ β hβ N S hInv
        (k + 2 * r) 1 (by lia) (by lia) hnext
      convert hshift using 1
  intro r j hdegree
  exact dictionary_contains_b_powers α γ β hβ N S hInv (k + 2 * r)
    (by lia) (hpure r (by lia)) j (by lia)

/-- Every truncated invariant monomial dictionary containing the first
coordinate contains all odd-exponent monomials through degree `N`. -/
theorem firstDictionary_minimal (α γ β : ℝ) (hβ : β ≠ 0) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hX : (X 0 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ S)
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S) :
    firstDictionary N ⊆ S := by
  have hseed : Finsupp.single 0 1 + Finsupp.single 1 0 ∈ S :=
    pair_mem_of_pow_mul_pow_supported 1 0 (by simpa using hX)
  intro d hd
  let r := d 0 / 2
  have hi : d 0 = 1 + 2 * r := by
    have hodd : d 0 % 2 = 1 := hd.1
    dsimp [r]
    lia
  have hdegree : 1 + 2 * r + d 1 ≤ N := by
    have h := hd.2
    rw [index_degree, hi] at h
    lia
  have htail := dictionary_contains_positive_tail α γ β hβ N S hInv
    1 (by lia) hseed r (d 1) hdegree
  have heq : d = Finsupp.single 0 (1 + 2 * r) + Finsupp.single 1 (d 1) := by
    calc
      d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := index_decompose d
      _ = _ := by rw [hi]
  exact heq.symm ▸ htail

private lemma even_tail_subset_of_seed (α γ β : ℝ) (hβ : β ≠ 0) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (hseed : Finsupp.single 0 2 + Finsupp.single 1 0 ∈ S) :
    {d : Fin 2 →₀ ℕ | 0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N} ⊆ S := by
  intro d htail
  let r := d 0 / 2 - 1
  have hi : d 0 = 2 + 2 * r := by
    have heven : d 0 % 2 = 0 := htail.2.1
    have hpos : 0 < d 0 := htail.1
    dsimp [r]
    lia
  have hdegree : 2 + 2 * r + d 1 ≤ N := by
    have h := htail.2.2
    rw [index_degree, hi] at h
    lia
  have hresult := dictionary_contains_positive_tail α γ β hβ N S hInv
    2 (by lia) hseed r (d 1) hdegree
  have heq : d = Finsupp.single 0 (2 + 2 * r) + Finsupp.single 1 (d 1) := by
    calc
      d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := index_decompose d
      _ = _ := by rw [hi]
  exact heq.symm ▸ hresult

/-- Every truncated invariant monomial dictionary containing the second
coordinate contains its even-exponent tail and the seed `b`. -/
theorem secondDictionary_minimal (α γ β : ℝ) (hβ : β ≠ 0) (N : ℕ)
    (S : Set (Fin 2 →₀ ℕ))
    (hX : (X 1 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ S)
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S) :
    secondDictionary N ⊆ S := by
  have hseed : Finsupp.single 0 0 + Finsupp.single 1 1 ∈ S :=
    pair_mem_of_pow_mul_pow_supported 0 1 (by simpa using hX)
  intro d hd
  rcases hd with hsingle | htail
  · simpa [hsingle] using hseed
  · have htwo : 2 ≤ N := by
      have h := htail.2.2
      rw [index_degree] at h
      have hpos := htail.1
      have heven := htail.2.1
      lia
    have hpure : Finsupp.single 0 2 + Finsupp.single 1 0 ∈ S := by
      simpa using dictionary_contains_shift α γ β hβ N S hInv
        0 1 (by lia) (by lia) hseed
    exact even_tail_subset_of_seed α γ β hβ N S hInv hpure htail

private lemma energy_coeff_first_sq :
    energy.coeff (Finsupp.single 0 2 + Finsupp.single 1 0) = 1 / 2 := by
  simp [energy, mul_add, X_pow_eq_monomial, coeff_monomial,
    coeff_C_mul, Finsupp.ext_iff, Fin.forall_fin_two]

private lemma energy_coeff_second_sq :
    energy.coeff (Finsupp.single 0 0 + Finsupp.single 1 2) = 1 / 2 := by
  simp [energy, mul_add, X_pow_eq_monomial, coeff_monomial,
    coeff_C_mul, Finsupp.ext_iff, Fin.forall_fin_two]

/-- Every truncated invariant monomial dictionary containing energy contains
both quadratic seeds and their even-exponent tail. -/
theorem energyDictionary_minimal (α γ β : ℝ) (hβ : β ≠ 0)
    (N : ℕ) (_hN : 2 ≤ N) (S : Set (Fin 2 →₀ ℕ))
    (hE : energy ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (hInv : ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S) :
    energyDictionary N ⊆ S := by
  have hfirst : Finsupp.single 0 2 + Finsupp.single 1 0 ∈ S := by
    apply index_mem_of_supported hE
    rw [energy_coeff_first_sq]
    norm_num
  have hsecond : Finsupp.single 0 0 + Finsupp.single 1 2 ∈ S := by
    apply index_mem_of_supported hE
    rw [energy_coeff_second_sq]
    norm_num
  intro d hd
  rcases hd with hsingle | htail
  · simpa [hsingle] using hsecond
  · exact even_tail_subset_of_seed α γ β hβ N S hInv hfirst htail

end TwoModeBurgers
