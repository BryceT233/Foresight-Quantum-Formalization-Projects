/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
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

`evenDictionary N k` retains the seed `b ^ k` at every order. The bound `N` applies
to its positive even exponents. Taking `k = 1` gives the second-coordinate dictionary
and `k = 2` gives the energy dictionary.

`supported_truncatedLie_invariant_iff` characterizes invariance by closure under
the two degree-raising transitions when the coupling is nonzero.
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
  rw [pow_mul_pow_eq_monomial, ← index_decompose d]

/-- The total degree of a two-mode monomial is the sum of its two exponents. -/
lemma index_degree (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

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

private lemma pow_mul_pow_mem_supported_iff (S : Set (Fin 2 →₀ ℕ)) (i j : ℕ) :
    (X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j ∈
      AddMonoidAlgebra.supported ℝ ℝ S ↔ Finsupp.single 0 i + Finsupp.single 1 j ∈ S := by
  rw [pow_mul_pow_eq_monomial]
  exact (monomial_mem_restrictSupport ℝ).trans (or_iff_left one_ne_zero)

/-- The paper's odd-exponent dictionary for the first coordinate. -/
def firstDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | d 0 % 2 = 1 ∧ d.degree ≤ N}

/-- Exponents of degree at most `N` whose first coordinate is positive and even. -/
def positiveEvenIndices (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | 0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N}

/-- The even-exponent dictionary with the additional monomial `b ^ k`. -/
def evenDictionary (N k : ℕ) : Set (Fin 2 →₀ ℕ) :=
  insert (Finsupp.single 1 k) (positiveEvenIndices N)

/-- The paper's even-exponent dictionary for the second coordinate. -/
def secondDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) := evenDictionary N 1

/-- The paper's even-exponent dictionary for the energy observable. -/
def energyDictionary (N : ℕ) : Set (Fin 2 →₀ ℕ) := evenDictionary N 2

/-- Every exponent in the dictionary has even first coordinate, including the seed. -/
lemma mod_two_eq_zero_of_mem_evenDictionary {N k : ℕ} {d : Fin 2 →₀ ℕ}
    (hd : d ∈ evenDictionary N k) : d 0 % 2 = 0 := by
  rcases hd with rfl | hd
  · simp
  · exact hd.2.1

/-- The truncated Lie operator `π_N D` on the ambient polynomial ring. -/
def truncatedLie (α γ β : ℝ) (N : ℕ) :
    Module.End ℝ (MvPolynomial (Fin 2) ℝ) :=
  (truncTotal (Fin 2) ℝ (N + 1)).comp
    (mkDerivation ℝ (vectorField α γ β)).toLinearMap

private lemma truncTotal_pow_mul_pow (N i j : ℕ) :
    truncTotal (Fin 2) ℝ (N + 1)
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j) =
      if i + j ≤ N then X 0 ^ i * X 1 ^ j else 0 := by
  simp only [pow_mul_pow_eq_monomial, truncTotal_monomial, pair_degree, Nat.lt_add_one_iff]

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

private lemma coeff_truncatedLie_pow_mul_pow (α γ β : ℝ) (N i j k l : ℕ)
    (hdegree : k + l ≤ N) :
    (truncatedLie α γ β N ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j)).coeff
      (Finsupp.single 0 k + Finsupp.single 1 l) =
        (if i = k ∧ j = l then -(α * i + γ * j) else 0) +
        (if i = k ∧ j + 1 = l then β * i else 0) -
        (if i + 2 = k ∧ j - 1 = l then β * j else 0) := by
  rw [truncatedLie, LinearMap.comp_apply, coeff_truncTotal, pair_degree,
    ite_eq_left (Nat.lt_succ_of_le hdegree), Derivation.coeFn_coe, lieDerivation_pow_mul_pow]
  simp only [mul_assoc, pow_mul_pow_eq_monomial,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.coe_neg, Pi.neg_apply, coeff_C_mul,
    coeff_monomial, pair_eq_pair_iff, mul_ite, mul_one, mul_zero, neg_ite, neg_zero]

private lemma truncatedLie_rise_coefficient (α γ β : ℝ) (N i j : ℕ)
    (hdegree : i + j + 1 ≤ N) :
    (truncatedLie α γ β N
      ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j)).coeff
        (Finsupp.single 0 i + Finsupp.single 1 (j + 1)) = β * (i : ℝ) := by
  rw [coeff_truncatedLie_pow_mul_pow α γ β N i j i (j + 1) (by lia)]
  simp

private lemma truncatedLie_shift_coefficient (α γ β : ℝ) (N i j : ℕ)
    (hdegree : i + 2 + (j - 1) ≤ N) :
    (truncatedLie α γ β N
      ((X 0 : MvPolynomial (Fin 2) ℝ) ^ i * X 1 ^ j)).coeff
        (Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1)) =
      -(β * (j : ℝ)) := by
  rw [coeff_truncatedLie_pow_mul_pow α γ β N i j (i + 2) (j - 1) hdegree]
  simp

/-- Closure of an exponent set under the nonlinear transitions retained at order `N`. -/
structure IsClosedUnderTransitions (N : ℕ) (S : Set (Fin 2 →₀ ℕ)) : Prop where
  /-- The term with coefficient `β i` raises the second exponent by one. -/
  rise {i j : ℕ} : Finsupp.single 0 i + Finsupp.single 1 j ∈ S →
    0 < i → i + j < N → Finsupp.single 0 i + Finsupp.single 1 (j + 1) ∈ S
  /-- The term with coefficient `-β j` trades one second-coordinate power for two first powers. -/
  shift {i j : ℕ} : Finsupp.single 0 i + Finsupp.single 1 j ∈ S →
    0 < j → i + j < N → Finsupp.single 0 (i + 2) + Finsupp.single 1 (j - 1) ∈ S

private lemma index_mem_of_supported {S : Set (Fin 2 →₀ ℕ)}
    {p : MvPolynomial (Fin 2) ℝ} {d : Fin 2 →₀ ℕ}
    (hp : p ∈ AddMonoidAlgebra.supported ℝ ℝ S)
    (hc : p.coeff d ≠ 0) : d ∈ S :=
  (mem_restrictSupport_iff ℝ).mp hp (mem_support_iff.mpr hc)

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
    (hInv _ ((pow_mul_pow_mem_supported_iff S i j).2 hsource))
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
    (hInv _ ((pow_mul_pow_mem_supported_iff S i j).2 hsource))
  rw [truncatedLie_shift_coefficient α γ β N i j hdegree]
  exact neg_ne_zero.mpr (mul_ne_zero hβ (by exact_mod_cast (Nat.ne_of_gt hj)))

/-- A monomial span is invariant exactly when nonzero coupling implies closure under the
retained transitions. In particular every monomial span is invariant when `β = 0`. -/
theorem supported_truncatedLie_invariant_iff (α γ β : ℝ) (N : ℕ) (S : Set (Fin 2 →₀ ℕ)) :
    (∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ S,
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S) ↔
      (β ≠ 0 → IsClosedUnderTransitions N S) := by
  constructor
  · intro hInv hβ
    exact ⟨fun hs hi hdeg => dictionary_contains_rise α γ β hβ N S hInv _ _ hi hdeg hs,
      fun hs hj hdeg => dictionary_contains_shift α γ β hβ N S hInv _ _ hj (by lia) hs⟩
  · intro hS
    let V := restrictSupport ℝ S
    have hterm (c : ℝ) (i j : ℕ)
        (hmem : c ≠ 0 → i + j ≤ N → Finsupp.single 0 i + Finsupp.single 1 j ∈ S) :
        C c * (if i + j ≤ N then X 0 ^ i * X 1 ^ j else 0) ∈ V := by
      by_cases hc : c = 0
      · simp [hc]
      rw [C_mul']
      apply V.smul_mem
      split_ifs with hdegree
      · exact (pow_mul_pow_mem_supported_iff S i j).2 (hmem hc hdegree)
      · exact V.zero_mem
    change restrictSupport ℝ S ≤ V.comap (truncatedLie α γ β N)
    rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    intro d hd
    change truncatedLie α γ β N (monomial d 1) ∈ V
    rw [monomial_decompose d, truncatedLie_pow_mul_pow, neg_mul]
    have hd' : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) ∈ S := index_decompose d ▸ hd
    apply V.sub_mem
    · apply V.add_mem
      · exact V.neg_mem (hterm _ _ _ fun _ _ => hd')
      · rw [Nat.add_assoc]
        apply hterm
        intro hc hdegree
        exact (hS (left_ne_zero_of_mul hc)).rise hd'
          (Nat.pos_of_ne_zero (by exact_mod_cast right_ne_zero_of_mul hc)) (by lia)
    · apply hterm
      intro hc hdegree
      have hj : 0 < d 1 := Nat.pos_of_ne_zero (by exact_mod_cast right_ne_zero_of_mul hc)
      exact (hS (left_ne_zero_of_mul hc)).shift hd' hj (by lia)

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
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ S :=
  (supported_truncatedLie_invariant_iff α γ β N S).2 fun _ =>
    ⟨fun hs hi hdeg => hrise _ _ hs hi hdeg, fun hs hj hdeg => hshift _ _ hs hj (by lia)⟩

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

/-- Adding any pure second-coordinate power to the positive even exponents gives an
invariant dictionary for the truncated operator. -/
theorem evenDictionary_invariant (α γ β : ℝ) (N k : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (evenDictionary N k),
      truncatedLie α γ β N p ∈ AddMonoidAlgebra.supported ℝ ℝ (evenDictionary N k) := by
  apply supported_truncatedLie_invariant
  · intro i j hs hi hdegree
    right
    refine ⟨by simpa using hi, ?_, by simpa only [pair_degree, Nat.add_assoc] using hdegree⟩
    simpa using mod_two_eq_zero_of_mem_evenDictionary hs
  · intro i j hs _ hdegree
    right
    refine ⟨by simp, ?_, by simpa only [pair_degree] using hdegree⟩
    simpa [Nat.add_mod] using mod_two_eq_zero_of_mem_evenDictionary hs

/-- The second-coordinate dictionary is invariant under truncation. -/
theorem secondDictionary_invariant (α γ β : ℝ) (N : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N),
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N) :=
  evenDictionary_invariant α γ β N 1

/-- The energy dictionary is invariant under truncation. -/
theorem energyDictionary_invariant (α γ β : ℝ) (N : ℕ) :
    ∀ p ∈ AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N),
      truncatedLie α γ β N p ∈
        AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N) :=
  evenDictionary_invariant α γ β N 2

/-- The odd-exponent dictionary contains the first coordinate. -/
theorem first_mem_firstDictionary (N : ℕ) (hN : 1 ≤ N) :
    (X 0 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ (firstDictionary N) := by
  change X 0 ∈ restrictSupport ℝ (firstDictionary N)
  simpa [X, firstDictionary, Finsupp.degree_single] using hN

/-- The even-exponent dictionary contains the second coordinate. -/
theorem second_mem_secondDictionary (N : ℕ) :
    (X 1 : MvPolynomial (Fin 2) ℝ) ∈
      AddMonoidAlgebra.supported ℝ ℝ (secondDictionary N) := by
  change X 1 ∈ restrictSupport ℝ (secondDictionary N)
  simp [X, secondDictionary, evenDictionary]

/-- The even-exponent dictionary contains the energy observable. -/
theorem energy_mem_energyDictionary (N : ℕ) (hN : 2 ≤ N) :
    energy ∈ AddMonoidAlgebra.supported ℝ ℝ (energyDictionary N) := by
  change energy ∈ restrictSupport ℝ (energyDictionary N)
  rw [energy, C_mul']
  apply Submodule.smul_mem
  apply Submodule.add_mem <;>
    simp [X_pow_eq_monomial, energyDictionary, evenDictionary, positiveEvenIndices,
      Finsupp.degree_single, hN]

private lemma IsClosedUnderTransitions.contains_b_powers {N : ℕ} {S : Set (Fin 2 →₀ ℕ)}
    (hS : IsClosedUnderTransitions N S)
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
    exact hS.rise (ih (by lia)) hi (by lia)

private lemma IsClosedUnderTransitions.contains_positive_tail {N : ℕ} {S : Set (Fin 2 →₀ ℕ)}
    (hS : IsClosedUnderTransitions N S)
    (k : ℕ) (hk : 0 < k)
    (hseed : Finsupp.single 0 k + Finsupp.single 1 0 ∈ S)
    {d : Fin 2 →₀ ℕ} (hstart : k ≤ d 0) (hparity : d 0 % 2 = k % 2)
    (hdegree : d.degree ≤ N) : d ∈ S := by
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
      have hnext := hS.rise hprev (by lia) (by lia)
      exact hS.shift hnext (by lia) (by lia)
  let r := (d 0 - k) / 2
  have hrow : k + 2 * r = d 0 := by
    dsimp [r]
    lia
  rw [index_degree] at hdegree
  have hbase : Finsupp.single 0 (d 0) + Finsupp.single 1 0 ∈ S := hrow ▸ hpure r (by lia)
  rw [index_decompose d]
  exact hS.contains_b_powers (d 0) (by lia) hbase (d 1) hdegree

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
    (pow_mul_pow_mem_supported_iff S 1 0).1 (by simpa using hX)
  have hS := (supported_truncatedLie_invariant_iff α γ β N S).mp hInv hβ
  intro d hd
  have hodd : d 0 % 2 = 1 := hd.1
  exact hS.contains_positive_tail 1 (by lia) hseed (by lia) hodd hd.2

private lemma IsClosedUnderTransitions.positiveEvenIndices_subset {N : ℕ} {S : Set (Fin 2 →₀ ℕ)}
    (hS : IsClosedUnderTransitions N S)
    (hseed : Finsupp.single 0 2 + Finsupp.single 1 0 ∈ S) :
    positiveEvenIndices N ⊆ S := by
  rintro d ⟨hpos, heven, hdegree⟩
  exact hS.contains_positive_tail 2 (by lia) hseed (by lia) heven hdegree

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
    (pow_mul_pow_mem_supported_iff S 0 1).1 (by simpa using hX)
  have hS := (supported_truncatedLie_invariant_iff α γ β N S).mp hInv hβ
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
      simpa using hS.shift hseed (by lia) (by lia)
    exact hS.positiveEvenIndices_subset hpure htail

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
  have hS := (supported_truncatedLie_invariant_iff α γ β N S).mp hInv hβ
  exact Set.insert_subset (by simpa using hsecond) (hS.positiveEvenIndices_subset hfirst)

end TwoModeBurgers
