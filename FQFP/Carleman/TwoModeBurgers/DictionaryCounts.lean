/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Dictionaries

/-!
# Sizes of the minimal two-mode monomial dictionaries

The cardinal formulas count the explicit index sets in `Dictionaries.lean`.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

private lemma degree_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum]
  simp only [Fin.sum_univ_two]

private lemma index_two (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
  ext i
  fin_cases i <;> simp

private def firstDictionaryEquiv (N : ℕ) :
    firstDictionary N ≃ Σ r : Fin ((N + 1) / 2), Fin (N - 2 * r.val) where
  toFun d := by
    have hodd : d.val 0 % 2 = 1 := d.property.1
    have hdegree : d.val 0 + d.val 1 ≤ N := by
      simpa only [degree_two] using d.property.2
    refine ⟨⟨d.val 0 / 2, by lia⟩, ⟨d.val 1, by lia⟩⟩
  invFun p := by
    refine ⟨Finsupp.single 0 (2 * p.1.val + 1) + Finsupp.single 1 p.2.val, ?_⟩
    constructor
    · simp
    · simp only [degree_two]
      have hr := p.1.isLt
      have hj := p.2.isLt
      simp at *
      lia
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · have hodd : d.val 0 % 2 = 1 := d.property.1
      have hdiv : 2 * (d.val 0 / 2) + 1 = d.val 0 := by lia
      simp [hdiv]
    · simp
  right_inv p := by
    cases p with
    | mk r j =>
      cases r with
      | mk r hr =>
        cases j with
        | mk j hj =>
          have hdiv : (2 * r + 1) / 2 = r := by
            calc
              (2 * r + 1) / 2 = (1 + 2 * r) / 2 := by ring_nf
              _ = r := by simp [Nat.add_mul_div_left]
          have hdiv' :
              (Finsupp.single (0 : Fin 2) (2 * r + 1) +
                Finsupp.single 1 j : Fin 2 →₀ ℕ) 0 / 2 = r := by
            simpa using hdiv
          simp only [Sigma.mk.injEq, Fin.mk.injEq]
          constructor
          · exact hdiv'
          · have hindex : N - 2 *
                ((Finsupp.single (0 : Fin 2) (2 * r + 1) +
                  Finsupp.single 1 j : Fin 2 →₀ ℕ) 0 / 2) = N - 2 * r := by
              rw [hdiv']
            exact (Fin.heq_ext_iff hindex).2 (by simp)

private lemma odd_row_sum (N : ℕ) :
    (∑ r ∈ Finset.range ((N + 1) / 2), (N - 2 * r)) =
      (N + 1) ^ 2 / 4 := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more N ih =>
    have hm : (N + 3) / 2 = (N + 1) / 2 + 1 := by lia
    rw [hm, Finset.sum_range_succ]
    have hsum :
        (∑ r ∈ Finset.range ((N + 1) / 2), (N + 2 - 2 * r)) =
          (∑ r ∈ Finset.range ((N + 1) / 2), (N - 2 * r)) +
            2 * ((N + 1) / 2) := by
      calc
        _ = ∑ r ∈ Finset.range ((N + 1) / 2), ((N - 2 * r) + 2) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hr' := Finset.mem_range.mp hr
          lia
        _ = _ := by simp [Finset.sum_add_distrib, mul_comm]
    rw [hsum, ih]
    have hlast : N + 2 - 2 * ((N + 1) / 2) +
        2 * ((N + 1) / 2) = N + 2 := by lia
    have hsq : (N + 3) ^ 2 = (N + 1) ^ 2 + 4 * (N + 2) := by ring
    rw [hsq]
    rw [Nat.add_mul_div_left] <;> lia

/-- The odd-exponent dictionary has the paper's quadratic cardinality. -/
theorem firstDictionary_ncard (N : ℕ) :
    (firstDictionary N).ncard = (N + 1) ^ 2 / 4 := by
  have hfinite : (firstDictionary N).Finite :=
    (Finsupp.finite_of_degree_le N).subset (by
      intro d hd
      exact hd.2)
  have : Fintype (firstDictionary N) := hfinite.fintype
  rw [← Set.fintypeCard_eq_ncard]
  rw [Fintype.card_congr (firstDictionaryEquiv N)]
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => N - 2 * r)]
  exact odd_row_sum N

private def evenTail (N : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {d | 0 < d 0 ∧ d 0 % 2 = 0 ∧ d.degree ≤ N}

private lemma evenTail_finite (N : ℕ) : (evenTail N).Finite :=
  (Finsupp.finite_of_degree_le N).subset (by
    intro d hd
    exact hd.2.2)

private def evenTailEquiv (N : ℕ) : evenTail N ≃ firstDictionary (N - 1) where
  toFun d := by
    refine ⟨Finsupp.single 0 (d.val 0 - 1) + Finsupp.single 1 (d.val 1), ?_⟩
    have hpos : 0 < d.val 0 := d.property.1
    have heven : d.val 0 % 2 = 0 := d.property.2.1
    have hdegree : d.val 0 + d.val 1 ≤ N := by
      simpa only [degree_two] using d.property.2.2
    constructor
    · simp
      lia
    · simp only [degree_two]
      simp
      lia
  invFun d := by
    refine ⟨Finsupp.single 0 (d.val 0 + 1) + Finsupp.single 1 (d.val 1), ?_⟩
    have hodd : d.val 0 % 2 = 1 := d.property.1
    have hdegree : d.val 0 + d.val 1 ≤ N - 1 := by
      simpa only [degree_two] using d.property.2
    refine ⟨by simp, ?_, ?_⟩
    · simp
      lia
    · simp only [degree_two]
      simp
      lia
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · have hpos : 0 < d.val 0 := d.property.1
      simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))]
    · simp
  right_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i
    · have hodd : d.val 0 % 2 = 1 := d.property.1
      have hpos : 0 < d.val 0 := by lia
      simp
    · simp

private lemma evenTail_ncard (N : ℕ) : (evenTail N).ncard = N ^ 2 / 4 := by
  have hfinite := evenTail_finite N
  have hfinite' : (firstDictionary (N - 1)).Finite :=
    (Finsupp.finite_of_degree_le (N - 1)).subset (by
      intro d hd
      exact hd.2)
  have : Fintype (evenTail N) := hfinite.fintype
  have : Fintype (firstDictionary (N - 1)) := hfinite'.fintype
  rw [← Set.fintypeCard_eq_ncard]
  rw [Fintype.card_congr (evenTailEquiv N)]
  rw [Set.fintypeCard_eq_ncard, firstDictionary_ncard]
  cases N with
  | zero => norm_num
  | succ N => simp

/-- The second-coordinate dictionary has `1 + ⌊N²/4⌋` monomials. -/
theorem secondDictionary_ncard (N : ℕ) :
    (secondDictionary N).ncard = 1 + N ^ 2 / 4 := by
  have hset : secondDictionary N = insert (Finsupp.single 1 1) (evenTail N) := by
    ext d
    simp [secondDictionary, evenTail]
  have hnot : Finsupp.single (1 : Fin 2) 1 ∉ evenTail N := by
    simp [evenTail]
  rw [hset, Set.ncard_insert_of_notMem hnot (evenTail_finite N), evenTail_ncard]
  lia

/-- The energy dictionary has the same cardinality as the second-coordinate dictionary. -/
theorem energyDictionary_ncard (N : ℕ) :
    (energyDictionary N).ncard = 1 + N ^ 2 / 4 := by
  have hset : energyDictionary N = insert (Finsupp.single 1 2) (evenTail N) := by
    ext d
    simp [energyDictionary, evenTail]
  have hnot : Finsupp.single (1 : Fin 2) 2 ∉ evenTail N := by
    simp [evenTail]
  rw [hset, Set.ncard_insert_of_notMem hnot (evenTail_finite N), evenTail_ncard]
  lia

/-- The two state-coordinate dictionaries contain no common monomial. -/
theorem first_second_dictionaries_disjoint (N : ℕ) :
    Disjoint (firstDictionary N) (secondDictionary N) := by
  rw [Set.disjoint_left]
  intro d hfirst hsecond
  rcases hsecond with hseed | htail
  · have hzero : d 0 = 0 := by rw [hseed]; simp
    have hodd := hfirst.1
    simp [hzero] at hodd
  · have hodd := hfirst.1
    have heven := htail.2.1
    lia

/-- The union of the two state dictionaries has the sum of their sizes. -/
theorem stateDictionaries_union_ncard (N : ℕ) :
    (firstDictionary N ∪ secondDictionary N).ncard =
      (N + 1) ^ 2 / 4 + (1 + N ^ 2 / 4) := by
  have hfirst : (firstDictionary N).Finite :=
    (Finsupp.finite_of_degree_le N).subset (by
      intro d hd
      exact hd.2)
  have hsecond : (secondDictionary N).Finite := by
    have hset : secondDictionary N = insert (Finsupp.single 1 1) (evenTail N) := by
      ext d
      simp [secondDictionary, evenTail]
    rw [hset]
    exact (evenTail_finite N).insert _
  rw [Set.ncard_union_eq (first_second_dictionaries_disjoint N) hfirst hsecond,
    firstDictionary_ncard, secondDictionary_ncard]

end TwoModeBurgers
