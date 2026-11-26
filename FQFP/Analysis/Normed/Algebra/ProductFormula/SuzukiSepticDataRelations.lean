/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Algebra.Word.SuzukiSepticRelations
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticCoefficients
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiDefectSepticCertificate
public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiCenteredSepticJet

/-!
# Polynomial relations between the complete septic data tables

The integer coordinate certificates identify the centered table as the defect
table plus its half-transport correction, and the BCH table as the centered
table minus its midpoint double commutator.

## Main results

* `expandedPolynomialValue_centered_sub_defect`: the centered transport correction.
* `expandedPolynomialValue_centered_sub_bch`: the midpoint double commutator.
* `suzukiCenteredSepticTerm_eq_nestedPolynomialValue`: the actual centered 32-term polynomial.
* `suzukiBchSepticTerm_eq_nestedPolynomialValue`: the actual BCH 32-term polynomial.
-/

@[expose] public noncomputable section

open scoped RealScalar

namespace FQFP.SuzukiSepticCertificate

open Finset WordTable TrotterError

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Integer cubic reduction preserves the transport correction at a Suzuki root. -/
theorem tripleValue_scaledOmegaTriple (c : Triple) (p : ℝ) (hp : BCH.IsSuzukiCubic p) :
    tripleValue p (scaledOmegaTriple c) =
      31500 * (1 - 8 * p + 16 * p ^ 2) * tripleValue p c := by
  have hrel : 60 * p ^ 3 - 48 * p ^ 2 + 12 * p - 1 = 0 := by
    unfold BCH.IsSuzukiCubic BCH.suzukiCubicCoeff at hp
    nlinarith only [hp]
  have h3 : p ^ 3 = (1 : ℝ) / 60 - p / 5 + 4 * p ^ 2 / 5 := by
    linarith only [hrel]
  have h4 : p ^ 4 = (1 : ℝ) / 75 - 43 * p / 300 + 11 * p ^ 2 / 25 := by
    linear_combination p * h3 + (4 / 5 : ℝ) * h3
  dsimp [tripleValue, scaledOmegaTriple]
  push_cast
  linear_combination -31500 * (-8 * (c.2.2 : ℝ) + 16 * c.2.1) * h3 -
    31500 * (16 * (c.2.2 : ℝ)) * h4

section Rational

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Binary bracket tables evaluate to the ordinary algebra commutator. -/
lemma eval_binaryBracketTable (letters : Fin 2 → A) (s t : Table (Fin 2)) :
    WordTable.eval 1 letters (binaryBracketTable s t) =
      ⁅WordTable.eval 1 letters s, WordTable.eval 1 letters t⁆ := by
  rw [binaryBracketTable, eval_append, eval_smul, eval_mul, eval_mul]
  simp [Ring.lie_def, sub_eq_add_neg]

/-- The basic binary table evaluates to the basic binary commutator. -/
lemma eval_binaryCommutatorTable (letters : Fin 2 → A) :
    WordTable.eval 1 letters binaryCommutatorTable = ⁅letters 0, letters 1⁆ := by
  simp [binaryCommutatorTable, WordTable.eval, Ring.lie_def, sub_eq_add_neg]

/-- The binary sum table evaluates to the total generator. -/
lemma eval_binarySumTable (letters : Fin 2 → A) :
    WordTable.eval 1 letters binarySumTable = letters 0 + letters 1 := by
  simp [binarySumTable, WordTable.eval]

/-- The complete centered-minus-defect coordinate is its certified bracket correction. -/
theorem eval_centered_sub_defect_coordinate (letters : Fin 2 → A) (q : Fin 3) :
    WordTable.eval 1 letters (readCoordinate q expandedCenteredData) =
      WordTable.eval 1 letters (readCoordinate q expandedDefectData) +
        ⁅⁅letters 0, letters 1⁆, nestedCoordinateValue letters q scaledOmegaQuinticData⁆ := by
  have hz := BinaryWordTable.eval_table_eq_zero 1 letters _ (centered_defect_matches q)
  rw [eval_append, eval_append, eval_smul, eval_smul, eval_binaryBracketTable,
    eval_binaryCommutatorTable, eval_expandCoordinate] at hz
  apply eq_of_sub_eq_zero
  convert hz using 1
  simp only [Int.cast_neg, Int.cast_one, neg_one_smul]
  abel

/-- The complete centered-minus-BCH coordinate is its certified double commutator. -/
theorem eval_centered_sub_bch_coordinate (letters : Fin 2 → A) (q : Fin 3) :
    WordTable.eval 1 letters (readCoordinate q expandedCenteredData) =
      WordTable.eval 1 letters (readCoordinate q expandedBchData) +
        (14700 : ℚ) • ⁅letters 0 + letters 1,
          ⁅letters 0 + letters 1, nestedCoordinateValue letters q quinticData⁆⁆ := by
  have hz := BinaryWordTable.eval_table_eq_zero 1 letters _ (centered_bch_matches q)
  rw [eval_append, eval_append, eval_smul, eval_smul, eval_binaryBracketTable,
    eval_binaryBracketTable, eval_binarySumTable, eval_expandCoordinate] at hz
  apply eq_of_sub_eq_zero
  convert hz using 1
  simp only [Int.cast_neg, Int.cast_one, Int.cast_ofNat, neg_smul, one_smul]
  abel

end Rational

section Reassembly

variable {A : Type*} [Ring A] [Algebra ℚ A] [Algebra ℝ A]

/-- An empty coordinate list has zero polynomial value. -/
lemma nestedPolynomialValue_nil (letters : Fin 2 → A) (p : ℝ) :
    nestedPolynomialValue letters p [] = 0 := by
  simp [nestedPolynomialValue, nestedCoordinateValue]

/-- Reassemble one integer triple before taking the remaining row sum. -/
lemma nestedPolynomialValue_cons (letters : Fin 2 → A) (p : ℝ)
    (r : List (Fin 2) × Triple) (rows : Rows) :
    nestedPolynomialValue letters p (r :: rows) =
      (tripleValue p r.2 / denominator) • rightNestedValue letters r.1 +
        nestedPolynomialValue letters p rows := by
  simp only [nestedPolynomialValue, nestedCoordinateValue, List.map_cons, List.sum_cons,
    smul_add, sum_add_distrib]
  congr 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [coordinate, tripleValue]
  simp only [Int.cast_smul_eq_zsmul]
  simp only [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  module

/-- Cubic reduction of every row preserves the whole transported quintic polynomial. -/
theorem nestedPolynomialValue_map_scaledOmegaTriple (letters : Fin 2 → A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) (rows : Rows) :
    nestedPolynomialValue letters p (rows.map fun r ↦ (r.1, scaledOmegaTriple r.2)) =
      (31500 * (1 - 8 * p + 16 * p ^ 2)) • nestedPolynomialValue letters p rows := by
  induction rows with
  | nil => simp [nestedPolynomialValue_nil]
  | cons r rows ih =>
      rw [List.map_cons, nestedPolynomialValue_cons, nestedPolynomialValue_cons, ih,
        tripleValue_scaledOmegaTriple r.2 p hp]
      module

/-- The six quintic numerator rows evaluate to the existing complete quintic polynomial. -/
theorem nestedPolynomialValue_quinticData (a b : A) (p : ℝ) :
    nestedPolynomialValue ![a, b] p quinticData =
      (144000 / denominator : ℝ) • BCH.suzukiQuinticTerm a b p := by
  simp only [quinticData, nestedPolynomialValue_cons, nestedPolynomialValue_nil,
    rightNestedValue, BCH.suzukiQuinticTerm, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [tripleValue, denominator, BCH.suzukiQuinticCoeff]
  module

/-- The reduced numerator table is exactly the centered transport correction. -/
theorem nestedPolynomialValue_scaledOmegaQuinticData (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    nestedPolynomialValue ![a, b] p scaledOmegaQuinticData =
      ((5 / 7 : ℝ) * (2 * p ^ 2 - p + 1 / 8)) • BCH.suzukiQuinticTerm a b p := by
  rw [scaledOmegaQuinticData, nestedPolynomialValue_map_scaledOmegaTriple _ p hp,
    nestedPolynomialValue_quinticData, smul_smul]
  congr 1
  norm_num [denominator]
  ring

/-- Reassembling the complete centered data gives the defect data plus the
original half-transport commutator, before taking any norm. -/
theorem expandedPolynomialValue_centered_sub_defect (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    expandedPolynomialValue ![a, b] p expandedCenteredData =
      expandedPolynomialValue ![a, b] p expandedDefectData +
        (5 / 7 : ℝ) • ⁅BCH.suzukiHalfQuadraticTerm a b p, BCH.suzukiQuinticTerm a b p⁆ := by
  simp only [expandedPolynomialValue, eval_centered_sub_defect_coordinate,
    smul_add, sum_add_distrib]
  congr 1
  change (∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) •
    ⁅⁅a, b⁆, nestedCoordinateValue ![a, b] q scaledOmegaQuinticData⁆) = _
  rw [show (∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) •
      ⁅⁅a, b⁆, nestedCoordinateValue ![a, b] q scaledOmegaQuinticData⁆) =
      ⁅⁅a, b⁆, nestedPolynomialValue ![a, b] p scaledOmegaQuinticData⁆ by
    simp only [nestedPolynomialValue, lie_sum, lie_smul]]
  rw [nestedPolynomialValue_scaledOmegaQuinticData a b p hp, BCH.suzukiHalfQuadraticTerm_eq]
  simp only [lie_smul, smul_lie, smul_smul]

/-- Reassembling the complete centered and BCH data gives the exact midpoint
double-commutator correction, for every real parameter. -/
theorem expandedPolynomialValue_centered_sub_bch (a b : A) (p : ℝ) :
    expandedPolynomialValue ![a, b] p expandedCenteredData =
      expandedPolynomialValue ![a, b] p expandedBchData +
        (1 / 24 : ℝ) • ⁅a + b, ⁅a + b, BCH.suzukiQuinticTerm a b p⁆⁆ := by
  simp only [expandedPolynomialValue, eval_centered_sub_bch_coordinate,
    smul_add, sum_add_distrib]
  congr 1
  change (∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) •
    (14700 : ℚ) • ⁅a + b, ⁅a + b, nestedCoordinateValue ![a, b] q quinticData⁆⁆) = _
  calc
    _ = ∑ q : Fin 3, (14700 : ℝ) • ((p ^ (q : ℕ) / denominator : ℝ) •
        ⁅a + b, ⁅a + b, nestedCoordinateValue ![a, b] q quinticData⁆⁆) := by
      apply sum_congr rfl
      intro q _
      rw [← Rat.cast_smul_eq_qsmul ℝ, Rat.cast_ofNat, smul_comm]
    _ = (14700 : ℝ) • (∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) •
        ⁅a + b, ⁅a + b, nestedCoordinateValue ![a, b] q quinticData⁆⁆) := (smul_sum ..).symm
    _ = (14700 : ℝ) • ⁅a + b, ⁅a + b, nestedPolynomialValue ![a, b] p quinticData⁆⁆ := by
      simp only [nestedPolynomialValue, lie_sum, lie_smul]
    _ = _ := by
      rw [nestedPolynomialValue_quinticData]
      simp only [lie_smul, smul_smul]
      norm_num [denominator]

end Reassembly

section CenteredCertificate

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- **Complete centered septic certificate.** The actual centered coefficient
equals the certified polynomial at all 128 binary word positions. -/
theorem suzukiCenteredSepticTerm_eq_expandedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    BCH.suzukiCenteredSepticTerm a b p =
      expandedPolynomialValue ![a, b] p expandedCenteredData := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [BCH.suzukiCenteredSepticTerm, suzukiDefectSepticTerm_eq_expandedPolynomialValue a b p hp]
  exact (expandedPolynomialValue_centered_sub_defect a b p hp).symm

/-- The actual centered coefficient is the complete 32-term right-nested presentation. -/
theorem suzukiCenteredSepticTerm_eq_nestedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    BCH.suzukiCenteredSepticTerm a b p =
      nestedPolynomialValue ![a, b] p nestedCenteredData := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [suzukiCenteredSepticTerm_eq_expandedPolynomialValue a b p hp,
    expandedPolynomialValue_centered_eq]

end CenteredCertificate

section LogarithmCertificate

variable {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]

/-- **Complete BCH septic certificate.** The actual seventh logarithm coefficient
equals the certified polynomial at all 128 binary word positions. -/
theorem suzukiBchSepticTerm_eq_expandedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    BCH.suzukiBchSepticTerm a b p = expandedPolynomialValue ![a, b] p expandedBchData := by
  have hq : Algebra.restrictScalars ℚ ℝ A = (inferInstance : Algebra ℚ A) :=
    Subsingleton.elim _ _
  have hN := suzukiCenteredSepticTerm_eq_expandedPolynomialValue a b p hp
  rw [hq] at hN
  have hD := expandedPolynomialValue_centered_sub_bch a b p
  rw [← hN, BCH.suzukiCenteredSepticTerm_eq_bch a b p hp] at hD
  exact add_right_cancel hD

/-- The actual BCH coefficient is the complete 32-term right-nested presentation. -/
theorem suzukiBchSepticTerm_eq_nestedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    BCH.suzukiBchSepticTerm a b p = nestedPolynomialValue ![a, b] p nestedBchData := by
  rw [suzukiBchSepticTerm_eq_expandedPolynomialValue a b p hp, expandedPolynomialValue_bch_eq]

end LogarithmCertificate

end FQFP.SuzukiSepticCertificate
