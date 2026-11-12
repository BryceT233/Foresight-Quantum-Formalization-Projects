/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.SuzukiSepticData
public import FQFP.Algebra.Word.SuzukiCertificateProbe

/-!
# Exact back-expansion of the binary septic commutator data

Integer word-table computations compare every parameter coordinate of the 32-term
right-nested presentations against all 128 associative word positions. The semantics
of the checker is evaluation in any rational associative algebra.

## Main results

* `eval_nestedTable`: nested-table evaluation is the actual right-nested commutator.
* `eval_expandedDefectData_eq`: exact back-expansion of the defect coefficient data.
* `eval_expandedCenteredData_eq`: exact back-expansion of the centered coefficient data.
* `eval_expandedBchData_eq`: exact back-expansion of the logarithm coefficient data.
-/

@[expose] public section

namespace FQFP.SuzukiSepticCertificate

open WordTable

/-- One parameter coordinate of an integer coefficient triple. -/
def coordinate (q : Fin 3) (c : Triple) : ℤ := ![c.1, c.2.1, c.2.2] q

/-- The integer word table of a right-nested commutator, in outermost-first order. -/
def nestedTable : List (Fin 2) → Table (Fin 2)
  | [] => []
  | [a] => [([a], 1)]
  | a :: b :: w =>
      mul [([a], 1)] (nestedTable (b :: w)) ++
        smul (-1) (mul (nestedTable (b :: w)) [([a], 1)])

/-- Expand one parameter coordinate of the right-nested rows into associative words. -/
def expandCoordinate (q : Fin 3) (rows : Rows) : Table (Fin 2) :=
  rows.flatMap fun p ↦ smul (coordinate q p.2) (nestedTable p.1)

/-- Read one parameter coordinate of the associative rows. -/
def readCoordinate (q : Fin 3) (rows : Rows) : Table (Fin 2) :=
  rows.map fun p ↦ (p.1, coordinate q p.2)

/-- Zero-tree checking of the difference of the two complete word tables. -/
def coordinateMatches (nested expanded : Rows) (q : Fin 3) : Bool :=
  BinaryWordTable.isZero (BinaryWordTable.collect
    (expandCoordinate q nested ++ smul (-1) (readCoordinate q expanded)))

/-- The binary word codes enumerate every degree-seven word exactly once. -/
theorem binaryWords_perm_fixedWords :
    ((List.range 128).map binaryWord).Perm (CoeffWordTable.fixedWords 2 7) := by
  decide +kernel

/-- The defect table lists all 128 binary degree-seven positions. -/
theorem expandedDefectData_positions :
    expandedDefectData.map Prod.fst = (List.range 128).map binaryWord := by
  decide +kernel

/-- The centered table lists all 128 binary degree-seven positions. -/
theorem expandedCenteredData_positions :
    expandedCenteredData.map Prod.fst = (List.range 128).map binaryWord := by
  decide +kernel

/-- The BCH table lists all 128 binary degree-seven positions. -/
theorem expandedBchData_positions :
    expandedBchData.map Prod.fst = (List.range 128).map binaryWord := by
  decide +kernel

/-- All three right-nested presentations have exactly 32 rows. -/
theorem nestedData_lengths :
    nestedDefectData.length = 32 ∧ nestedCenteredData.length = 32 ∧
      nestedBchData.length = 32 := by
  decide +kernel

/-- The 32 right-nested words in each of the three presentations are distinct. -/
theorem nestedData_words_nodup :
    (nestedDefectData.map Prod.fst).Nodup ∧ (nestedCenteredData.map Prod.fst).Nodup ∧
      (nestedBchData.map Prod.fst).Nodup := by
  decide +kernel

/-- Every retained right-nested row has at least one nonzero parameter coordinate. -/
theorem nestedData_nonzero :
    (nestedDefectData ++ nestedCenteredData ++ nestedBchData).all
      (fun row ↦ row.2 != (0, 0, 0)) = true := by
  decide +kernel

/-- Evaluate a right-nested word, with its first letter acting outermost. -/
def rightNestedValue {A : Type*} [Ring A] (letters : Fin 2 → A) : List (Fin 2) → A
  | [] => 0
  | [a] => letters a
  | a :: b :: w => ⁅letters a, rightNestedValue letters (b :: w)⁆

section Semantics

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The table recursion evaluates to the indicated right-nested commutator. -/
theorem eval_nestedTable (letters : Fin 2 → A) (w : List (Fin 2)) :
    WordTable.eval 1 letters (nestedTable w) = rightNestedValue letters w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases w with
      | nil => simp [nestedTable, rightNestedValue, eval_singleton]
      | cons b w =>
          simp only [nestedTable, rightNestedValue, eval_append, eval_mul, eval_smul, ih]
          simp [eval_singleton, Ring.lie_def, sub_eq_add_neg]

/-- One rational parameter coordinate of the right-nested presentation. -/
noncomputable def nestedCoordinateValue (letters : Fin 2 → A) (q : Fin 3) (rows : Rows) : A :=
  (rows.map fun p ↦ (coordinate q p.2 : ℚ) • rightNestedValue letters p.1).sum

/-- Expansion of the rows preserves their nested-commutator semantics. -/
theorem eval_expandCoordinate (letters : Fin 2 → A) (q : Fin 3) (rows : Rows) :
    WordTable.eval 1 letters (expandCoordinate q rows) =
      nestedCoordinateValue letters q rows := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
      change WordTable.eval 1 letters
        (smul (coordinate q p.2) (nestedTable p.1) ++ expandCoordinate q rows) =
          (coordinate q p.2 : ℚ) • rightNestedValue letters p.1 +
            nestedCoordinateValue letters q rows
      rw [eval_append, eval_smul, eval_nestedTable, ih]

/-- A checked zero difference gives equality of the complete coordinate polynomials. -/
theorem eval_readCoordinate_eq_of_matches (letters : Fin 2 → A)
    (nested expanded : Rows) (q : Fin 3) (h : coordinateMatches nested expanded q = true) :
    WordTable.eval 1 letters (readCoordinate q expanded) =
      nestedCoordinateValue letters q nested := by
  have hz := BinaryWordTable.eval_table_eq_zero 1 letters
    (expandCoordinate q nested ++ smul (-1) (readCoordinate q expanded)) h
  rw [eval_append, eval_smul, eval_expandCoordinate] at hz
  exact (eq_of_sub_eq_zero (by
    simpa only [Int.cast_neg, Int.cast_one, neg_one_smul, sub_eq_add_neg] using hz)).symm

end Semantics

theorem defect_constant_matches :
    coordinateMatches nestedDefectData expandedDefectData 0 = true := by
  decide +kernel

theorem defect_linear_matches :
    coordinateMatches nestedDefectData expandedDefectData 1 = true := by
  decide +kernel

theorem defect_quadratic_matches :
    coordinateMatches nestedDefectData expandedDefectData 2 = true := by
  decide +kernel

theorem centered_constant_matches :
    coordinateMatches nestedCenteredData expandedCenteredData 0 = true := by
  decide +kernel

theorem centered_linear_matches :
    coordinateMatches nestedCenteredData expandedCenteredData 1 = true := by
  decide +kernel

theorem centered_quadratic_matches :
    coordinateMatches nestedCenteredData expandedCenteredData 2 = true := by
  decide +kernel

theorem bch_constant_matches :
    coordinateMatches nestedBchData expandedBchData 0 = true := by
  decide +kernel

theorem bch_linear_matches :
    coordinateMatches nestedBchData expandedBchData 1 = true := by
  decide +kernel

theorem bch_quadratic_matches :
    coordinateMatches nestedBchData expandedBchData 2 = true := by
  decide +kernel

/-- Every parameter coordinate of the defect data expands back exactly. -/
theorem defect_matches (q : Fin 3) :
    coordinateMatches nestedDefectData expandedDefectData q = true := by
  fin_cases q
  · exact defect_constant_matches
  · exact defect_linear_matches
  · exact defect_quadratic_matches

/-- Every parameter coordinate of the centered data expands back exactly. -/
theorem centered_matches (q : Fin 3) :
    coordinateMatches nestedCenteredData expandedCenteredData q = true := by
  fin_cases q
  · exact centered_constant_matches
  · exact centered_linear_matches
  · exact centered_quadratic_matches

/-- Every parameter coordinate of the BCH data expands back exactly. -/
theorem bch_matches (q : Fin 3) :
    coordinateMatches nestedBchData expandedBchData q = true := by
  fin_cases q
  · exact bch_constant_matches
  · exact bch_linear_matches
  · exact bch_quadratic_matches

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The complete defect coordinate equals the 32-term nested coordinate. -/
theorem eval_expandedDefectData_eq (letters : Fin 2 → A) (q : Fin 3) :
    WordTable.eval 1 letters (readCoordinate q expandedDefectData) =
      nestedCoordinateValue letters q nestedDefectData :=
  eval_readCoordinate_eq_of_matches letters _ _ q (defect_matches q)

/-- The complete centered coordinate equals the 32-term nested coordinate. -/
theorem eval_expandedCenteredData_eq (letters : Fin 2 → A) (q : Fin 3) :
    WordTable.eval 1 letters (readCoordinate q expandedCenteredData) =
      nestedCoordinateValue letters q nestedCenteredData :=
  eval_readCoordinate_eq_of_matches letters _ _ q (centered_matches q)

/-- The complete logarithm coordinate equals the 32-term nested coordinate. -/
theorem eval_expandedBchData_eq (letters : Fin 2 → A) (q : Fin 3) :
    WordTable.eval 1 letters (readCoordinate q expandedBchData) =
      nestedCoordinateValue letters q nestedBchData :=
  eval_readCoordinate_eq_of_matches letters _ _ q (bch_matches q)

/-- Reassemble the three associative coordinates at a real parameter. -/
noncomputable def expandedPolynomialValue [Algebra ℝ A]
    (letters : Fin 2 → A) (p : ℝ) (rows : Rows) : A :=
  ∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) •
    WordTable.eval 1 letters (readCoordinate q rows)

/-- The real scalar polynomial specified by one integer coordinate triple. -/
def tripleValue (p : ℝ) (c : Triple) : ℝ :=
  (c.1 : ℝ) + p * (c.2.1 : ℝ) + p ^ 2 * (c.2.2 : ℝ)

/-- Reassemble the three nested-commutator coordinates at a real parameter. -/
noncomputable def nestedPolynomialValue [Algebra ℝ A]
    (letters : Fin 2 → A) (p : ℝ) (rows : Rows) : A :=
  ∑ q : Fin 3, (p ^ (q : ℕ) / denominator : ℝ) • nestedCoordinateValue letters q rows

/-- **Complete defect-data back-expansion.** The three exact parameter coordinates
are combined before evaluation, for every real parameter and rational real algebra. -/
theorem expandedPolynomialValue_defect_eq [Algebra ℝ A] (letters : Fin 2 → A) (p : ℝ) :
    expandedPolynomialValue letters p expandedDefectData =
      nestedPolynomialValue letters p nestedDefectData := by
  simp only [expandedPolynomialValue, nestedPolynomialValue, eval_expandedDefectData_eq]

/-- **Complete centered-data back-expansion.** Both presentations agree at every real parameter. -/
theorem expandedPolynomialValue_centered_eq [Algebra ℝ A] (letters : Fin 2 → A) (p : ℝ) :
    expandedPolynomialValue letters p expandedCenteredData =
      nestedPolynomialValue letters p nestedCenteredData := by
  simp only [expandedPolynomialValue, nestedPolynomialValue, eval_expandedCenteredData_eq]

/-- **Complete BCH-data back-expansion.** Both presentations agree at every real parameter. -/
theorem expandedPolynomialValue_bch_eq [Algebra ℝ A] (letters : Fin 2 → A) (p : ℝ) :
    expandedPolynomialValue letters p expandedBchData =
      nestedPolynomialValue letters p nestedBchData := by
  simp only [expandedPolynomialValue, nestedPolynomialValue, eval_expandedBchData_eq]

end FQFP.SuzukiSepticCertificate
