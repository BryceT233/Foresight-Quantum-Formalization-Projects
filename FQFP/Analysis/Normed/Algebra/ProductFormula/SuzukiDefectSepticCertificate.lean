/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiSepticCoefficients
public import FQFP.Algebra.Word.SuzukiDefectSepticVerification
public import FQFP.Algebra.Word.SuzukiSepticCertificate

/-!
# The actual Suzuki septic defect and its complete word certificate

The integer conjugation recurrence evaluates to the factorial-normalized actual
half-defect coefficient. A cubic quotient certificate identifies its 128 binary
word positions with the three exact parameter coordinates.

## Main results

* `evaluate_defectCoeffTable`: semantics of the integer grouped recurrence.
* `suzukiDefectSepticTerm_eq_expandedPolynomialValue`: the actual 128-position certificate.
* `suzukiDefectSepticTerm_eq_nestedPolynomialValue`: the actual 32-term representation.
-/

@[expose] public noncomputable section

namespace FQFP.SuzukiSepticCertificate

open Finset TrotterError CoeffWordTable

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Evaluate a central-parameter table while preserving the ordinary letter order. -/
def evaluate (p : ℝ) (letters : Fin 2 → A) (t : ParamTable) : A :=
  CoeffWordTable.eval (Int.castRingHom ℝ)
    (fun x ↦ match x with | none => p • 1 | some i => letters i) t

lemma evaluate_collect (p : ℝ) (letters : Fin 2 → A) (t : ParamTable) :
    evaluate p letters (CentralBinaryWordTable.collect t) = evaluate p letters t :=
  CentralBinaryWordTable.eval_collect _ p letters t

lemma evaluate_append (p : ℝ) (letters : Fin 2 → A) (s t : ParamTable) :
    evaluate p letters (s ++ t) = evaluate p letters s + evaluate p letters t :=
  CoeffWordTable.eval_append ..

lemma evaluate_smul (p : ℝ) (letters : Fin 2 → A) (c : ℤ) (t : ParamTable) :
    evaluate p letters (smul c t) = (c : ℝ) • evaluate p letters t :=
  CoeffWordTable.eval_smul ..

lemma evaluate_mul (p : ℝ) (letters : Fin 2 → A) (s t : ParamTable) :
    evaluate p letters (mul s t) = evaluate p letters s * evaluate p letters t :=
  CoeffWordTable.eval_mul ..

lemma evaluate_bracketTable (p : ℝ) (letters : Fin 2 → A) (s t : ParamTable) :
    evaluate p letters (bracketTable s t) =
      ⁅evaluate p letters s, evaluate p letters t⁆ := by
  rw [bracketTable, evaluate_collect, evaluate_append, evaluate_smul,
    evaluate_mul, evaluate_mul]
  simp [Ring.lie_def, sub_eq_add_neg]

lemma evaluate_adTable (p : ℝ) (letters : Fin 2 → A) (s t : ParamTable) (n : ℕ) :
    evaluate p letters (adTable s n t) =
      adPow (evaluate p letters s) n (evaluate p letters t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [adTable, evaluate_bracketTable, ih, ad_pow_succ]

lemma defectExpWeight_cast (q : ℕ) (hq : q ≤ 6) :
    (defectExpWeight q : ℝ) = (Nat.factorial q : ℝ)⁻¹ * (-420 : ℝ) ^ q := by
  interval_cases q <;> norm_num [defectExpWeight, Nat.factorial]

/-- The integer recurrence is the actual grouped coefficient with its common scale removed. -/
theorem evaluate_defectCoeffTable (p : ℝ) (letters : Fin 2 → A)
    {s : ℕ} (Z : Fin s → ParamTable) (n : ℕ) (hn : n ≤ 6) :
    evaluate p letters (defectCoeffTable Z n) = (1 / 420 : ℝ) •
      groupedConjCoeff (fun i ↦ (-420 : ℝ) • evaluate p letters (Z i))
        (fun i ↦ (420 : ℝ) • evaluate p letters (Z i))
          ((420 : ℝ) • evaluate p letters defectSeedTable) n := by
  induction s generalizing n with
  | zero =>
      by_cases hn0 : n = 0 <;>
        simp [defectCoeffTable, groupedConjCoeff, hn0, evaluate,
          CoeffWordTable.eval_nil, smul_smul]
  | succ s ih =>
      rw [defectCoeffTable, evaluate_collect, evaluate_append,
        show evaluate p letters ((List.range (n + 1)).flatMap fun q ↦
          smul (defectExpWeight q) (adTable (Z (Fin.last s)) q
            (defectCoeffTable (fun i ↦ Z i.castSucc) (n - q)))) = _ from
          CoeffWordTable.eval_flatMap_range _ _ _ _, groupedConjCoeff, smul_add, smul_sum]
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro q hq
        change evaluate p letters (smul (defectExpWeight q)
          (adTable (Z (Fin.last s)) q
            (defectCoeffTable (fun i ↦ Z i.castSucc) (n - q)))) = _
        rw [evaluate_smul, evaluate_adTable, ih (fun i ↦ Z i.castSucc) (n - q) (by lia),
          map_smul, smul_smul, adPow_smul_left, smul_smul, smul_smul,
          defectExpWeight_cast q (by
            have := mem_range.mp hq
            lia)]
        congr 1
        ring
      · by_cases hn0 : n = 0 <;> simp [hn0, evaluate, CoeffWordTable.eval_nil, smul_smul]

/-- The integer half-generators evaluate to the actual Suzuki half-generators. -/
lemma evaluate_halfTables (a b : A) (p : ℝ) (i : Fin 6) :
    (420 : ℝ) • evaluate p ![(840 : ℝ)⁻¹ • a, (840 : ℝ)⁻¹ • b] (halfTables i) =
      BCH.fiveStageStrangHalfGenerator a b p i := by
  fin_cases i <;>
    norm_num [evaluate, halfTables, BCH.fiveStageStrangHalfGenerator,
      CoeffWordTable.eval, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_add, smul_sub]
  all_goals module

/-- The common-scale seed is exactly the actual half-defect seed. -/
lemma evaluate_defectSeedTable (a b : A) (p : ℝ) :
    (420 : ℝ) • evaluate p ![(840 : ℝ)⁻¹ • a, (840 : ℝ)⁻¹ • b] defectSeedTable =
      -(1 / 2 : ℝ) • (a + b) := by
  norm_num [evaluate, defectSeedTable, CoeffWordTable.eval, smul_add, smul_smul]

/-- The complete seventh-degree defect is `120` times the integer coefficient table. -/
theorem suzukiDefectSepticTerm_eq_evaluate (a b : A) (p : ℝ) :
    BCH.suzukiDefectSepticTerm a b p =
      (120 : ℝ) • evaluate p ![(840 : ℝ)⁻¹ • a, (840 : ℝ)⁻¹ • b]
        (defectCoeffTable halfTables 6) := by
  rw [evaluate_defectCoeffTable p _ halfTables 6 (by norm_num)]
  simp only [neg_smul, evaluate_halfTables, evaluate_defectSeedTable,
    BCH.suzukiDefectSepticTerm, smul_smul]
  norm_num

lemma evaluate_cubicRelationTable (letters : Fin 2 → A) (p : ℝ) :
    evaluate p letters cubicRelationTable = BCH.suzukiCubicCoeff p • (1 : A) := by
  norm_num [evaluate, cubicRelationTable, CoeffWordTable.eval, BCH.suzukiCubicCoeff,
    smul_mul_assoc, smul_smul]
  module

/-- Direct ordered-word evaluation of the unnormalized three-coordinate rows. -/
def rowsValue (letters : Fin 2 → A) (p : ℝ) (rows : Rows) : A :=
  (rows.map fun row ↦ tripleValue p row.2 • (row.1.map letters).prod).sum

lemma evaluate_septicCoordinateTable (letters : Fin 2 → A) (p : ℝ) (rows : Rows) :
    evaluate p letters (septicCoordinateTable rows) = rowsValue letters p rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change evaluate p letters
        ([(row.1.map some, row.2.1), (none :: row.1.map some, row.2.2.1),
          (none :: none :: row.1.map some, row.2.2.2)] ++ septicCoordinateTable rows) =
            tripleValue p row.2 • (row.1.map letters).prod + rowsValue letters p rows
      rw [evaluate_append, ih]
      congr 1
      simp only [evaluate, CoeffWordTable.eval, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.map_map, Function.comp_def, List.prod_cons,
        smul_mul_assoc, one_mul, smul_smul, Int.coe_castRingHom, add_zero, tripleValue]
      module

lemma rowsValue_smul (letters : Fin 2 → A) (p c : ℝ) (rows : Rows) (n : ℕ)
    (hlen : ∀ row ∈ rows, row.1.length = n) :
    rowsValue (fun i ↦ c • letters i) p rows = c ^ n • rowsValue letters p rows := by
  induction rows with
  | nil => simp [rowsValue]
  | cons row rows ih =>
      change tripleValue p row.2 • (row.1.map fun i ↦ c • letters i).prod +
        rowsValue (fun i ↦ c • letters i) p rows =
          c ^ n • (tripleValue p row.2 • (row.1.map letters).prod + rowsValue letters p rows)
      rw [prod_map_smul, hlen row List.mem_cons_self,
        ih (fun r hr ↦ hlen r (List.mem_cons_of_mem row hr)), smul_add, smul_comm]

section RationalScalars

variable [Algebra ℚ A]

lemma eval_real_eq_eval_rat (letters : Fin 2 → A) (t : WordTable.Table (Fin 2)) :
    CoeffWordTable.eval (Int.castRingHom ℝ) letters t = WordTable.eval 1 letters t := by
  simp only [CoeffWordTable.eval, WordTable.eval, one_pow, div_one,
    Int.coe_castRingHom, Int.cast_smul_eq_zsmul]

lemma rowsValue_eq_expandedPolynomialValue (letters : Fin 2 → A) (p : ℝ) (rows : Rows) :
    rowsValue letters p rows = (denominator : ℝ) • expandedPolynomialValue letters p rows := by
  induction rows with
  | nil => simp [rowsValue, expandedPolynomialValue, readCoordinate, WordTable.eval_nil]
  | cons row rows ih =>
      change tripleValue p row.2 • (row.1.map letters).prod + rowsValue letters p rows = _
      rw [ih]
      simp only [expandedPolynomialValue, readCoordinate, List.map_cons,
        WordTable.eval_cons, one_pow, div_one, smul_add, Finset.sum_add_distrib]
      congr 1
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, coordinate, pow_zero,
        Fin.val_zero, Fin.val_succ, smul_add, smul_smul, tripleValue,
        ← Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℚ]
      norm_num [denominator]
      module

end RationalScalars

/-- Under cubic cancellation, the actual coefficient table has the certified reduced target. -/
theorem evaluate_defectCoeffTable_eq_target (letters : Fin 2 → A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    evaluate p letters (defectCoeffTable halfTables 6) =
      (48404160 : ℝ) • evaluate p letters (septicCoordinateTable expandedDefectData) := by
  have hz := congrArg (evaluate p letters) defectSepticResidual_eq_nil
  rw [defectSepticResidual, evaluate_collect, evaluate_append, evaluate_append,
    evaluate_smul, evaluate_smul, evaluate_mul, evaluate_cubicRelationTable] at hz
  change BCH.suzukiCubicCoeff p = 0 at hp
  simp only [hp, zero_smul, zero_mul, smul_zero, add_zero] at hz
  simpa only [evaluate, CoeffWordTable.eval_nil, Int.cast_neg, Int.cast_ofNat,
    neg_smul, sub_eq_add_neg, add_neg_eq_zero] using hz

/-- Every position retained in the complete defect table has degree seven. -/
lemma expandedDefectData_lengths :
    ∀ row ∈ expandedDefectData, row.1.length = 7 := by
  intro row hrow
  have hw : row.1 ∈ expandedDefectData.map Prod.fst :=
    List.mem_map.mpr ⟨row, hrow, rfl⟩
  rw [expandedDefectData_positions] at hw
  exact (CoeffWordTable.mem_fixedWords_iff_length 2 7 row.1).mp
    (binaryWords_perm_fixedWords.subset hw)

/-- **Complete septic defect certificate.** The actual grouped coefficient equals
the certified 128-position polynomial, evaluated at the same generators and parameter. -/
theorem suzukiDefectSepticTerm_eq_expandedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    BCH.suzukiDefectSepticTerm a b p =
      expandedPolynomialValue ![a, b] p expandedDefectData := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [suzukiDefectSepticTerm_eq_evaluate,
    evaluate_defectCoeffTable_eq_target _ p hp, evaluate_septicCoordinateTable]
  change (120 : ℝ) • (48404160 : ℝ) •
    rowsValue (fun i ↦ (840 : ℝ)⁻¹ • ![a, b] i) p expandedDefectData = _
  rw [rowsValue_smul _ p _ expandedDefectData 7 expandedDefectData_lengths,
    rowsValue_eq_expandedPolynomialValue]
  norm_num [smul_smul, denominator]

/-- The actual defect is also the paper's complete 32-term right-nested polynomial. -/
theorem suzukiDefectSepticTerm_eq_nestedPolynomialValue (a b : A) (p : ℝ)
    (hp : BCH.IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    BCH.suzukiDefectSepticTerm a b p = nestedPolynomialValue ![a, b] p nestedDefectData := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [suzukiDefectSepticTerm_eq_expandedPolynomialValue a b p hp,
    expandedPolynomialValue_defect_eq]

end FQFP.SuzukiSepticCertificate
