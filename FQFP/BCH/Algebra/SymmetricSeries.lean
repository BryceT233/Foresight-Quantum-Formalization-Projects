/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.BinaryWordTable
public import FQFP.BCH.Algebra.ExponentialProduct
public import FQFP.BCH.Algebra.SymmetricTerms

/-!
# The finite symmetric BCH logarithm through degree eight

The homogeneous coefficients of three ordered exponential factors are combined by the
finite logarithm. Integer word certificates identify the cubic, quintic, and septic terms and
verify the cancellation of the even degrees.

## Main results

* `sum_logCoeff_positivePowerTrunc_eq_symmetric`: the finite logarithm is the linear, cubic,
  and quintic homogeneous terms.
* `sum_logCoeff_positivePowerTrunc_eq_symmetric_septic`: the finite logarithm through
  degree eight, including the septic correction.
-/

@[expose] public noncomputable section

open Finset Finset.Nat FQFP.WordTable

namespace FQFP.BCH

private lemma eval_flatMap_range {κ A : Type*} [Semiring A] [Algebra ℚ A]
    (scale : ℚ) (letters : κ → A) (f : ℕ → WordTable.Table κ) (m : ℕ) :
    eval scale letters ((List.range m).flatMap f) =
      ∑ i ∈ range m, eval scale letters (f i) := by
  induction m with
  | zero => simp [eval_nil]
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, eval_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, sum_range_succ, ih]

private def symmetricExpNumerator (n ij i : ℕ) : ℤ :=
  (420 ^ n / (i.factorial * (ij - i).factorial * (n - ij).factorial * 2 ^ (i + (n - ij))) : ℕ)

private def symmetricExpRow (n ij i : ℕ) : List (Fin 2) × ℤ :=
  (List.replicate i 0 ++ List.replicate (ij - i) 1 ++ List.replicate (n - ij) 0,
    symmetricExpNumerator n ij i)

private def symmetricExpRaw (n : ℕ) : WordTable.Table (Fin 2) :=
  (List.range (n + 1)).flatMap fun ij ↦
    (List.range (ij + 1)).flatMap fun i ↦ [symmetricExpRow n ij i]

private def symmetricExpCoeffCheck (n ij i : ℕ) : Bool :=
  ((symmetricExpNumerator n ij i : ℚ) / 420 ^ n) ==
    ((i.factorial : ℚ)⁻¹ * ((ij - i).factorial : ℚ)⁻¹ * ((n - ij).factorial : ℚ)⁻¹ *
      ((2 : ℚ)⁻¹) ^ i * ((2 : ℚ)⁻¹) ^ (n - ij))

private lemma symmetricExpCoeffCheck_all :
    (List.range 9).all (fun n ↦ (List.range (n + 1)).all fun ij ↦
      (List.range (ij + 1)).all (symmetricExpCoeffCheck n ij)) = true := by
  decide +kernel

private lemma symmetricExpRow_coeff (n ij i : ℕ) (hn : n ≤ 8)
    (hij : ij ≤ n) (hi : i ≤ ij) :
    ((symmetricExpNumerator n ij i : ℚ) / 420 ^ n) =
      ((i.factorial : ℚ)⁻¹ * ((ij - i).factorial : ℚ)⁻¹ * ((n - ij).factorial : ℚ)⁻¹ *
        ((2 : ℚ)⁻¹) ^ i * ((2 : ℚ)⁻¹) ^ (n - ij)) := by
  have h := List.all_eq_true.mp symmetricExpCoeffCheck_all n (List.mem_range.mpr (by lia))
  have h := List.all_eq_true.mp h ij (List.mem_range.mpr (by lia))
  have h := List.all_eq_true.mp h i (List.mem_range.mpr (by lia))
  simpa only [symmetricExpCoeffCheck, beq_iff_eq] using h

private lemma eval_symmetricExpRow {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) (n ij i : ℕ) (hn : n ≤ 8) (hij : ij ≤ n) (hi : i ≤ ij) :
    eval 420 ![a, b] [symmetricExpRow n ij i] =
      (((i.factorial : ℚ)⁻¹ * ((ij - i).factorial : ℚ)⁻¹) •
        (((2 : ℚ)⁻¹ • a) ^ i * b ^ (ij - i))) *
        (((n - ij).factorial : ℚ)⁻¹ • ((2 : ℚ)⁻¹ • a) ^ (n - ij)) := by
  rw [eval_singleton]
  simp only [symmetricExpRow, List.length_append, List.length_replicate, List.map_append,
    List.prod_append, List.map_replicate, List.prod_replicate, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_pow, smul_mul_smul_comm, smul_smul]
  rw [show i + (ij - i) + (n - ij) = n by lia, symmetricExpRow_coeff n ij i hn hij hi]
  simp only [smul_mul_assoc, smul_smul]
  congr 1
  ring

private lemma eval_symmetricExpRaw {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) (n : ℕ) (hn : n ≤ 8) :
    eval 420 ![a, b] (symmetricExpRaw n) =
      expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a) n := by
  rw [symmetricExpRaw, eval_flatMap_range, expMulMulTerm,
    sum_antidiagonal_eq_sum_range_succ_mk]
  apply sum_congr rfl
  intro ij hij
  rw [eval_flatMap_range, expMulTerm, sum_antidiagonal_eq_sum_range_succ_mk, sum_mul]
  apply sum_congr rfl
  intro i hi
  simpa only [smul_mul_smul_comm] using
    eval_symmetricExpRow a b n ij i hn (Nat.le_of_lt_succ (mem_range.mp hij))
      (Nat.le_of_lt_succ (mem_range.mp hi))

private def symmetricExpTable (n : ℕ) : WordTable.Table (Fin 2) :=
  BinaryWordTable.collapse (symmetricExpRaw n)

private lemma eval_symmetricExpTable {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) {n : ℕ} (hn : n ≤ 8) :
    eval 420 ![a, b] (symmetricExpTable n) =
      expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a) n := by
  rw [symmetricExpTable, BinaryWordTable.eval_collapse]
  exact eval_symmetricExpRaw a b n hn

private def symmetricPowerTable : ℕ → ℕ → WordTable.Table (Fin 2)
  | 0, n => if n = 0 then unit else []
  | k + 1, n => BinaryWordTable.collapse ((List.range (n - k)).flatMap fun i ↦
      mul (symmetricExpTable (i + 1)) (symmetricPowerTable k (n - (i + 1))))

private lemma eval_symmetricPowerTable {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) (k n : ℕ) (hn : n ≤ 8) :
    eval 420 ![a, b] (symmetricPowerTable k n) =
      positivePowerCoeff (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 0 <;> simp [symmetricPowerTable, positivePowerCoeff, h, eval_unit, eval_nil]
  | succ k ih =>
    rw [symmetricPowerTable, BinaryWordTable.eval_collapse, eval_flatMap_range, positivePowerCoeff]
    apply sum_congr rfl
    intro i hi
    rw [eval_mul, eval_symmetricExpTable a b (by
      have := mem_range.mp hi
      lia),
      ih _ (by lia)]

private def logarithmWeights : ℕ → ℤ
  | 0 => 0
  | 1 => 840
  | 2 => -420
  | 3 => 280
  | 4 => -210
  | 5 => 168
  | 6 => -140
  | 7 => 120
  | 8 => -105
  | _ => 0

private def symmetricLogTable (n : ℕ) : WordTable.Table (Fin 2) :=
  BinaryWordTable.collapse ((List.range 9).flatMap fun k ↦
    smul (logarithmWeights k) (symmetricPowerTable k n))

private lemma eval_symmetricLogTable {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) (n : ℕ) (hn : n ≤ 8) :
    eval 420 ![a, b] (symmetricLogTable n) =
      (840 : ℚ) • ∑ k ∈ range 9, logCoeff k •
        positivePowerCoeff (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n := by
  rw [symmetricLogTable, BinaryWordTable.eval_collapse, eval_flatMap_range, smul_sum]
  apply sum_congr rfl
  intro k hk
  rw [eval_smul, eval_symmetricPowerTable a b k n hn, smul_smul]
  have h : (logarithmWeights k : ℚ) = 840 * logCoeff k := by
    have hk9 := mem_range.mp hk
    interval_cases k <;> norm_num [logarithmWeights, logCoeff]
  rw [h]

private def symmetricTargetTable : ℕ → WordTable.Table (Fin 2)
  | 1 => [([0], 420), ([1], 420)]
  | 3 => smul 3087000
      [([0, 0, 1], -1), ([0, 1, 0], 2), ([1, 0, 0], -1),
        ([1, 1, 0], 2), ([1, 0, 1], -4), ([0, 1, 1], 2)]
  | 5 => smul 2268945000 symmetricBchQuinticTermTable
  | 7 => smul 2382392250000 symmetricBchSepticTermTable
  | _ => []

private lemma symmetric_coefficients_match (n : Fin 9) :
    BinaryWordTable.isZero (BinaryWordTable.collect
      (symmetricLogTable n ++ smul (-840) (symmetricTargetTable n))) = true := by
  fin_cases n <;> decide +kernel

private lemma symmetric_log_degree_eq_target {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) (n : Fin 9) :
    (∑ k ∈ range 9, logCoeff k •
      positivePowerCoeff (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n) =
      eval 420 ![a, b] (symmetricTargetTable n) := by
  have hz := BinaryWordTable.eval_table_eq_zero 420 (![a, b] : Fin 2 → A) _
    (symmetric_coefficients_match n)
  rw [eval_append, eval_smul, eval_symmetricLogTable a b n (by
    have := n.isLt
    lia)] at hz
  have heq : (840 : ℚ) •
      (∑ k ∈ range 9, logCoeff k •
        positivePowerCoeff (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k n) =
        (840 : ℚ) • eval 420 ![a, b] (symmetricTargetTable n) := by
    simpa only [Int.cast_neg, Int.cast_ofNat, neg_smul, add_neg_eq_zero] using hz
  exact (smul_right_injective A (by norm_num : (840 : ℚ) ≠ 0)) heq

private lemma eval_symmetricTargetTable_quintic {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) :
    eval 420 ![a, b] (symmetricTargetTable 5) = symmetricBchQuinticTerm a b := by
  rw [symmetricTargetTable, eval_smul,
    eval_of_length _ _ _ 5 symmetricBchQuinticTermTable_length]
  norm_num [symmetricBchQuinticTerm, smul_smul]

private lemma eval_symmetricTargetTable_septic {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) :
    eval 420 ![a, b] (symmetricTargetTable 7) = symmetricBchSepticTerm a b := by
  rw [symmetricTargetTable, eval_smul,
    eval_of_length _ _ _ 7 symmetricBchSepticTermTable_length]
  norm_num [symmetricBchSepticTerm, smul_smul]

private lemma eval_symmetricTargetTable_sum {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) :
    (∑ n ∈ range 7, eval 420 ![a, b] (symmetricTargetTable n)) =
      (a + b) + symmetricBchCubicTerm a b + symmetricBchQuinticTerm a b := by
  simp only [sum_range_succ, sum_range_zero]
  rw [eval_symmetricTargetTable_quintic]
  norm_num [symmetricTargetTable, eval_smul, WordTable.smul, eval,
    symmetricBchCubicTerm, mul_sub, sub_mul, mul_assoc]
  module

private lemma sum_logCoeff_positivePowerTrunc_eq_sum_target
    {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) (m : ℕ) (hm : m ≤ 9) :
    (∑ k ∈ range m, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k m) =
      ∑ n ∈ range m, eval 420 ![a, b] (symmetricTargetTable n) := by
  simp only [positivePowerTrunc_eq_sum_coeff, smul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← symmetric_log_degree_eq_target a b ⟨n, lt_of_lt_of_le (mem_range.mp hn) hm⟩]
  apply sum_subset (range_mono hm)
  intro k _ hk
  have hmk : m ≤ k := Nat.le_of_not_gt (fun h ↦ hk (mem_range.mpr h))
  rw [positivePowerCoeff_eq_zero_of_lt _ k n
    (lt_of_lt_of_le (mem_range.mp hn) hmk), smul_zero]

/-- **Symmetric BCH through degree six**: all even homogeneous corrections vanish,
leaving exactly the linear, cubic, and quintic terms. -/
theorem sum_logCoeff_positivePowerTrunc_eq_symmetric {A : Type*} [Ring A] [Algebra ℚ A]
    (a b : A) :
    (∑ k ∈ range 7, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k 7) =
      (a + b) + symmetricBchCubicTerm a b + symmetricBchQuinticTerm a b := by
  rw [sum_logCoeff_positivePowerTrunc_eq_sum_target a b 7 (by decide)]
  exact eval_symmetricTargetTable_sum a b

/-- **Symmetric BCH through degree eight**: the even homogeneous corrections vanish,
leaving the linear, cubic, quintic, and septic terms. -/
theorem sum_logCoeff_positivePowerTrunc_eq_symmetric_septic
    {A : Type*} [Ring A] [Algebra ℚ A] (a b : A) :
    (∑ k ∈ range 9, logCoeff k •
      positivePowerTrunc (expMulMulTerm ((2 : ℚ)⁻¹ • a) b ((2 : ℚ)⁻¹ • a)) k 9) =
      (a + b) + symmetricBchCubicTerm a b + symmetricBchQuinticTerm a b +
        symmetricBchSepticTerm a b := by
  rw [sum_logCoeff_positivePowerTrunc_eq_sum_target a b 9 le_rfl,
    sum_range_succ, sum_range_succ, eval_symmetricTargetTable_sum,
    eval_symmetricTargetTable_septic]
  simp [symmetricTargetTable, eval_nil]

end FQFP.BCH
