/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.ExponentialList
public import FQFP.BCH.Algebra.CentralBinaryWordTable
public import FQFP.BCH.Palindromic
public import FQFP.BCH.SuzukiTerms
public import FQFP.BCH.SuzukiParameter

/-!
# Quintic Suzuki coefficient matching

Finite ordered exponential coefficients and their logarithm are represented by
integer word tables with explicit denominators. A central letter records the real parameter;
the other two letters retain their order. Integer quotient certificates identify
the linear and quintic coefficients modulo the Suzuki cubic relation.

The ordinary letters are evaluated at `a/120` and `b/120`. Integer exponential
weights `60^i/i!` and logarithm weights `60 * logCoeff i` clear all denominators
through degree five. The quotient tables use the same letter scale.

## Main results

* `sum_expListLogCoeff_suzuki5_eq`: the finite logarithm through degree five.
-/

@[expose] public noncomputable section

open Finset Finset.Nat

namespace FQFP.BCH

private abbrev ParamTable := CoeffWordTable.Table ℤ (Option (Fin 2))

private def argumentTables : List ParamTable :=
  [[([none, some 0], 1)], [([none, some 1], 2)],
    [([none, some 0], 2)], [([none, some 1], 2)],
    [([some 0], 1), ([none, some 0], -3)],
    [([some 1], 2), ([none, some 1], -8)],
    [([some 0], 1), ([none, some 0], -3)],
    [([none, some 1], 2)], [([none, some 0], 2)],
    [([none, some 1], 2)], [([none, some 0], 1)]]

private def tablePow (t : ParamTable) : ℕ → ParamTable
  | 0 => CoeffWordTable.unit
  | n + 1 => CentralBinaryWordTable.collect (CoeffWordTable.mul t (tablePow t n))

private def tableExp : List ParamTable → ℕ → ParamTable
  | [], n => if n = 0 then CoeffWordTable.unit else []
  | t :: ts, n => CentralBinaryWordTable.collect ((List.range (n + 1)).flatMap fun i ↦
      CoeffWordTable.smul (60 ^ i / Nat.factorial i : ℕ)
        (CoeffWordTable.mul (tablePow t i) (tableExp ts (n - i))))

private def tablePower : ℕ → ℕ → ParamTable
  | 0, n => if n = 0 then CoeffWordTable.unit else []
  | k + 1, n => CentralBinaryWordTable.collect ((List.range (n - k)).flatMap fun i ↦
      CoeffWordTable.mul (tableExp argumentTables (i + 1)) (tablePower k (n - (i + 1))))

private def logWeights : ℕ → ℤ
  | 1 => 60
  | 2 => -30
  | 3 => 20
  | 4 => -15
  | 5 => 12
  | _ => 0

private def tableLog (n : ℕ) : ParamTable :=
  CentralBinaryWordTable.collect ((List.range (n + 1)).flatMap fun k ↦
    CoeffWordTable.smul (logWeights k) (tablePower k n))

private def tableBracket (s t : ParamTable) : ParamTable :=
  CentralBinaryWordTable.collect (CoeffWordTable.mul s t ++
    CoeffWordTable.smul (-1) (CoeffWordTable.mul t s))

private def childsTables : Fin 8 → ParamTable := fun i ↦
  let a : ParamTable := [([some 0], 1)]
  let b : ParamTable := [([some 1], 1)]
  let x := if i.val < 4 then a else b
  let y := if i.val % 4 < 2 then a else b
  let z := if i.val % 2 = 0 then a else b
  tableBracket x (tableBracket y (tableBracket z (tableBracket b a)))

private def betaTables : Fin 8 → ParamTable :=
  ![[
    ([], -1036800),
    ([none], 8985600),
    ([none, none], 21945600)],
    [
    ([], -6220800),
    ([none], 53913600),
    ([none, none], 2073600)],
    [],
    [
    ([], -12441600),
    ([none], 107827200),
    ([none, none], -168652800)],
    [
    ([], 2073600),
    ([none], -17971200),
    ([none, none], 85708800)],
    [
    ([], 6220800),
    ([none], -53913600),
    ([none, none], 257126400)],
    [],
    [
    ([], -4147200),
    ([none], 35942400),
    ([none, none], 1382400)]]

private def targetTable : ℕ → ParamTable
  | 1 => [([some 0], 120), ([some 1], 120)]
  | 5 => CentralBinaryWordTable.collect ((List.finRange 8).flatMap fun i ↦
      CoeffWordTable.mul (betaTables i) (childsTables i))
  | _ => []

private def relationTable : ParamTable :=
  [([], 1), ([none], -12), ([none, none], 48), ([none, none, none], -60)]

/-- Integral quotient witnesses for the Suzuki relation at letter scale `120`. -/
private def suzukiQuotientTable : ℕ → ParamTable
  | 3 => [
    ([some 0, some 0, some 1], -72000),
    ([some 0, some 1, some 0], 144000),
    ([some 0, some 1, some 1], 144000),
    ([some 1, some 0, some 0], -72000),
    ([some 1, some 0, some 1], -288000),
    ([some 1, some 1, some 0], 144000)]
  | 5 => [
    ([some 0, some 0, some 0, some 0, some 1], 29203200),
    ([some 0, some 0, some 0, some 1, some 0], -116812800),
    ([some 0, some 0, some 0, some 1, some 1], -116812800),
    ([some 0, some 0, some 1, some 0, some 0], 175219200),
    ([some 0, some 0, some 1, some 0, some 1], 304819200),
    ([some 0, some 0, some 1, some 1, some 0], 45619200),
    ([some 0, some 0, some 1, some 1, some 1], 132019200),
    ([some 0, some 1, some 0, some 0, some 0], -116812800),
    ([some 0, some 1, some 0, some 0, some 1], -213580800),
    ([some 0, some 1, some 0, some 1, some 0], -182476800),
    ([some 0, some 1, some 0, some 1, some 1], -182476800),
    ([some 0, some 1, some 1, some 0, some 0], 45619200),
    ([some 0, some 1, some 1, some 0, some 1], -244684800),
    ([some 0, some 1, some 1, some 1, some 0], 163123200),
    ([some 0, some 1, some 1, some 1, some 1], -30412800),
    ([some 1, some 0, some 0, some 0, some 0], 29203200),
    ([some 1, some 0, some 0, some 0, some 1], 142387200),
    ([some 1, some 0, some 0, some 1, some 0], -213580800),
    ([some 1, some 0, some 0, some 1, some 1], -213580800),
    ([some 1, some 0, some 1, some 0, some 0], 304819200),
    ([some 1, some 0, some 1, some 0, some 1], 854323200),
    ([some 1, some 0, some 1, some 1, some 0], -244684800),
    ([some 1, some 0, some 1, some 1, some 1], 121651200),
    ([some 1, some 1, some 0, some 0, some 0], -116812800),
    ([some 1, some 1, some 0, some 0, some 1], -213580800),
    ([some 1, some 1, some 0, some 1, some 0], -182476800),
    ([some 1, some 1, some 0, some 1, some 1], -182476800),
    ([some 1, some 1, some 1, some 0, some 0], 132019200),
    ([some 1, some 1, some 1, some 0, some 1], 121651200),
    ([some 1, some 1, some 1, some 1, some 0], -30412800),
    ([none, some 0, some 0, some 0, some 0, some 1], 100224000),
    ([none, some 0, some 0, some 0, some 1, some 0], -400896000),
    ([none, some 0, some 0, some 0, some 1, some 1], -400896000),
    ([none, some 0, some 0, some 1, some 0, some 0], 601344000),
    ([none, some 0, some 0, some 1, some 0, some 1], 601344000),
    ([none, some 0, some 0, some 1, some 1, some 0], 601344000),
    ([none, some 0, some 0, some 1, some 1, some 1], 601344000),
    ([none, some 0, some 1, some 0, some 0, some 0], -400896000),
    ([none, some 0, some 1, some 0, some 0, some 1], 601344000),
    ([none, some 0, some 1, some 0, some 1, some 0], -2405376000),
    ([none, some 0, some 1, some 0, some 1, some 1], -2405376000),
    ([none, some 0, some 1, some 1, some 0, some 0], 601344000),
    ([none, some 0, some 1, some 1, some 0, some 1], 3608064000),
    ([none, some 0, some 1, some 1, some 1, some 0], -2405376000),
    ([none, some 0, some 1, some 1, some 1, some 1], -400896000),
    ([none, some 1, some 0, some 0, some 0, some 0], 100224000),
    ([none, some 1, some 0, some 0, some 0, some 1], -400896000),
    ([none, some 1, some 0, some 0, some 1, some 0], 601344000),
    ([none, some 1, some 0, some 0, some 1, some 1], 601344000),
    ([none, some 1, some 0, some 1, some 0, some 0], 601344000),
    ([none, some 1, some 0, some 1, some 0, some 1], -2405376000),
    ([none, some 1, some 0, some 1, some 1, some 0], 3608064000),
    ([none, some 1, some 0, some 1, some 1, some 1], 1603584000),
    ([none, some 1, some 1, some 0, some 0, some 0], -400896000),
    ([none, some 1, some 1, some 0, some 0, some 1], 601344000),
    ([none, some 1, some 1, some 0, some 1, some 0], -2405376000),
    ([none, some 1, some 1, some 0, some 1, some 1], -2405376000),
    ([none, some 1, some 1, some 1, some 0, some 0], 601344000),
    ([none, some 1, some 1, some 1, some 0, some 1], 1603584000),
    ([none, some 1, some 1, some 1, some 1, some 0], -400896000),
    ([none, none, some 0, some 0, some 0, some 0, some 1], -177120000),
    ([none, none, some 0, some 0, some 0, some 1, some 0], 708480000),
    ([none, none, some 0, some 0, some 0, some 1, some 1], 708480000),
    ([none, none, some 0, some 0, some 1, some 0, some 0], -1062720000),
    ([none, none, some 0, some 0, some 1, some 0, some 1], -933120000),
    ([none, none, some 0, some 0, some 1, some 1, some 0], -1192320000),
    ([none, none, some 0, some 0, some 1, some 1, some 1], -1105920000),
    ([none, none, some 0, some 1, some 0, some 0, some 0], 708480000),
    ([none, none, some 0, some 1, some 0, some 0, some 1], -1451520000),
    ([none, none, some 0, some 1, some 0, some 1, some 0], 4769280000),
    ([none, none, some 0, some 1, some 0, some 1, some 1], 4769280000),
    ([none, none, some 0, some 1, some 1, some 0, some 0], -1192320000),
    ([none, none, some 0, some 1, some 1, some 0, some 1], -7672320000),
    ([none, none, some 0, some 1, some 1, some 1, some 0], 5114880000),
    ([none, none, some 0, some 1, some 1, some 1, some 1], 794880000),
    ([none, none, some 1, some 0, some 0, some 0, some 0], -177120000),
    ([none, none, some 1, some 0, some 0, some 0, some 1], 967680000),
    ([none, none, some 1, some 0, some 0, some 1, some 0], -1451520000),
    ([none, none, some 1, some 0, some 0, some 1, some 1], -1451520000),
    ([none, none, some 1, some 0, some 1, some 0, some 0], -933120000),
    ([none, none, some 1, some 0, some 1, some 0, some 1], 5806080000),
    ([none, none, some 1, some 0, some 1, some 1, some 0], -7672320000),
    ([none, none, some 1, some 0, some 1, some 1, some 1], -3179520000),
    ([none, none, some 1, some 1, some 0, some 0, some 0], 708480000),
    ([none, none, some 1, some 1, some 0, some 0, some 1], -1451520000),
    ([none, none, some 1, some 1, some 0, some 1, some 0], 4769280000),
    ([none, none, some 1, some 1, some 0, some 1, some 1], 4769280000),
    ([none, none, some 1, some 1, some 1, some 0, some 0], -1105920000),
    ([none, none, some 1, some 1, some 1, some 0, some 1], -3179520000),
    ([none, none, some 1, some 1, some 1, some 1, some 0], 794880000)]
  | _ => []

private def residualTable (n : ℕ) : ParamTable :=
  CentralBinaryWordTable.collect (tableLog n ++ CoeffWordTable.smul (-60) (targetTable n) ++
    CoeffWordTable.smul (-60) (CoeffWordTable.mul relationTable (suzukiQuotientTable n)))

private lemma coefficients_match (n : Fin 6) :
    (residualTable n).all (fun row ↦ row.2 == 0) = true := by
  fin_cases n <;> decide +kernel

section Semantics

variable {A : Type*} [Ring A] [Algebra ℝ A]

private def parameterLetters (a b : A) (p : ℝ) : Option (Fin 2) → A :=
  fun x ↦ match x with
      | none => p • 1
      | some i => (120 : ℝ)⁻¹ • (![a, b] : Fin 2 → A) i

variable (a b : A) (p : ℝ)

local notation "E" => CoeffWordTable.eval (Int.castRingHom ℝ) (parameterLetters a b p)

private lemma eval_collect (t : ParamTable) :
    E (CentralBinaryWordTable.collect t) = E t := by
  convert CentralBinaryWordTable.eval_collect (Int.castRingHom ℝ) p
    (fun i ↦ (120 : ℝ)⁻¹ • (![a, b] : Fin 2 → A) i) t using 2 <;>
    funext x <;> cases x <;> rfl

private lemma eval_tablePow (t : ParamTable) (n : ℕ) :
    E (tablePow t n) = E t ^ n := by
  induction n with
  | zero => simp [tablePow, CoeffWordTable.eval_unit]
  | succ n ih =>
      rw [tablePow, eval_collect, CoeffWordTable.eval_mul, ih, pow_succ']

private lemma eval_argumentTables :
    (argumentTables.map fun t ↦ (60 : ℝ) • E t) =
      suzuki5Arguments a b p 1 := by
  norm_num [argumentTables, parameterLetters, CoeffWordTable.eval, suzuki5Arguments,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  repeat' constructor
  all_goals module

private lemma eval_tableBracket (s t : ParamTable) :
    E (tableBracket s t) =
      E s * E t - E t * E s := by
  rw [tableBracket, eval_collect, CoeffWordTable.eval_append,
    CoeffWordTable.eval_mul, CoeffWordTable.eval_smul,
    CoeffWordTable.eval_mul]
  rw [map_neg, map_one, neg_one_smul, sub_eq_add_neg]

private lemma eval_childsTables (i : Fin 8) :
    E (childsTables i) =
      childsComm ((120 : ℝ)⁻¹ • a) ((120 : ℝ)⁻¹ • b) i := by
  fin_cases i <;> dsimp [childsTables]
  all_goals
    simp only [eval_tableBracket, CoeffWordTable.eval_singleton, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, map_one, one_smul, parameterLetters,
      Matrix.cons_val_zero, Matrix.cons_val_one, Ring.lie_def]

private lemma eval_betaTables (i : Fin 8) :
    E (betaTables i) =
      ((120 : ℝ) ^ 5 * suzukiQuinticCoeff p i) • (1 : A) := by
  fin_cases i <;>
    norm_num [betaTables, suzukiQuinticCoeff, parameterLetters, CoeffWordTable.eval,
      smul_mul_assoc, smul_smul]
  all_goals module

private lemma childsComm_smul (a b : A) (c : ℝ) (i : Fin 8) :
    childsComm (c • a) (c • b) i = c ^ 5 • childsComm a b i := by
  have hbracket (x y : A) (r s : ℝ) :
      (r • x) * (s • y) - (s • y) * (r • x) = (r * s) • (x * y - y * x) := by
    simp only [smul_mul_smul_comm, smul_sub]
    rw [mul_comm s r]
  unfold childsComm
  split <;> simp only [Ring.lie_def, hbracket] <;> congr 1 <;> ring

private lemma eval_targetTable_five :
    E (targetTable 5) = suzukiQuinticTerm a b p := by
  rw [targetTable, eval_collect, CoeffWordTable.eval_flatMap]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  unfold suzukiQuinticTerm
  apply sum_congr rfl
  intro i hi
  rw [CoeffWordTable.eval_mul, eval_betaTables, eval_childsTables, childsComm_smul,
    smul_mul_smul_comm, one_mul]
  congr 1
  norm_num
  ring

private lemma eval_relationTable :
    E relationTable = suzukiCubicCoeff p • (1 : A) := by
  norm_num [relationTable, parameterLetters, CoeffWordTable.eval, suzukiCubicCoeff,
    smul_mul_assoc, smul_smul]
  module

variable [Algebra ℚ A] [IsScalarTower ℚ ℝ A]

private lemma eval_tableExp (ts : List ParamTable) (n : ℕ) :
    n ≤ 5 → E (tableExp ts n) =
      expListTerm (ts.map fun t ↦ (60 : ℝ) • E t) n := by
  induction ts generalizing n with
  | nil =>
      intro hn
      by_cases h : n = 0 <;>
        simp [tableExp, expListTerm, h, CoeffWordTable.eval_unit,
          CoeffWordTable.eval_nil]
  | cons t ts ih =>
      intro hn
      rw [tableExp, eval_collect, CoeffWordTable.eval_flatMap_range,
        List.map_cons, expListTerm, sum_antidiagonal_eq_sum_range_succ_mk]
      apply sum_congr rfl
      intro i hi
      rw [CoeffWordTable.eval_smul, CoeffWordTable.eval_mul, eval_tablePow,
        ih _ (by lia)]
      simp only [← Rat.cast_smul_eq_qsmul ℝ,
        smul_pow, smul_mul_assoc, smul_smul]
      have hi5 : i ≤ 5 := by
        have := mem_range.mp hi
        lia
      interval_cases i <;> norm_num [Nat.factorial]

private lemma eval_tablePower (k n : ℕ) (hn : n ≤ 5) :
    E (tablePower k n) =
      positivePowerCoeff (expListTerm (suzuki5Arguments a b p 1)) k n := by
  induction k generalizing n with
  | zero => by_cases h : n = 0 <;>
      simp [tablePower, positivePowerCoeff, h, CoeffWordTable.eval_unit,
        CoeffWordTable.eval_nil]
  | succ k ih =>
      rw [tablePower, eval_collect, CoeffWordTable.eval_flatMap_range, positivePowerCoeff]
      apply sum_congr rfl
      intro i hi
      rw [CoeffWordTable.eval_mul, eval_tableExp a b p argumentTables (i + 1) (by
        have := mem_range.mp hi
        lia), eval_argumentTables, ih _ (by lia)]

private lemma eval_tableLog (n : ℕ) (hn : n ≤ 5) :
    E (tableLog n) =
      (60 : ℝ) • expListLogCoeff (suzuki5Arguments a b p 1) n := by
  rw [tableLog, eval_collect, expListLogCoeff, smul_sum, CoeffWordTable.eval_flatMap_range]
  apply sum_congr rfl
  intro k hk
  rw [CoeffWordTable.eval_smul, eval_tablePower a b p k n hn]
  have hk5 : k ≤ 5 := by
    have := mem_range.mp hk
    lia
  simp only [← Rat.cast_smul_eq_qsmul ℝ, smul_smul]
  interval_cases k <;> norm_num [logWeights, logCoeff]

private lemma log_coefficient_eq_target (hp : IsSuzukiCubic p) (n : Fin 6) :
    expListLogCoeff (suzuki5Arguments a b p 1) n = E (targetTable n) := by
  have hz := CoeffWordTable.eval_eq_zero_of_all (Int.castRingHom ℝ)
    (parameterLetters a b p) (residualTable n) (coefficients_match n)
  rw [residualTable, eval_collect, CoeffWordTable.eval_append, CoeffWordTable.eval_append,
    CoeffWordTable.eval_smul, CoeffWordTable.eval_smul, CoeffWordTable.eval_mul,
    eval_tableLog a b p n (by
      have := n.isLt
      lia), eval_relationTable] at hz
  change suzukiCubicCoeff p = 0 at hp
  rw [hp, zero_smul, zero_mul, smul_zero, add_zero] at hz
  norm_num only [map_neg, map_ofNat, neg_smul] at hz
  have heq : (60 : ℝ) • expListLogCoeff (suzuki5Arguments a b p 1) n =
      (60 : ℝ) • E (targetTable n) := by
    simpa only [add_neg_eq_zero] using hz
  exact (smul_right_injective A (by norm_num : (60 : ℝ) ≠ 0)) heq

end Semantics

private lemma suzuki5Arguments_smul {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (p t : ℝ) :
    suzuki5Arguments a b p t = (suzuki5Arguments a b p 1).map (fun x ↦ t • x) := by
  simp [suzuki5Arguments, smul_smul, mul_comm]

/-- **Quintic Suzuki matching**: cubic cancellation leaves the linear term and the
source Childs quintic polynomial through degree five. -/
theorem sum_expListLogCoeff_suzuki5_eq {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (p t : ℝ) (hp : IsSuzukiCubic p) :
    letI : Algebra ℚ A := .restrictScalars ℚ ℝ A
    (∑ d ∈ range 6, expListLogCoeff (suzuki5Arguments a b p t) d) =
      t • (a + b) + t ^ 5 • suzukiQuinticTerm a b p := by
  let : Algebra ℚ A := .restrictScalars ℚ ℝ A
  rw [suzuki5Arguments_smul]
  simp only [expListLogCoeff_smul]
  calc
    _ = ∑ d ∈ range 6, t ^ d •
        CoeffWordTable.eval (Int.castRingHom ℝ) (parameterLetters a b p) (targetTable d) := by
      apply sum_congr rfl
      intro d hd
      rw [log_coefficient_eq_target a b p hp ⟨d, mem_range.mp hd⟩]
    _ = _ := by
      simp only [sum_range_succ, sum_range_zero]
      rw [eval_targetTable_five]
      norm_num [targetTable, parameterLetters, CoeffWordTable.eval, smul_smul]

end FQFP.BCH
