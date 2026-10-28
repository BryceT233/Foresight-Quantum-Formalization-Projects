/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.Table.Defs
public import FQFP.Algebra.Word.CoeffTable

/-!
# Integer tables as general coefficient tables

The integer operations agree with the integer specialization of coefficient tables
as lists, including their collection order and retained zero coefficients.
Scaled evaluation is general coefficient evaluation on inversely scaled letters.
No nonzero-scale hypothesis is needed, even for the empty word.
-/

@[expose] public section

namespace FQFP.WordTable

/-- The two unit tables are the same list. -/
lemma unit_eq_coeffWordTable {κ : Type*} :
    (unit : Table κ) = CoeffWordTable.unit (R := ℤ) := by
  simp only [unit, CoeffWordTable.unit]

/-- Integer table multiplication is the specialization of coefficient multiplication. -/
lemma mul_eq_coeffWordTable {κ : Type*} (s t : Table κ) :
    mul s t = CoeffWordTable.mul s t := rfl

/-- Integer coefficient scaling agrees in both representations. -/
lemma smul_eq_coeffWordTable {κ : Type*} (c : ℤ) (t : Table κ) :
    smul c t = CoeffWordTable.smul c t := rfl

/-- Row insertion agrees as a list, including the position and value of a merged row. -/
lemma addRow_eq_coeffWordTable {κ : Type*} [DecidableEq κ] (p : List κ × ℤ) (t : Table κ) :
    addRow p t = CoeffWordTable.addRow p t := by
  induction t with
  | nil => rfl
  | cons q t ih => simp only [addRow, CoeffWordTable.addRow, ih]

/-- Collection into an accumulator agrees as a list, not just after evaluation. -/
lemma collapseAux_eq_coeffWordTable {κ : Type*} [DecidableEq κ] (t acc : Table κ) :
    collapseAux t acc = CoeffWordTable.collapseAux t acc := by
  induction t generalizing acc with
  | nil => rfl
  | cons p t ih =>
      simp only [collapseAux, CoeffWordTable.collapseAux, addRow_eq_coeffWordTable, ih]

/-- Collection preserves the same row order and zero coefficients in both representations. -/
lemma collapse_eq_coeffWordTable {κ : Type*} [DecidableEq κ] (t : Table κ) :
    collapse t = CoeffWordTable.collapse t := by
  simpa only [collapse, CoeffWordTable.collapse] using collapseAux_eq_coeffWordTable t []

variable {κ A : Type*} [Semiring A] [Algebra ℚ A]

/-- Scaling each letter incorporates its word-length denominator, also at scale zero. -/
lemma smul_prod_scaled_letters (scale : ℚ) (letters : κ → A) (w : List κ) (c : ℤ) :
    (c : ℚ) • (w.map fun k ↦ scale⁻¹ • letters k).prod =
      ((c : ℚ) / scale ^ w.length) • (w.map letters).prod := by
  rw [prod_map_smul, smul_smul, div_eq_mul_inv, inv_pow]

/-- Scaled integer evaluation is coefficient evaluation on inversely scaled letters. -/
lemma eval_eq_coeffWordTable (scale : ℚ) (letters : κ → A) (t : Table κ) :
    eval scale letters t =
      CoeffWordTable.eval (Int.castRingHom ℚ) (fun k ↦ scale⁻¹ • letters k) t := by
  simp only [eval, CoeffWordTable.eval]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact (smul_prod_scaled_letters scale letters p.1 p.2).symm

/-- At scale one, both evaluations use the same letter assignment. -/
lemma eval_one_eq_coeffWordTable (letters : κ → A) (t : Table κ) :
    eval 1 letters t = CoeffWordTable.eval (Int.castRingHom ℚ) letters t := by
  simpa only [inv_one, one_smul] using eval_eq_coeffWordTable 1 letters t

end FQFP.WordTable
