/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.Algebra.Word.Table

/-!
# Integer word table boundary regressions

Run with `lake env lean FQFPTest/WordTable.lean` after building `FQFP`.
The examples check scale zero, empty words, noncommutative multiplication order,
first-occurrence collection order, and retained zero coefficients.
-/

open FQFP FQFP.WordTable

section Evaluation

variable {κ A : Type*} [Semiring A] [Algebra ℚ A] (letters : κ → A)

-- At scale zero the empty table is zero, but the empty word still contributes.
example : eval 0 letters ([] : Table κ) = 0 := eval_nil 0 letters

example (c : ℤ) : eval 0 letters [([], c)] = (c : ℚ) • (1 : A) := by
  simp [eval_singleton]

example : eval 0 letters unit = 1 := eval_unit 0 letters

example : eval 0 letters (pow ([] : Table κ) 0) = 1 := by
  rw [eval_pow, pow_zero]

-- Every nonempty word vanishes at scale zero, regardless of its coefficient.
example (w : List κ) (hw : w ≠ []) (c : ℤ) : eval 0 letters [(w, c)] = 0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons k w => simp [eval_singleton]

-- The bridge is available at zero without a nonzero-scale assumption.
example (t : Table κ) : eval 0 letters t =
    CoeffWordTable.eval (Int.castRingHom ℚ) (fun _ ↦ (0 : A)) t := by
  simpa only [inv_zero, zero_smul] using eval_eq_coeffWordTable 0 letters t

end Evaluation

-- The result retains left-to-right letter order over an arbitrary semiring.
example {A : Type*} [Semiring A] [Algebra ℚ A] (letters : Bool → A) :
    eval 2 letters (mul [([false], 2)] [([true], 2)]) = letters false * letters true := by
  rw [eval_mul]
  norm_num [eval_singleton]

-- Cancellations keep zero rows in the order of the first occurrences.
example : collapse [([false], 3), ([true], 5), ([false], -3), ([], 0), ([true], -5)] =
    [([false], 0), ([true], 0), ([], 0)] := by decide

example : CoeffWordTable.collapse
    ([([false], 3), ([true], 5), ([false], -3), ([], 0), ([true], -5)] : Table Bool) =
    [([false], 0), ([true], 0), ([], 0)] := by decide

-- Insertion merges only the first matching row of an existing accumulator.
example : addRow ([false], -2) [([true], 0), ([false], 2), ([false], 9)] =
    [([true], 0), ([false], 0), ([false], 9)] := by decide

-- Empty-word cancellation also retains its zero coefficient.
example : collapse ([([], 4), ([], -4)] : Table Bool) = [([], 0)] := by decide

-- Evaluation is unchanged after collecting a mixture of empty and nonempty words at zero.
example {A : Type*} [Semiring A] [Algebra ℚ A] (letters : Bool → A) :
    eval 0 letters (collapse [([false], 3), ([], 4), ([false], -3), ([], -1)]) =
      (3 : ℚ) • (1 : A) := by
  rw [eval_collapse]
  norm_num [eval_cons, eval_nil]
  rw [← add_smul]
  norm_num

open Lean in
-- Check exported compatibility equations without triggering lazy equation generation.
run_meta do
  let env ← getEnv
  for n in [`FQFP.WordTable.unit.eq_1, `FQFP.WordTable.collapse.eq_1] do
    unless env.contains n do
      throwError "Missing exported equation {n}"
