/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.BCH.Algebra.Word
public import FQFP.BCH.Algebra.WordTable

/-!
# Finite Taylor expansions of ordered word tables

Subsets record the positions at which a chosen letter receives a perturbation. Grouping by
their cardinality gives homogeneous Taylor pieces without changing the multiplication order.
The table interfaces keep each word paired with its coefficient and its rational scale.

## Main definitions

* `FQFP.wordTaylorPiece`: a word with a prescribed number of perturbation positions.
* `FQFP.wordLinDiffShift`: change of the linear piece when its base letter is shifted.
* `FQFP.WordTable.taylorPiece`, `FQFP.WordTable.linDiffShift`: the weighted table versions.

## Main results

* `FQFP.word_update_add_eq_sum_taylorPiece`: expansion of a word.
* `FQFP.WordTable.eval_update_add_eq_sum_taylorPiece`: expansion of a whole table.
* `FQFP.WordTable.taylorPiece_one_update_add`: expansion of the shifted linear piece.
-/

@[expose] public noncomputable section

open Finset

namespace FQFP

variable {κ A : Type*} [DecidableEq κ] [Semiring A]

/-- The part of a word with exactly `k` occurrences of the chosen letter replaced by `V`. -/
def wordTaylorPiece {n : ℕ} (w : Fin n → κ) (a : κ) (letters : κ → A) (V : A) (k : ℕ) : A :=
  ∑ s ∈ (wordPositions w a).powersetCard k,
    (List.ofFn (s.piecewise (fun _ ↦ V) (fun i ↦ letters (w i)))).prod

/-- The unperturbed Taylor piece is the original ordered word. -/
lemma wordTaylorPiece_zero {n : ℕ} (w : Fin n → κ) (a : κ) (letters : κ → A) (V : A) :
    wordTaylorPiece w a letters V 0 = wordEval letters w := by
  simp only [wordTaylorPiece, powersetCard_zero, sum_singleton, piecewise_empty,
    wordEval, List.map_ofFn, Function.comp_def]

/-- Expand a word up to any upper bound on the number of occurrences of the chosen letter. -/
theorem word_update_add_eq_sum_taylorPiece {n r : ℕ} (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V : A) (hcard : (wordPositions w a).card ≤ r) :
    wordEval (Function.update letters a (letters a + V)) w =
      ∑ k ∈ range (r + 1), wordTaylorPiece w a letters V k := by
  rw [wordEval, List.map_ofFn]
  exact (prod_word_update_add w letters a V).trans
    (sum_powerset_eq_sum_powersetCard_of_card_le hcard _)

/-- A linear word piece is the sum over its single distinguished perturbation position. -/
lemma wordTaylorPiece_one {n : ℕ} (w : Fin n → κ) (a : κ) (letters : κ → A) (W : A) :
    wordTaylorPiece w a letters W 1 =
      ∑ i ∈ wordPositions w a,
        (List.ofFn (({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
          (fun j ↦ letters (w j)))).prod := by
  simp [wordTaylorPiece, powersetCard_one]

/-- The linear word piece is additive in its perturbation. -/
lemma wordTaylorPiece_one_add {n : ℕ} (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V W : A) :
    wordTaylorPiece w a letters (V + W) 1 =
      wordTaylorPiece w a letters V 1 + wordTaylorPiece w a letters W 1 := by
  simp only [wordTaylorPiece_one, piecewise_singleton, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  exact (MultilinearMap.mkPiAlgebraFin ℕ n A).map_update_add (fun j ↦ letters (w j)) i V W

/-- The linear word piece respects scalar multiplication. -/
lemma wordTaylorPiece_one_smul {R : Type*} [CommSemiring R] [Algebra R A]
    {n : ℕ} (w : Fin n → κ) (a : κ) (letters : κ → A) (c : R) (V : A) :
    wordTaylorPiece w a letters (c • V) 1 = c • wordTaylorPiece w a letters V 1 := by
  simp only [wordTaylorPiece_one, piecewise_singleton, smul_sum]
  apply sum_congr rfl
  intro i _
  exact (MultilinearMap.mkPiAlgebraFin R n A).map_update_smul (fun j ↦ letters (w j)) i c V

/-- No word piece exists above the number of occurrences of the perturbed letter. -/
lemma wordTaylorPiece_eq_zero_of_card_lt {n k : ℕ} (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V : A) (hk : (wordPositions w a).card < k) :
    wordTaylorPiece w a letters V k = 0 := by
  simp only [wordTaylorPiece, powersetCard_eq_empty.mpr hk, sum_empty]

/-- A positive-degree word component vanishes at a zero perturbation. -/
lemma wordTaylorPiece_zero_direction {n k : ℕ} (w : Fin n → κ) (a : κ)
    (letters : κ → A) (hk : 0 < k) : wordTaylorPiece w a letters 0 k = 0 := by
  apply sum_eq_zero
  intro s hs
  have hsne : s.Nonempty := card_pos.mp (by simpa only [(mem_powersetCard.mp hs).2] using hk)
  obtain ⟨i, hi⟩ := hsne
  exact (MultilinearMap.mkPiAlgebraFin ℕ n A).map_coord_zero i (by simp [hi])

/-- Words with exactly one `W` and a nonempty set of additional perturbation positions `V`. -/
def wordLinDiffShift {n : ℕ} (w : Fin n → κ) (a : κ) (letters : κ → A) (V W : A) : A :=
  ∑ i ∈ wordPositions w a,
    ∑ s ∈ ((wordPositions w a).erase i).powerset.erase ∅,
      (List.ofFn (({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
        (s.piecewise (fun _ ↦ V) (fun j ↦ letters (w j))))).prod

/-- Shifting the base of a linear word piece inserts a nonempty set of additional positions. -/
theorem wordTaylorPiece_one_update_add {n : ℕ} (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V W : A) :
    wordTaylorPiece w a (Function.update letters a (letters a + V)) W 1 =
      wordTaylorPiece w a letters W 1 + wordLinDiffShift w a letters V W := by
  rw [wordTaylorPiece_one, wordTaylorPiece_one, wordLinDiffShift, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  let P := wordPositions w a
  let base : Fin n → A := ({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
    (fun j ↦ letters (w j))
  have hword : ({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
      (fun j ↦ Function.update letters a (letters a + V) (w j)) =
      (P.erase i).piecewise ((fun _ ↦ V) + base) base := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [base, P]
    · by_cases hj : w j = a
      · simp [base, P, piecewise, hji, hj, add_comm]
      · simp [base, P, piecewise, hji, hj]
  rw [hword, prod_piecewise_add]
  have hterm (s : Finset (Fin n)) (hs : s ∈ (P.erase i).powerset) :
      s.piecewise (fun _ ↦ V) base =
        ({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
          (s.piecewise (fun _ ↦ V) (fun j ↦ letters (w j))) := by
    have his : i ∉ s := fun h ↦ (mem_erase.mp (mem_powerset.mp hs h)).1 rfl
    funext j
    by_cases hji : j = i
    · subst j
      simp [base, his]
    · simp [base, piecewise, hji]
  rw [show (∑ s ∈ (P.erase i).powerset,
      (List.ofFn (s.piecewise (fun _ ↦ V) base)).prod) =
      ∑ s ∈ (P.erase i).powerset,
        (List.ofFn (({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
          (s.piecewise (fun _ ↦ V) (fun j ↦ letters (w j))))).prod from
    sum_congr rfl fun s hs ↦ congrArg (fun f ↦ (List.ofFn f).prod) (hterm s hs)]
  rw [← sum_erase_add _ _ (show ∅ ∈ (P.erase i).powerset by simp)]
  simp only [piecewise_empty]
  exact add_comm _ _

end FQFP

namespace FQFP.WordTable

variable {κ A : Type*} [DecidableEq κ] [Semiring A] [Algebra ℚ A]

/-- A coefficient table with exactly `k` perturbation positions in each row. -/
def taylorPiece (scale : ℚ) (t : Table κ) (a : κ) (letters : κ → A) (V : A) (k : ℕ) : A :=
  (t.map fun p ↦ ((p.2 : ℚ) / scale ^ p.1.length) •
    wordTaylorPiece p.1.get a letters V k).sum

/-- A Taylor component respects concatenation of coefficient tables. -/
lemma taylorPiece_append (scale : ℚ) (s t : Table κ) (a : κ) (letters : κ → A)
    (V : A) (k : ℕ) :
    taylorPiece scale (s ++ t) a letters V k =
      taylorPiece scale s a letters V k + taylorPiece scale t a letters V k := by
  simp only [taylorPiece, List.map_append, List.sum_append]

/-- Reordering coefficient rows preserves every Taylor component. -/
lemma taylorPiece_eq_of_perm (scale : ℚ) {s t : Table κ} (h : s.Perm t)
    (a : κ) (letters : κ → A) (V : A) (k : ℕ) :
    taylorPiece scale s a letters V k = taylorPiece scale t a letters V k :=
  (h.map _).sum_eq

/-- Change of the linear piece under a shift of the base letter, with every coefficient retained. -/
def linDiffShift (scale : ℚ) (t : Table κ) (a : κ) (letters : κ → A) (V W : A) : A :=
  (t.map fun p ↦ ((p.2 : ℚ) / scale ^ p.1.length) •
    wordLinDiffShift p.1.get a letters V W).sum

/-- The unperturbed table piece is the original table evaluation. -/
lemma taylorPiece_zero (scale : ℚ) (t : Table κ) (a : κ) (letters : κ → A) (V : A) :
    taylorPiece scale t a letters V 0 = eval scale letters t := by
  simp only [taylorPiece, wordTaylorPiece_zero, wordEval, List.ofFn_get, eval]

/-- The linear table piece is additive in its perturbation. -/
lemma taylorPiece_one_add (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V W : A) :
    taylorPiece scale t a letters (V + W) 1 =
      taylorPiece scale t a letters V 1 + taylorPiece scale t a letters W 1 := by
  simp only [taylorPiece, wordTaylorPiece_one_add, smul_add, List.sum_map_add]

/-- The linear table piece respects rational scalar multiplication. -/
lemma taylorPiece_one_smul (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (c : ℚ) (V : A) :
    taylorPiece scale t a letters (c • V) 1 = c • taylorPiece scale t a letters V 1 := by
  simp only [taylorPiece, wordTaylorPiece_one_smul, smul_comm _ c]
  induction t with
  | nil => simp
  | cons p t ih => simp only [List.map_cons, List.sum_cons, smul_add, ih]

/-- A positive-degree table component vanishes at a zero perturbation. -/
lemma taylorPiece_zero_direction (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) {k : ℕ} (hk : 0 < k) :
    taylorPiece scale t a letters 0 k = 0 := by
  simp only [taylorPiece, wordTaylorPiece_zero_direction _ _ _ hk, smul_zero,
    List.map_const', List.sum_replicate]

/-- A table component above every row's occurrence count vanishes. -/
lemma taylorPiece_eq_zero_of_card_lt (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V : A) (k : ℕ)
    (hk : ∀ p ∈ t, (wordPositions p.1.get a).card < k) :
    taylorPiece scale t a letters V k = 0 := by
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
  rw [wordTaylorPiece_eq_zero_of_card_lt _ _ _ _ (hk p hp), smul_zero]

/-- Expand a table at a chosen letter, using a common upper bound on its occurrence count. -/
theorem eval_update_add_eq_sum_taylorPiece (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V : A) (r : ℕ)
    (hcard : ∀ p ∈ t, (wordPositions p.1.get a).card ≤ r) :
    eval scale (Function.update letters a (letters a + V)) t =
      ∑ k ∈ range (r + 1), taylorPiece scale t a letters V k := by
  induction t with
  | nil => simp [eval, taylorPiece]
  | cons p t ih =>
    rw [eval_cons, ih (fun q hq ↦ hcard q (List.mem_cons_of_mem _ hq))]
    have hp := word_update_add_eq_sum_taylorPiece p.1.get a letters V
      (hcard p (List.mem_cons_self ..))
    simp only [wordEval, List.ofFn_get] at hp
    rw [hp, smul_sum, ← sum_add_distrib]
    rfl

/-- Expand the change in the table's linear piece when the base letter is shifted. -/
theorem taylorPiece_one_update_add (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V W : A) :
    taylorPiece scale t a (Function.update letters a (letters a + V)) W 1 =
      taylorPiece scale t a letters W 1 + linDiffShift scale t a letters V W := by
  simp only [taylorPiece, linDiffShift, wordTaylorPiece_one_update_add, smul_add,
    List.sum_map_add]

end FQFP.WordTable
