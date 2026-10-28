/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.Taylor
public import FQFP.Analysis.Normed.Algebra.Word
public import FQFP.Analysis.Normed.Algebra.WordTable

/-!
# Norm bounds for finite Taylor expansions of ordered words

The same substitution sets used in the algebraic expansion supply their norm budgets.
A Taylor piece retains its prescribed perturbation power. Higher perturbation powers can
be absorbed into a common bound on the actual inputs, while independent perturbation
bounds remain unrestricted above. Derivative shifts retain the derivative direction as
one factor without imposing a common bound on that direction.

## Main definitions

* `FQFP.WordTable.taylorWeight`, `FQFP.WordTable.linDiffShiftWeight`: weighted position counts.

## Main results

* `FQFP.norm_wordTaylorPiece_le`, `FQFP.norm_wordLinDiffShift_le`: ordered word estimates.
* `FQFP.WordTable.norm_taylorPiece_le_of_le`: retain a chosen number of perturbation factors.
* `FQFP.WordTable.norm_sum_taylorPiece_le_of_le`: combine finitely many perturbation degrees.
* `FQFP.WordTable.norm_linDiffShift_le`: estimate a derivative shift in a word table.
-/

@[expose] public noncomputable section

open Finset

/-- A rational absolute-value budget can be computed before casting it to the reals. -/
lemma List.sum_map_norm_mul_natCast {ι : Type*} (l : List ι) (c : ι → ℚ) (b : ι → ℕ) :
    (l.map fun p ↦ ‖c p‖ * (b p : ℝ)).sum =
      (((l.map fun p ↦ |c p| * (b p : ℚ)).sum : ℚ) : ℝ) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [ih]
    simp only [Rat.cast_mul, Rat.cast_abs, Rat.cast_natCast, ← Rat.norm_cast_real, Real.norm_eq_abs]

namespace FQFP

/-- A two-letter assignment is bounded when each of its two values is bounded. -/
lemma norm_pair_le {A : Type*} [Norm A] (x y : A) {M : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (i : Fin 2) : ‖![x, y] i‖ ≤ M := by
  fin_cases i
  · exact hx
  · exact hy

section Bounds

variable {κ A : Type*} [DecidableEq κ] [NormedRing A]

/-- Bound a word piece by the number of its selected position subsets. -/
lemma norm_wordTaylorPiece_le {n : ℕ} (hn : 0 < n) (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V : A) (k : ℕ) {M Vn : ℝ}
    (hletters : ∀ i, ‖letters (w i)‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖wordTaylorPiece w a letters V k‖ ≤
      ((wordPositions w a).card.choose k : ℝ) * (Vn ^ k * M ^ (n - k)) := by
  calc
    _ ≤ ∑ _s ∈ (wordPositions w a).powersetCard k, Vn ^ k * M ^ (n - k) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
      simpa only [(mem_powersetCard.mp hs).2] using
        norm_prod_piecewise_le_of_pos hn s (fun _ ↦ V) (fun i ↦ letters (w i))
          (fun _ _ ↦ hV) (fun i _ ↦ hletters i)
    _ = _ := by simp only [sum_const, card_powersetCard, nsmul_eq_mul]

private lemma pow_mul_pow_le_of_le {v M : ℝ} (hv : 0 ≤ v) (hM : 0 ≤ M) (hvM : v ≤ M)
    (n k r : ℕ) (hrk : r ≤ k) (hkn : k ≤ n) :
    v ^ k * M ^ (n - k) ≤ v ^ r * M ^ (n - r) := by
  calc
    _ = v ^ r * (v ^ (k - r) * M ^ (n - k)) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hrk]
    _ ≤ v ^ r * (M ^ (k - r) * M ^ (n - k)) := by gcongr
    _ = _ := by
      rw [← pow_add]
      congr 2
      lia

/-- Bound the change of a word derivative, preserving one factor from each perturbation.
Only the base perturbation `V`, not the derivative direction `W`, is bounded by `M`. -/
lemma norm_wordLinDiffShift_le {n : ℕ} (hn : 0 < n) (w : Fin n → κ) (a : κ)
    (letters : κ → A) (V W : A) {M Vn Wn : ℝ}
    (hletters : ∀ i, ‖letters (w i)‖ ≤ M) (hVM : ‖V‖ ≤ M)
    (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖wordLinDiffShift w a letters V W‖ ≤
      ((wordPositions w a).card * (2 ^ ((wordPositions w a).card - 1) - 1) : ℕ) *
        (Vn * Wn * M ^ (n - 2)) := by
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  have hWn : 0 ≤ Wn := (norm_nonneg W).trans hW
  calc
    _ ≤ ∑ i ∈ wordPositions w a,
        ∑ _s ∈ ((wordPositions w a).erase i).powerset.erase ∅,
          Vn * Wn * M ^ (n - 2) := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun s hs ↦ ?_)
      obtain ⟨hs0, hs⟩ := mem_erase.mp hs
      have hspos : 1 ≤ s.card := by simpa using card_pos.mpr (nonempty_iff_ne_empty.mpr hs0)
      have hss := mem_powerset.mp hs
      have his : i ∉ s := fun h ↦ (mem_erase.mp (hss h)).1 rfl
      have hsn : s.card + 1 ≤ n := by
        simpa only [card_insert_of_notMem his, card_univ, Fintype.card_fin] using
          card_le_card (subset_univ (insert i s))
      have hfn : ({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
          (s.piecewise (fun _ ↦ V) (fun j ↦ letters (w j))) =
          ({i} : Finset (Fin n)).piecewise (fun _ ↦ W)
            ((insert i s).piecewise (fun _ ↦ V) (fun j ↦ letters (w j))) := by
        funext j
        by_cases hji : j = i
        · simp [piecewise, hji]
        · simp [piecewise, hji]
      rw [hfn]
      have hprod := norm_prod_piecewise_piecewise_le_of_pos hn (insert i s) {i}
        (singleton_subset_iff.mpr (mem_insert_self i s)) (fun _ ↦ W) (fun _ ↦ V)
        (fun j ↦ letters (w j)) (fun _ _ ↦ hW) (fun _ _ _ ↦ le_rfl)
        (fun j _ ↦ hletters j)
      simp only [card_singleton, card_insert_of_notMem his, Nat.add_sub_cancel, pow_one] at hprod
      have hp : ‖V‖ ^ s.card * M ^ (n - (s.card + 1)) ≤ ‖V‖ * M ^ (n - 2) := by
        simpa only [pow_one, show n - 1 - s.card = n - (s.card + 1) by lia,
          show n - 1 - 1 = n - 2 by lia] using
          pow_mul_pow_le_of_le (norm_nonneg V) hM hVM (n - 1) s.card 1 hspos (by lia)
      calc
        _ ≤ Wn * (‖V‖ ^ s.card * M ^ (n - (s.card + 1))) := by
          simpa only [mul_assoc] using hprod
        _ ≤ Wn * (‖V‖ * M ^ (n - 2)) := mul_le_mul_of_nonneg_left hp hWn
        _ ≤ Vn * Wn * M ^ (n - 2) := by
          calc
            _ ≤ Wn * (Vn * M ^ (n - 2)) := by gcongr
            _ = _ := by ring
    _ = _ := by
      calc
        _ = ∑ _i ∈ wordPositions w a,
            ((2 ^ ((wordPositions w a).card - 1) - 1 : ℕ) : ℝ) *
              (Vn * Wn * M ^ (n - 2)) := by
          apply sum_congr rfl
          intro i hi
          simp only [sum_const, card_erase_of_mem (empty_mem_powerset _), card_powerset,
            card_erase_of_mem hi, nsmul_eq_mul]
        _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

end Bounds

namespace WordTable

/-- The absolute coefficient budget weighted by the number of `k`-position substitutions. -/
noncomputable def taylorWeight {κ : Type*} [DecidableEq κ]
    (scale : ℚ) (t : Table κ) (a : κ) (k : ℕ) : ℝ :=
  (t.map fun p ↦ ‖(p.2 : ℚ) / scale ^ p.1.length‖ *
    ((wordPositions p.1.get a).card.choose k : ℝ)).sum

/-- The absolute coefficient budget for one derivative position and a nonempty base shift. -/
noncomputable def linDiffShiftWeight {κ : Type*} [DecidableEq κ]
    (scale : ℚ) (t : Table κ) (a : κ) : ℝ :=
  (t.map fun p ↦ ‖(p.2 : ℚ) / scale ^ p.1.length‖ *
    (((wordPositions p.1.get a).card *
      (2 ^ ((wordPositions p.1.get a).card - 1) - 1) : ℕ) : ℝ)).sum

variable {κ A : Type*} [DecidableEq κ] [NormedRing A] [NormedAlgebra ℚ A]

/-- Bound a homogeneous table Taylor piece using its weighted substitution count. -/
lemma norm_taylorPiece_le (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V : A) (k n : ℕ) (hn : 0 < n)
    (hlen : ∀ p ∈ t, p.1.length = n) {M Vn : ℝ}
    (hletters : ∀ p ∈ t, ∀ i, ‖letters (p.1.get i)‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖taylorPiece scale t a letters V k‖ ≤
      taylorWeight scale t a k * (Vn ^ k * M ^ (n - k)) := by
  apply List.norm_sum_map_smul_le
  intro p hp
  have hlength := hlen p hp
  simpa only [hlength] using
    norm_wordTaylorPiece_le (by lia) p.1.get a letters V k (hletters p hp) hV

/-- Retain any `r` perturbation factors and absorb the rest into a common input bound.
The independent perturbation bound `Vn` need not lie below `M`. -/
lemma norm_taylorPiece_le_of_le (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V : A) (k n r : ℕ) (hn : 0 < n) (hrk : r ≤ k) (hkn : k ≤ n)
    (hlen : ∀ p ∈ t, p.1.length = n) {M Vn : ℝ}
    (hletters : ∀ p ∈ t, ∀ i, ‖letters (p.1.get i)‖ ≤ M)
    (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) :
    ‖taylorPiece scale t a letters V k‖ ≤
      taylorWeight scale t a k * (Vn ^ r * M ^ (n - r)) := by
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  have hw : 0 ≤ taylorWeight scale t a k := by
    apply List.sum_nonneg
    intro v hv
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
    positivity
  apply (norm_taylorPiece_le scale t a letters V k n hn hlen hletters le_rfl).trans
  apply mul_le_mul_of_nonneg_left _ hw
  calc
    _ ≤ ‖V‖ ^ r * M ^ (n - r) :=
      pow_mul_pow_le_of_le (norm_nonneg V) hM hVM n k r hrk hkn
    _ ≤ _ := by gcongr

/-- Bound a finite family of Taylor components while retaining a common perturbation degree. -/
lemma norm_sum_taylorPiece_le_of_le {ι : Type*} (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V : A) (s : Finset ι) (degree : ι → ℕ) (n r : ℕ) (hn : 0 < n)
    (hr : ∀ i ∈ s, r ≤ degree i) (hdeg : ∀ i ∈ s, degree i ≤ n)
    (hlen : ∀ p ∈ t, p.1.length = n) {M Vn C : ℝ}
    (hletters : ∀ p ∈ t, ∀ i, ‖letters (p.1.get i)‖ ≤ M)
    (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn)
    (hC : ∑ i ∈ s, taylorWeight scale t a (degree i) ≤ C) :
    ‖∑ i ∈ s, taylorPiece scale t a letters V (degree i)‖ ≤
      C * (Vn ^ r * M ^ (n - r)) := by
  have hM : 0 ≤ M := (norm_nonneg V).trans hVM
  have hVn : 0 ≤ Vn := (norm_nonneg V).trans hV
  calc
    _ ≤ ∑ i ∈ s, taylorWeight scale t a (degree i) * (Vn ^ r * M ^ (n - r)) :=
      norm_sum_le_of_le _ fun i hi ↦
        norm_taylorPiece_le_of_le scale t a letters V (degree i) n r hn
          (hr i hi) (hdeg i hi) hlen hletters hVM hV
    _ = (∑ i ∈ s, taylorWeight scale t a (degree i)) * (Vn ^ r * M ^ (n - r)) :=
      (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

/-- Bound a table derivative shift by the product of independent perturbation bounds. -/
lemma norm_linDiffShift_le (scale : ℚ) (t : Table κ) (a : κ)
    (letters : κ → A) (V W : A) (n : ℕ) (hn : 0 < n)
    (hlen : ∀ p ∈ t, p.1.length = n) {M Vn Wn : ℝ}
    (hletters : ∀ p ∈ t, ∀ i, ‖letters (p.1.get i)‖ ≤ M)
    (hVM : ‖V‖ ≤ M) (hV : ‖V‖ ≤ Vn) (hW : ‖W‖ ≤ Wn) :
    ‖linDiffShift scale t a letters V W‖ ≤
      linDiffShiftWeight scale t a * (Vn * Wn * M ^ (n - 2)) := by
  apply List.norm_sum_map_smul_le
  intro p hp
  have hlength := hlen p hp
  simpa only [hlength] using
    norm_wordLinDiffShift_le (by lia) p.1.get a letters V W (hletters p hp) hVM hV hW

end WordTable

end FQFP
