/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Multipoint fields and their Carleman lift

A level `k` field has `k` independent points of `ℝ^m` and an ordered tuple of
`k` component indices in `Fin n`. Its coordinates represent the continuous
Kronecker product in the PDE Carleman construction.

The carrier consists of functions, with no regularity or norm imposed.
Time derivatives are stated at fixed spatial points and component indices,
using only the derivatives of the finitely many factors at those points.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace Carleman.PDE

/-- A level `k` field on `k` independent points, with ordered component indices. -/
abbrev MultipointField (m n k : ℕ) :=
  (Fin k → (Fin m → ℝ)) → ((Fin k → Fin n) → ℝ)

/-- The continuous Kronecker power of a field, expressed in ordered coordinates. -/
def multipointLift {m n k : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ) :
    MultipointField m n k :=
  fun xs js => ∏ i : Fin k, u (xs i) (js i)

/-- Inserting an independent point and component inserts one factor in the lift. -/
lemma multipointLift_insertNth {m n k : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (p : Fin (k + 1)) (x : Fin m → ℝ) (c : Fin n)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    multipointLift u (p.insertNth x xs) (p.insertNth c js) =
      u x c * multipointLift u xs js := by
  unfold multipointLift
  rw [Fin.prod_univ_succAbove _ p]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- Replacing one slot isolates its factor without dividing by any field value. -/
lemma multipointLift_update {m n k : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (p : Fin k) (x : Fin m → ℝ) (c : Fin n)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    multipointLift u (Function.update xs p x) (Function.update js p c) =
      u x c * ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  unfold multipointLift
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- Removing a slot leaves exactly the product over the other original slots. -/
lemma multipointLift_removeNth {m n k : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (p : Fin (k + 1)) (xs : Fin (k + 1) → (Fin m → ℝ)) (js : Fin (k + 1) → Fin n) :
    multipointLift u (p.removeNth xs) (p.removeNth js) =
      ∏ i ∈ Finset.univ.erase p, u (xs i) (js i) := by
  unfold multipointLift
  refine Finset.prod_bij (fun i _ => p.succAbove i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne p i, Finset.mem_univ _⟩
  · intro i _ j _ h
    exact Fin.succAbove_right_injective h
  · intro j hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
    exact ⟨i, Finset.mem_univ _, hi⟩

lemma multipointLift_zero {m n : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (xs : Fin 0 → (Fin m → ℝ)) (js : Fin 0 → Fin n) :
    multipointLift u xs js = 1 := by
  simp [multipointLift]

lemma multipointLift_one {m n : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (xs : Fin 1 → (Fin m → ℝ)) (js : Fin 1 → Fin n) :
    multipointLift u xs js = u (xs 0) (js 0) := by
  simp [multipointLift]

/-- Simultaneously permuting spatial points and component slots leaves the lift unchanged. -/
lemma multipointLift_reindex {m n k : ℕ} (u : (Fin m → ℝ) → Fin n → ℝ)
    (e : Fin k ≃ Fin k) (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) :
    multipointLift u (xs ∘ e) (js ∘ e) = multipointLift u xs js := by
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

/-- The time product rule for the lift, including derivatives within a time interval. -/
lemma hasDerivWithinAt_multipointLift {m n k : ℕ}
    (u : ℝ → (Fin m → ℝ) → Fin n → ℝ) (v : (Fin m → ℝ) → Fin n → ℝ)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) (I : Set ℝ) (t : ℝ)
    (hu : ∀ i, HasDerivWithinAt (fun s => u s (xs i) (js i)) (v (xs i) (js i)) I t) :
    HasDerivWithinAt (fun s => multipointLift (u s) xs js)
      (∑ i : Fin k, v (xs i) (js i) *
        ∏ j ∈ Finset.univ.erase i, u t (xs j) (js j)) I t := by
  simpa only [multipointLift, smul_eq_mul, mul_comm] using
    (HasDerivWithinAt.fun_finsetProd (u := Finset.univ) (fun i _ => hu i))

/-- The time derivative of the lift at fixed spatial points and component indices. -/
lemma hasDerivAt_multipointLift {m n k : ℕ}
    (u : ℝ → (Fin m → ℝ) → Fin n → ℝ) (v : (Fin m → ℝ) → Fin n → ℝ)
    (xs : Fin k → (Fin m → ℝ)) (js : Fin k → Fin n) (t : ℝ)
    (hu : ∀ i, HasDerivAt (fun s => u s (xs i) (js i)) (v (xs i) (js i)) t) :
    HasDerivAt (fun s => multipointLift (u s) xs js)
      (∑ i : Fin k, v (xs i) (js i) *
        ∏ j ∈ Finset.univ.erase i, u t (xs j) (js j)) t := by
  rw [← hasDerivWithinAt_univ]
  exact hasDerivWithinAt_multipointLift u v xs js Set.univ t
    (fun i => (hu i).hasDerivWithinAt)

end Carleman.PDE
