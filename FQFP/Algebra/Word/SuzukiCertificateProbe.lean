/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Word.CoeffTable

/-!
# Finite word-position probes for Suzuki certificates

The degree-five binary alphabet has 32 positions, including zero coefficient
positions. The degree-seven ternary probe checks the 2187-position scale of
the same concrete word enumeration used by finite coefficient tables.
-/

@[expose] public section

namespace FQFP.CoeffWordTable

/-- Enumerate every ordered word of fixed length on `Fin alphabetSize`. -/
def fixedWords (alphabetSize : ℕ) : ℕ → List (List (Fin alphabetSize))
  | 0 => [[]]
  | n + 1 => (fixedWords alphabetSize n).flatMap fun w ↦
      (List.finRange alphabetSize).map fun letter ↦ letter :: w

/-- Membership is exactly the word-length condition. -/
theorem mem_fixedWords_iff_length (alphabetSize n : ℕ)
    (w : List (Fin alphabetSize)) :
    w ∈ fixedWords alphabetSize n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [fixedWords]
  | succ n ih =>
      cases w with
      | nil => simp [fixedWords]
      | cons a w =>
          simp only [fixedWords, List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨v, hv, b, hb, hbw⟩
            have h := List.cons.inj hbw
            simpa [h.2] using (ih v).mp hv
          · intro hlen
            refine ⟨w, (ih w).mpr ?_, a, List.mem_finRange a, rfl⟩
            simpa using hlen

/-- Fixed-length enumeration has no repeated words. -/
theorem fixedWords_nodup (alphabetSize n : ℕ) :
    (fixedWords alphabetSize n).Nodup := by
  induction n with
  | zero => simp [fixedWords]
  | succ n ih =>
      rw [fixedWords, List.nodup_flatMap]
      constructor
      · intro w hw
        exact (List.nodup_finRange alphabetSize).map
          (fun a b h ↦ (List.cons.inj h).1)
      · apply ih.imp
        intro w v hne
        apply List.disjoint_left.mpr
        intro x hx hy
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
        obtain ⟨b, _, hab⟩ := List.mem_map.mp hy
        exact hne (List.cons.inj hab).2.symm

/-- All 32 positions of the binary quintic word table are enumerated. -/
theorem binary_quintic_position_count : (fixedWords 2 5).length = 32 := by
  decide +kernel

/-- Binary quintic positions are pairwise distinct. -/
theorem binary_quintic_positions_nodup : (fixedWords 2 5).Nodup := by
  exact fixedWords_nodup 2 5

/-- The ternary septic enumeration reaches all 2187 ordered positions. -/
theorem ternary_septic_position_count : (fixedWords 3 7).length = 2187 := by
  decide +kernel

/-- The 2187 enumerated words each have degree seven. -/
theorem ternary_septic_position_lengths :
    (fixedWords 3 7).all (fun w ↦ w.length == 7) = true := by
  decide +kernel

/-- The ternary septic scale probe contains no repeated word positions. -/
theorem ternary_septic_positions_nodup : (fixedWords 3 7).Nodup := by
  exact fixedWords_nodup 3 7

end FQFP.CoeffWordTable
