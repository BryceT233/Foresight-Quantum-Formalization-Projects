module

public import Mathlib

/-!
# Spike: the order-preserving expansion behind `bchQuinticTermTaylor2Decomp`

Scratch file, not part of the library. Checked with
`lake env lean artifacts/examples/quintic-expansion-spike.lean`.

`Mathlib`'s `Finset.prod_add` is `CommSemiring`-only, and its summand
`(∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i` reorders the letters, so it is *false* for a
noncommutative ring. BCH needs a noncommutative `𝔸`, so the expansion must preserve letter
order: choose the `c`-letter at a set `T` of positions and keep everything else in place.

The induction is by *snoc* (`List.reverseRecOn`), so the position indices of the prefix are
unchanged when one letter is appended. Every product step is `List.prod_append`, which needs
no commutativity; all `Finset` steps are about sums, which are commutative anyway.

`#print axioms Spike.expansion` gives `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open Finset

namespace Spike

variable {𝔸 : Type*} [Semiring 𝔸]

/-- The absolute positions of the letter `a` (index `0`) in a binary word pattern. -/
def aPos (w : List (Fin 2)) : Finset ℕ :=
  (Finset.range w.length).filter fun j => w[j]? = some 0

/-- The ternary word read off `w` with the letter `a` at each position in `T` replaced by `c`. -/
def substWord (w : List (Fin 2)) (T : Finset ℕ) : List (Fin 3) :=
  (List.range w.length).map fun j => if j ∈ T then 1 else if w[j]? = some 0 then 0 else 2

/-- The product whose `j`-th factor is `a + c` at an `a`-position and `b` elsewhere. -/
def posProd (w : List (Fin 2)) (a c b : 𝔸) : 𝔸 :=
  ((List.range w.length).map fun j => if w[j]? = some 0 then a + c else b).prod

lemma posProd_concat (l : List (Fin 2)) (k : Fin 2) (a c b : 𝔸) :
    posProd (l ++ [k]) a c b = posProd l a c b * (if k = 0 then a + c else b) := by
  unfold posProd
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.prod_append]
  have hf : (List.range l.length).map
        (fun j => if (l ++ [k])[j]? = some 0 then a + c else b)
      = (List.range l.length).map (fun j => if l[j]? = some 0 then a + c else b) := by
    refine List.map_congr_left fun j hj => ?_
    rw [List.getElem?_append_left (List.mem_range.mp hj)]
  rw [hf]
  simp

lemma length_notMem_aPos (l : List (Fin 2)) : l.length ∉ aPos l := by
  simp [aPos]

lemma aPos_concat (l : List (Fin 2)) (k : Fin 2) :
    aPos (l ++ [k]) = if k = 0 then insert l.length (aPos l) else aPos l := by
  unfold aPos
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert,
    List.getElem?_concat_length]
  have hf : (Finset.range l.length).filter (fun j => (l ++ [k])[j]? = some 0)
      = (Finset.range l.length).filter (fun j => l[j]? = some 0) :=
    Finset.filter_congr fun j hj => by
      rw [List.getElem?_append_left (List.mem_range.mp hj)]
  rw [hf]
  by_cases hk : k = 0 <;> simp [hk]

lemma substWord_concat (l : List (Fin 2)) (k : Fin 2) (T : Finset ℕ) :
    substWord (l ++ [k]) T
      = substWord l (T.erase l.length)
        ++ [if l.length ∈ T then 1 else if k = 0 then 0 else 2] := by
  unfold substWord
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun j hj => ?_
    have hjlt : j < l.length := List.mem_range.mp hj
    have hjn : j ≠ l.length := by lia
    rw [List.getElem?_append_left hjlt]
    by_cases h : j ∈ T <;> simp [h, hjn, Finset.mem_erase]
  · simp

/-! ### The two letter shapes, `k = 0` (`a`) and `k = 1` (`b`) -/

section Cases

variable (l : List (Fin 2)) (a c b : 𝔸)

lemma posProd_concat_zero : posProd (l ++ [0]) a c b = posProd l a c b * (a + c) := by
  rw [posProd_concat]; simp

lemma posProd_concat_one : posProd (l ++ [1]) a c b = posProd l a c b * b := by
  rw [posProd_concat]; simp

lemma aPos_concat_zero : aPos (l ++ [0]) = insert l.length (aPos l) := by
  rw [aPos_concat]; simp

lemma aPos_concat_one : aPos (l ++ [1]) = aPos l := by
  rw [aPos_concat]; simp

lemma substWord_concat_zero (T : Finset ℕ) :
    substWord (l ++ [0]) T = substWord l (T.erase l.length) ++ [if l.length ∈ T then 1 else 0] := by
  rw [substWord_concat]; simp

lemma substWord_concat_one (T : Finset ℕ) :
    substWord (l ++ [1]) T = substWord l (T.erase l.length) ++ [if l.length ∈ T then 1 else 2] := by
  rw [substWord_concat]; simp

end Cases

/-- **Order-preserving expansion.** Replacing the letter `a` by the sum `a + c` in a binary
word product distributes into the sum over the subsets `T` of the `a`-positions of the
products in which exactly the positions in `T` carry `c` instead of `a`.

This is the noncommutative replacement for `Finset.prod_add`: the factors stay in their
original positions, so no commutativity is used. -/
theorem expansion (w : List (Fin 2)) (a c b : 𝔸) :
    posProd w a c b
      = ∑ T ∈ (aPos w).powerset, ((substWord w T).map ![a, c, b]).prod := by
  induction w using List.reverseRecOn with
  | nil => simp [posProd, aPos, substWord]
  | append_singleton l k ih =>
      have hsub : ∀ x ∈ (aPos l).powerset, x ⊆ aPos l := fun x hx =>
        Finset.mem_powerset.mp hx
      have hxn : ∀ x ∈ (aPos l).powerset, l.length ∉ x := fun x hx h =>
        length_notMem_aPos l (hsub x hx h)
      have hk2 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
      obtain rfl | rfl := hk2
      · rw [posProd_concat_zero, ih, aPos_concat_zero,
          Finset.sum_powerset_insert (length_notMem_aPos l), mul_add, Finset.sum_mul,
          Finset.sum_mul]
        congr 1
        · refine Finset.sum_congr rfl fun x hx => ?_
          have hxer : x.erase l.length = x := Finset.erase_eq_of_notMem (hxn x hx)
          rw [substWord_concat_zero, hxer]
          simp [hxn x hx]
        · refine Finset.sum_congr rfl fun x hx => ?_
          have hiner : (insert l.length x).erase l.length = x :=
            Finset.erase_insert (hxn x hx)
          rw [substWord_concat_zero, hiner]
          simp
      · rw [posProd_concat_one, ih, aPos_concat_one, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxer : x.erase l.length = x := Finset.erase_eq_of_notMem (hxn x hx)
        rw [substWord_concat_one, hxer]
        simp [hxn x hx]

end Spike

