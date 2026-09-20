/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.Commutator
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Norm bounds for iterated commutators

`TrotterError` bounds a single commutator and the iterated adjoint —
`norm_commutator_le` (`‖⁅A, B⁆‖ ≤ 2 * ‖A‖ * ‖B‖`), `norm_adPow_le`, `norm_adSequence_le` — but
has **no bound on `nestedComm` itself**. The `Lean-BCH` depth-3 commutator estimates need one,
so this file supplies it.

It lives in `FQFP.BCH` rather than in `TrotterError` because `TrotterError` is frozen; the two
theorems below depend only on `norm_commutator_le` and would lift into `TrotterError` unchanged
if that ever becomes worthwhile.

## Main results

* `norm_nestedComm_le`: `‖nestedComm H‖ ≤ 2 ^ p * ∏ i, ‖H i‖` for `H : Fin (p + 1) → 𝔸`.
* `norm_nestedCommOfList_le`: the list form,
  `‖nestedCommOfList b L‖ ≤ 2 ^ L.length * (‖b‖ * (L.map norm).prod)`.

## Implementation notes

The list form is proved first and the `Fin` form by induction on `p`, because `nestedComm` peels
its *last* argument: the recursive call is `nestedComm (fun i => H i.castSucc)`, whose product
is a `Fin p`-product of doubly-`castSucc`ed indices. Reducing that to a `Fin (p+1)`-product needs
the `Fin.prod_univ_castSucc` orientation recorded in the local `hprod` step.
-/

@[expose] public section

open Finset

namespace FQFP.BCH

open TrotterError

-- `TrotterError` sets the associative-ring Lie bracket up the same way (`Commutator.lean:58`).
attribute [local instance] LieRing.ofAssociativeRing

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The norm of `nestedCommOfList b L` is bounded by `2 ^ L.length` times the product of the
norms of the seed and the list entries. -/
theorem norm_nestedCommOfList_le (b : 𝔸) (L : List 𝔸) :
    ‖nestedCommOfList b L‖ ≤ 2 ^ L.length * (‖b‖ * (L.map norm).prod) := by
  induction L generalizing b with
  | nil => simp [nestedCommOfList]
  | cons x L ih =>
      rw [show nestedCommOfList b (x :: L) = nestedCommOfList ⁅x, b⁆ L from rfl,
        List.length_cons, List.map_cons, List.prod_cons, pow_succ']
      calc ‖nestedCommOfList ⁅x, b⁆ L‖
          ≤ 2 ^ L.length * (‖⁅x, b⁆‖ * (L.map norm).prod) := ih ⁅x, b⁆
        _ ≤ 2 ^ L.length * ((2 * ‖x‖ * ‖b‖) * (L.map norm).prod) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (norm_commutator_le x b)
                (List.prod_nonneg fun a ha => by
                  obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
                  exact norm_nonneg x))
              (by positivity)
        _ = 2 ^ L.length * 2 * (‖x‖ * (‖b‖ * (L.map norm).prod)) := by ring
        _ = 2 * 2 ^ L.length * (‖b‖ * (‖x‖ * (L.map norm).prod)) := by ring

/-- The norm of a `p`-fold nested commutator is bounded by `2 ^ p` times the product of the
norms of its arguments. For `p = 1` this is `norm_commutator_le`. -/
theorem norm_nestedComm_le {p : ℕ} (H : Fin (p + 1) → 𝔸) :
    ‖nestedComm H‖ ≤ 2 ^ p * ∏ i : Fin (p + 1), ‖H i‖ := by
  induction p with
  | zero =>
      rw [nestedComm]; simp
  | succ p ih =>
      rw [nestedComm]
      have hprod : (∏ i : Fin (p + 2), ‖H i‖)
          = (∏ i : Fin (p + 1), ‖H i.castSucc‖) * ‖H (Fin.last (p + 1))‖ := by
        rw [Fin.prod_univ_castSucc]
      calc ‖⁅H (Fin.last (p + 1)), nestedComm (fun i : Fin (p + 1) => H i.castSucc)⁆‖
          ≤ 2 * ‖H (Fin.last (p + 1))‖ *
              ‖nestedComm (fun i : Fin (p + 1) => H i.castSucc)‖ := norm_commutator_le _ _
        _ ≤ 2 * ‖H (Fin.last (p + 1))‖ *
              (2 ^ p * ∏ i : Fin (p + 1), ‖(fun i : Fin (p + 1) => H i.castSucc) i‖) :=
            mul_le_mul_of_nonneg_left (ih _) (by positivity)
        _ = 2 ^ (p + 1) * ∏ i : Fin (p + 2), ‖H i‖ := by
            rw [hprod]; ring

end FQFP.BCH
