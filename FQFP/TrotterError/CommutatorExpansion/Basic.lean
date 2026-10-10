/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.TrotterError.ExpSMulConj

import FQFP.TrotterError.ListLemmas

/-!
# Multi-layer conjugation and its remainder

Definitions of `multiConj`, `conjCoeff`, `commutatorRemainderTerm`, and
`commutatorRemainder`, preserving the paper's noncommutative factor order.
-/

@[expose] public section

namespace TrotterError

open NormedSpace MeasureTheory Finset
open TrotterError.List
open scoped ContDiff algebraMap

/-! ### Multi-layer conjugation `thm:comm_exp_conj` -/

/-- The multi-layer conjugation `e^{τA_{s-1}}⋯e^{τA₀} B e^{-τA₀}⋯e^{-τA_{s-1}}`, where
`A ⟨0⟩` is innermost (the paper's `A₁`, applied first) and `A ⟨s-1⟩` is outermost (the paper's
`A_s`). -/
noncomputable def multiConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) : 𝔸 :=
  (List.ofFn (fun i : Fin s => exp (τ • A i))).reverse.prod * B *
    (List.ofFn (fun i : Fin s => exp (-τ • A i))).prod

/-- The single `(j, q)` summand of `commutatorRemainder`. -/
@[irreducible]
noncomputable def commutatorRemainderTerm {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (τ : ℝ) (j : Fin s) (q : Fin (j + 1) → ℕ) : 𝔸 :=
  ((List.ofFn (fun i : Fin s => exp (τ • A i))).drop (j + 1)).reverse.prod *
    (∫ u in 0..τ, (((τ - u) ^ (q (Fin.last j) - 1) * τ ^ (∑ i : Fin j, q i.castSucc) /
        ((Nat.factorial (q (Fin.last j) - 1) : ℝ) *
          ∏ i : Fin j, (Nat.factorial (q i.castSucc) : ℝ))) : ℝ) •
      expSMulConj (A j) (adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B) u) *
    ((List.ofFn (fun i : Fin s => exp (-τ • A i))).drop (j + 1)).prod

/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

/-- The `τ^j` coefficient of the multi-layer conjugation, as the multinomial-weighted sum
`Σ_{q ∈ finAntidiagonal s j} (∏ i, q_i!⁻¹) • adSequence A q B`. -/
noncomputable def conjCoeff {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (j : ℕ) : 𝔸 :=
  ∑ q ∈ finAntidiagonal s j,
    ((∏ i : Fin s, (Nat.factorial (q i) : ℝ))⁻¹ : ℝ) • adSequence A q B

end TrotterError
