/-
Prove2Me definition bundle for `TrotterError.norm_commutatorRemainder_le`.

The def/structure layer needed by the target's formal_statement, so that
the statement compiles standalone. Generated from the FQFP TrotterError
development; source spans are taken verbatim.

Source: https://github.com/BryceT233/Foresight-Quantum-Formalization-Projects/tree/d6bfac12d15bc59fcc5f90206ac3312da602eb3d
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Multinomial

open Finset LieAlgebra
open scoped algebraMap
attribute [local instance] LieRing.ofAssociativeRing
open NormedSpace MeasureTheory
open scoped ContDiff algebraMap
open NormedSpace MeasureTheory Finset

namespace TrotterError

/-! #### from FQFP.TrotterError.Commutator -/


-- TrotterError.adPow
/-- The `q`-fold iterated adjoint `ad_A^q = (ad A)^q`, as an ℝ-linear endomorphism of `𝔸`. -/
abbrev adPow {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] (A : 𝔸) (q : ℕ) : Module.End ℝ 𝔸 :=
  (ad ℝ 𝔸 A) ^ q

-- TrotterError.adSequence
/-- The iterated `ad` over a sequence of operators with multiplicities,
`ad_{A ⟨s-1⟩}^{q ⟨s-1⟩} ⋯ ad_{A ⟨0⟩}^{q ⟨0⟩}(B)`, where `A ⟨0⟩` is applied first
(innermost) and `A ⟨s-1⟩` is applied last (outermost). -/
def adSequence {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (q : Fin s → ℕ) (B : 𝔸) : 𝔸 :=
  match s with
  | 0 => B
  | s + 1 =>
      adPow (A (Fin.last s)) (q (Fin.last s))
        (adSequence (fun i : Fin s => A i.castSucc) (fun i : Fin s => q i.castSucc) B)

-- TrotterError.αCommConj
/-- The paper's `α_comm(A_s, …, A_1, B)`: the multinomial-weighted sum
`Σ_{q₁+⋯+q_s = p} (p choose q₁⋯q_s) ‖ad_{A_s}^{q_s} ⋯ ad_{A_1}^{q_1}(B)‖`. -/
noncomputable def αCommConj {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ q ∈ Finset.finAntidiagonal s p,
    (Nat.multinomial (Finset.univ : Finset (Fin s)) q : ℝ) * ‖adSequence A q B‖

/-! #### from FQFP.TrotterError.ExpSMulConj -/


-- TrotterError.expSMulConj
/-- Single conjugation `e^{τA} X e^{-τA} = exp (τ • A) * X * exp ((-τ) • A)`. -/
noncomputable def expSMulConj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    (A X : 𝔸) (τ : ℝ) : 𝔸 :=
  exp (τ • A) * X * exp ((-τ) • A)

/-! #### from FQFP.TrotterError.CommutatorExpansion -/


-- TrotterError.commutatorRemainderTerm
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

-- TrotterError.commutatorRemainder
/-- The operator-valued remainder `𝒞(τ)` of `thm:comm_exp_conj` (theory.tex:229-235). The outer
sum runs over 0-based layer indices `j : Fin s` with `k := j + 1` the 1-based index of the paper,
so `A j` is `A_k`, the antidiagonal condition `q₁ + ⋯ + q_k = p` is `q ∈ finAntidiagonal (j + 1) p`
with `q (Fin.last j) = q_k`, and `q_k ≠ 0` is `q (Fin.last j) ≠ 0`. The `ad` sequence is
`adSequence (A ∘ Fin.castLE …) q B = ad_{A_k}^{q_k} ⋯ ad_{A₁}^{q₁}(B)`. -/
noncomputable def commutatorRemainder {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    {s : ℕ} (A : Fin s → 𝔸) (B : 𝔸) (p : ℕ) (τ : ℝ) : 𝔸 :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    commutatorRemainderTerm A B τ j q

-- TrotterError.layerSum
/-- The layer-by-layer sum of multinomial-weighted `adSequence` norms appearing in the bound of
`commutatorRemainder`, summed over the 1-based layers `1..s`. -/
noncomputable def layerSum {𝔸 : Type*} [NormedRing 𝔸] [Algebra ℝ 𝔸] {s : ℕ} (A : Fin s → 𝔸)
    (B : 𝔸) (p : ℕ) : ℝ :=
  ∑ j : Fin s, ∑ q ∈ (finAntidiagonal (j + 1) p).filter (fun q => q (Fin.last j) ≠ 0),
    (Nat.multinomial (univ : Finset (Fin (j + 1))) q : ℝ) *
      ‖adSequence (A ∘ Fin.castLE (Nat.succ_le_of_lt j.2)) q B‖

end TrotterError
