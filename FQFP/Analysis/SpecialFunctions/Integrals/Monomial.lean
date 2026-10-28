/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Nested monomial integrals

Successive interval integrals admit an explicit coefficient and power-order formula.

## Main results

* `TrotterError.iteratedIntegralMonomial`.
* `TrotterError.monomialConstant`.
* `TrotterError.iteratedIntegralMonomial_eq`.
* `TrotterError.monomial_integral_order`.
-/

@[expose] public section

namespace TrotterError

open Asymptotics Finset
open scoped Topology BigOperators

/-- The canonical nested iterated integral of a monomial: `Γ` nested integrals, the `(i+1)`-st
integration variable carrying the power `p i`, each integral running from `0` to the immediately
preceding variable (the outermost from `0` to `t`). This is the sequential specialization of the
paper's `lem:monomial`; the general form (each inner upper limit an arbitrary earlier variable)
has the same order `t^{Σp + Γ}` by the same induction. -/
noncomputable def iteratedIntegralMonomial (Γ : ℕ) (p : Fin Γ → ℕ) : ℝ → ℝ :=
  match Γ with
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ τ in 0..t, τ ^ p 0 * iteratedIntegralMonomial n (Fin.tail p) τ

/-- The scalar constant in the closed form of `iteratedIntegralMonomial`: the nested integral of
the monomial equals `monomialConstant Γ p * t ^ ((∑ i, p i) + Γ)`. -/
noncomputable def monomialConstant (Γ : ℕ) (p : Fin Γ → ℕ) : ℝ :=
  match Γ with
  | 0 => 1
  | n + 1 => monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ)

/-- Closed form of the canonical nested monomial integral. -/
lemma iteratedIntegralMonomial_eq (Γ : ℕ) (p : Fin Γ → ℕ) (t : ℝ) :
    iteratedIntegralMonomial Γ p t = monomialConstant Γ p * t ^ ((∑ i : Fin Γ, p i) + Γ) := by
  induction Γ generalizing t with
  | zero => simp [iteratedIntegralMonomial, monomialConstant]
  | succ n ih =>
      change (∫ τ in 0..t, τ ^ p 0 * iteratedIntegralMonomial n (Fin.tail p) τ) =
        monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ) *
          t ^ ((∑ i : Fin (n + 1), p i) + (n + 1))
      simp_rw [ih (Fin.tail p)]
      have hsum : (∑ i : Fin (n + 1), p i) = p 0 + ∑ i : Fin n, Fin.tail p i := by
        rw [Fin.sum_univ_succ]
        rfl
      calc
        (∫ τ in 0..t, τ ^ p 0 * (monomialConstant n (Fin.tail p) *
              τ ^ ((∑ i : Fin n, Fin.tail p i) + n)))
            = ∫ τ in 0..t, monomialConstant n (Fin.tail p) *
                τ ^ ((∑ i : Fin (n + 1), p i) + n) := by
                apply intervalIntegral.integral_congr_uIoo
                intro τ hτ
                change τ ^ p 0 * (monomialConstant n (Fin.tail p) *
                    τ ^ ((∑ i : Fin n, Fin.tail p i) + n)) =
                  monomialConstant n (Fin.tail p) * τ ^ ((∑ i : Fin (n + 1), p i) + n)
                rw [hsum]; ring
        _ = monomialConstant n (Fin.tail p) *
              ∫ τ in 0..t, τ ^ ((∑ i : Fin (n + 1), p i) + n) := by
                rw [intervalIntegral.integral_const_mul]
        _ = monomialConstant n (Fin.tail p) * (t ^ (((∑ i : Fin (n + 1), p i) + n) + 1) /
              ((((∑ i : Fin (n + 1), p i) + n) + 1 : ℕ) : ℝ)) := by simp
        _ = (monomialConstant n (Fin.tail p) / (((∑ i : Fin (n + 1), p i) + (n + 1)) : ℝ)) *
              t ^ ((∑ i : Fin (n + 1), p i) + (n + 1)) := by
                rw [Nat.add_assoc]; ring_nf; norm_num

/-- `lem:monomial`: the canonical nested iterated integral of a monomial is `O(t^{Σp + Γ})`. -/
theorem monomial_integral_order (Γ : ℕ) (p : Fin Γ → ℕ) :
    (fun t : ℝ => iteratedIntegralMonomial Γ p t) =O[𝓝 (0 : ℝ)]
      (fun t => t ^ ((∑ i : Fin Γ, p i) + Γ)) := by
  have h : (fun t : ℝ => iteratedIntegralMonomial Γ p t) =
      fun t => monomialConstant Γ p * t ^ ((∑ i : Fin Γ, p i) + Γ) := by
    funext t
    exact iteratedIntegralMonomial_eq Γ p t
  exact h ▸ isBigO_const_mul_self (monomialConstant Γ p)
    (fun t => t ^ ((∑ i : Fin Γ, p i) + Γ)) (𝓝 (0 : ℝ))

end TrotterError
