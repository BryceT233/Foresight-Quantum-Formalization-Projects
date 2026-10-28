/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Polynomial identity on a nonempty open set

For a finite set of real variables, equality of polynomial evaluations on
any nonempty open set implies equality of the polynomials. Thus local polynomial
identities determine global ones.

## Main results

* `MvPolynomial.eq_of_eval_eq_on_isOpen`: equality follows from evaluation on an open set.
-/

@[expose] public section

namespace MvPolynomial

/-- Two real polynomials in finitely many variables that agree on a nonempty
open set are equal. -/
theorem eq_of_eval_eq_on_isOpen {n : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hUn : U.Nonempty)
    (h : ∀ x ∈ U, eval x p = eval x q) : p = q := by
  obtain ⟨x, hx⟩ := hUn
  obtain ⟨s, hs, hsU⟩ := isOpen_pi_iff'.mp hU x hx
  apply funext_set s (fun i => ?_)
  · intro y hy
    exact h y (hsU hy)
  · obtain ⟨a, b, hab, hsub⟩ := (hs i).1.exists_Ioo_subset ⟨x i, (hs i).2⟩
    exact (Set.Ioo_infinite hab).mono hsub

end MvPolynomial
