/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Polynomial.Module.Calculus
public import Mathlib.Tactic.Linarith

/-!
# Coefficientwise degree bounds for polynomial modules

`DegreeLE p n` means that coefficients above `n` vanish, including when the
coefficient space is trivial. The integral bound is independent of Lie brackets
and associative multiplication.
-/

@[expose] public noncomputable section

namespace PolynomialModule

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

/-- A coefficientwise upper bound on polynomial degree. -/
def DegreeLE (p : PolynomialModule ℚ M) (n : ℕ) : Prop :=
  ∀ k, n < k → p.coeff k = 0

theorem degreeLE_zero (n : ℕ) : DegreeLE (0 : PolynomialModule ℚ M) n := by
  intro k hk
  simp

theorem DegreeLE.mono {p : PolynomialModule ℚ M} {m n : ℕ}
    (h : DegreeLE p m) (hmn : m ≤ n) : DegreeLE p n :=
  fun k hk ↦ h k (by lia)

theorem degreeLE_single {i n : ℕ} (m : M) (hi : i ≤ n) :
    DegreeLE (single ℚ i m) n := by
  intro k hk
  simp [show i ≠ k by lia]

theorem DegreeLE.add {p q : PolynomialModule ℚ M} {n : ℕ}
    (hp : DegreeLE p n) (hq : DegreeLE q n) : DegreeLE (p + q) n := by
  intro k hk
  simp [hp k hk, hq k hk]

theorem DegreeLE.smul {p : PolynomialModule ℚ M} {n : ℕ}
    (hp : DegreeLE p n) (r : ℚ) : DegreeLE (r • p) n := by
  intro k hk
  change r • p.coeff k = 0
  rw [hp k hk, smul_zero]

theorem degreeLE_sum {ι : Type*} (s : Finset ι) (f : ι → PolynomialModule ℚ M)
    (n : ℕ) (h : ∀ i ∈ s, DegreeLE (f i) n) : DegreeLE (∑ i ∈ s, f i) n := by
  intro k hk
  simp only [coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i hi ↦ h i hi k hk

/-- A supported coefficient lies below a coefficientwise degree bound. -/
theorem DegreeLE.le_of_mem_support {p : PolynomialModule ℚ M} {n i : ℕ}
    (hp : DegreeLE p n) (hi : i ∈ p.coeff.support) : i ≤ n := by
  by_contra hn
  exact Finsupp.mem_support_iff.mp hi (hp i (by lia))

/-- Taking a zero-constant primitive increases the auxiliary degree by at most one. -/
theorem DegreeLE.integralZero {p : PolynomialModule ℚ M} {n : ℕ}
    (hp : DegreeLE p n) : DegreeLE (integralZero p) (n + 1) := by
  change DegreeLE (p.coeff.sum fun i m ↦ (i + 1 : ℚ)⁻¹ • single ℚ (i + 1) m) (n + 1)
  apply degreeLE_sum
  intro i hi
  exact (degreeLE_single _ (by have := hp.le_of_mem_support hi; lia)).smul _

end PolynomialModule
