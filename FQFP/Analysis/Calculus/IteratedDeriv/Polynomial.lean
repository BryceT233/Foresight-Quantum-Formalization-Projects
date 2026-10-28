/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Calculus.IteratedDeriv.Asymptotics
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivatives and vanishing coefficients of algebra-valued polynomials

Coefficients of a polynomial are recovered by derivatives at zero, without commutativity.

## Main results

* `TrotterError.contDiff_algebraMap`.
* `TrotterError.contDiff_algebraMap_pow`.
* `TrotterError.contDiff_monomial`.
* `TrotterError.iteratedDeriv_algebraMap_pow`.
* `TrotterError.iteratedDeriv_polynomial_zero`.
* `TrotterError.polynomial_isBigO_iff_coeffs_zero`.
-/

@[expose] public section

namespace TrotterError

open NormedSpace Asymptotics Finset
open scoped Topology BigOperators ContDiff algebraMap

variable {𝔸 : Type*} [NormedRing 𝔸]

/-- The `algebraMap` embedding `ℝ → 𝔸` is smooth. -/
lemma contDiff_algebraMap [NormedAlgebra ℝ 𝔸] :
    ContDiff ℝ ∞ (fun τ : ℝ => (τ : 𝔸)) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (contDiff_smul_const (𝕜 := ℝ) (A := ℝ) (F := 𝔸) (v := (1 : 𝔸))
      : ContDiff ℝ ∞ (fun a : ℝ => a • (1 : 𝔸)))

/-- The real power monomial `τ ↦ (τ ^ k : 𝔸)` is smooth. -/
lemma contDiff_algebraMap_pow [NormedAlgebra ℝ 𝔸] (k : ℕ) :
    ContDiff ℝ ∞ (fun τ : ℝ => (τ ^ k : 𝔸)) := contDiff_algebraMap.pow k

/-- The 𝔸-monomial `τ ↦ c * (τ ^ k : 𝔸)` is smooth. -/
lemma contDiff_monomial [NormedAlgebra ℝ 𝔸]
    (c : 𝔸) (k : ℕ) :
    ContDiff ℝ ∞ (fun τ : ℝ => c * (τ ^ k : 𝔸)) :=
  contDiff_const.mul (contDiff_algebraMap_pow (𝔸 := 𝔸) k)

/-- The `n`-th iterated derivative of `τ ↦ (τ : 𝔸) ^ m` is
`(m.descFactorial n : ℝ) • (x : 𝔸) ^ (m - n)`. -/
lemma iteratedDeriv_algebraMap_pow [NormedAlgebra ℝ 𝔸]
    (m n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun τ : ℝ => (τ : 𝔸) ^ m) x =
      (m.descFactorial n : ℝ) • (x : 𝔸) ^ (m - n) := by
  have hfun : (fun τ : ℝ => (τ : 𝔸) ^ m) = fun τ : ℝ => (τ ^ m : ℝ) • (1 : 𝔸) := by
    funext τ
    rw [← map_pow, ← Algebra.algebraMap_eq_smul_one]
  rw [hfun]
  rw [iteratedDeriv_smul_const (𝕜 := ℝ) (𝔸 := ℝ) (F := 𝔸) (f := fun τ : ℝ => τ ^ m)
    (by fun_prop) (1 : 𝔸)]
  rw [iteratedDeriv_pow, mul_smul, ← Algebra.algebraMap_eq_smul_one, map_pow]

/-- The `j`-th iterated derivative at `0` of the degree-`< p` polynomial
`τ ↦ ∑_{k < p} T k · τ^k` equals `(j! : ℝ) • T j`: only the `k = j` monomial survives. -/
lemma iteratedDeriv_polynomial_zero [NormedAlgebra ℝ 𝔸]
    (p : ℕ) (T : ℕ → 𝔸) (j : ℕ) (hj : j < p) :
    iteratedDeriv j (fun τ : ℝ => ∑ k ∈ Finset.range p, T k * (τ ^ k : 𝔸)) 0 =
      (Nat.factorial j : ℝ) • T j := by
  have hmonoAt : ∀ k : ℕ, ContDiffAt ℝ j (fun τ : ℝ => T k * (τ ^ k : 𝔸)) 0 := fun k =>
    (contDiff_monomial (T k) k).contDiffAt.of_le (mod_cast le_top)
  have hpowAt : ∀ k : ℕ, ContDiffAt ℝ j (fun τ : ℝ => (τ ^ k : 𝔸)) 0 := fun k =>
    contDiff_algebraMap_pow (𝔸 := 𝔸) k |>.contDiffAt.of_le (mod_cast le_top)
  calc
    iteratedDeriv j (fun τ : ℝ => ∑ k ∈ Finset.range p, T k * (τ ^ k : 𝔸)) 0
        = ∑ k ∈ Finset.range p, iteratedDeriv j (fun τ : ℝ => T k * (τ ^ k : 𝔸)) 0 :=
            iteratedDeriv_fun_sum (I := Finset.range p) (fun k _ => hmonoAt k)
    _ = ∑ k ∈ Finset.range p, T k * iteratedDeriv j (fun τ : ℝ => (τ ^ k : 𝔸)) 0 := by
            apply Finset.sum_congr rfl
            intro k _
            exact iteratedDeriv_const_mul (T k) (hpowAt k)
    _ = ∑ k ∈ Finset.range p, T k * ((k.descFactorial j : ℝ) • (0 : 𝔸) ^ (k - j)) := by
            apply Finset.sum_congr rfl
            intro k _
            have h : iteratedDeriv j (fun τ : ℝ => (τ ^ k : 𝔸)) 0 =
                (k.descFactorial j : ℝ) • (0 : 𝔸) ^ (k - j) := by
              simpa using iteratedDeriv_algebraMap_pow (𝔸 := 𝔸) k j 0
            exact congrArg (fun z => T k * z) h
    _ = (Nat.factorial j : ℝ) • T j := by
            have hsingle : (∑ k ∈ Finset.range p,
                T k * ((k.descFactorial j : ℝ) • (0 : 𝔸) ^ (k - j))) =
                T j * ((j.descFactorial j : ℝ) • (0 : 𝔸) ^ (j - j)) := by
              refine Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj) ?_
              intro k hk hkj
              rcases lt_trichotomy k j with hlt | heq | hgt
              · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
              · exact False.elim (hkj heq)
              · simp [zero_pow (Nat.sub_pos_of_lt hgt).ne']
            rw [hsingle, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_smul_comm, mul_one]

/-- A polynomial `Σ_{j < p} T j · τ^j` (coefficients `T j : 𝔸`, degree `< p`) is `O(τ^p)`
at `0` iff all its coefficients vanish (the order-condition cancellation step of the paper's
main theorem, theory.tex:258-264). -/
theorem polynomial_isBigO_iff_coeffs_zero [NormedAlgebra ℝ 𝔸]
    (p : ℕ) (T : ℕ → 𝔸) :
    (fun τ : ℝ => ‖∑ j ∈ Finset.range p, T j * (τ ^ j : 𝔸)‖) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) ↔
      ∀ j : ℕ, j < p → T j = 0 := by
  let poly : ℝ → 𝔸 := fun τ => ∑ j ∈ Finset.range p, T j * (τ ^ j : 𝔸)
  have hpoly_smooth : ContDiff ℝ ∞ poly := ContDiff.sum (fun j _ => contDiff_monomial (T j) j)
  constructor
  · intro hbig
    have hvan : ∀ j < p, iteratedDeriv j poly 0 = 0 :=
      (isBigO_norm_iff_iteratedDeriv_lt_eq_zero poly p hpoly_smooth).mp hbig
    intro j hj
    have hfac : (Nat.factorial j : ℝ) • T j = 0 := by
      rw [← iteratedDeriv_polynomial_zero p T j hj]
      exact hvan j hj
    have hfac_nz : (Nat.factorial j : ℝ) ≠ 0 := by positivity
    calc
      T j = ((Nat.factorial j : ℝ)⁻¹ : ℝ) • ((Nat.factorial j : ℝ) • T j) := by
              rw [smul_smul, inv_mul_cancel₀ hfac_nz, one_smul]
      _ = ((Nat.factorial j : ℝ)⁻¹ : ℝ) • (0 : 𝔸) := by rw [hfac]
      _ = 0 := smul_zero _
  · intro hT
    have hzero : (fun _ : ℝ => (0 : ℝ)) =O[𝓝 (0 : ℝ)] (fun τ : ℝ => τ ^ p) := by
      refine IsBigO.of_bound 0 ?_
      filter_upwards with τ
      simp
    have hpoly : (fun τ : ℝ => ‖∑ j ∈ Finset.range p, T j * (τ ^ j : 𝔸)‖) = fun _ => (0 : ℝ) := by
      funext τ
      have hsum : (∑ j ∈ Finset.range p, T j * (τ ^ j : 𝔸)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hT j (Finset.mem_range.mp hj), zero_mul]
      simp [hsum]
    simpa [hpoly] using hzero

end TrotterError
