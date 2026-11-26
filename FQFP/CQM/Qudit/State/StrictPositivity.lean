/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean: positive definiteness under tensor products,
relabeling and convex mixtures, for the uniform state and in dimension one.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Spectral.Tensor
public import FQFP.CQM.Qudit.State.Support
public import Mathlib.Algebra.Algebra.StrictPositivity

/-!
# Strictly positive density operators

A density has full support exactly when its least eigenvalue is positive. Full support is
preserved by tensor products and by mixtures in which a full-support component has positive weight.
-/

public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.Density

variable {H K : Qudit}

/-- A density operator is strictly positive exactly when its support is the entire space. -/
theorem isStrictlyPositive_iff_support_eq_top (ρ : Density H) :
    IsStrictlyPositive ρ.op ↔ ρ.support = ⊤ := by
  rw [IsStrictlyPositive.iff_of_unital, and_iff_right (LinearMap.nonneg_iff_isPositive.mpr
    ρ.positive), LinearMap.isUnit_iff_range_eq_top, support]

/-- Strict positivity is equivalent to a positive least eigenvalue. -/
theorem isStrictlyPositive_iff_sInf_realSpectrum_pos (ρ : Density H) :
    IsStrictlyPositive ρ.op ↔ 0 < sInf (_root_.spectrum ℝ ρ.op) := by
  obtain ⟨i, hi⟩ := ρ.exists_isLeast_eigenvalue
  rw [hi.csInf_eq, IsStrictlyPositive.iff_of_unital,
    and_iff_right (LinearMap.nonneg_iff_isPositive.mpr ρ.positive), ← spectrum.zero_notMem_iff ℝ]
  constructor
  · intro h
    exact (ρ.eigenvalue_nonneg i).lt_of_ne fun he => h (he ▸ hi.1)
  · exact fun hp hz => (hp.trans_le (hi.2 hz)).false

/-- A tensor product has full support exactly when both factors do. -/
theorem isStrictlyPositive_tensor_iff (ρ : Density H) (σ : Density K) :
    IsStrictlyPositive (ρ.tensor σ).op ↔ IsStrictlyPositive ρ.op ∧ IsStrictlyPositive σ.op := by
  obtain ⟨i, hi⟩ := ρ.exists_isLeast_eigenvalue
  obtain ⟨j, hj⟩ := σ.exists_isLeast_eigenvalue
  simp only [isStrictlyPositive_iff_sInf_realSpectrum_pos, sInf_realSpectrum_tensor,
    hi.csInf_eq, hj.csInf_eq, mul_pos_iff, not_lt.mpr (ρ.eigenvalue_nonneg i), false_and,
    or_false]

/-- Unitary transport preserves and reflects strict positivity. -/
theorem isStrictlyPositive_map_unitary_iff (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    IsStrictlyPositive (ρ.map U).op ↔ IsStrictlyPositive ρ.op := by
  rw [isStrictlyPositive_iff_sInf_realSpectrum_pos, realSpectrum_map_unitary,
    isStrictlyPositive_iff_sInf_realSpectrum_pos]

/-- Support inclusion propagates full support from the smaller state to the larger one. -/
theorem AbsolutelyContinuous.isStrictlyPositive {ρ σ : Density H} (h : ρ.AbsolutelyContinuous σ)
    (hρ : IsStrictlyPositive ρ.op) : IsStrictlyPositive σ.op := by
  rw [isStrictlyPositive_iff_support_eq_top] at hρ ⊢
  exact top_unique (hρ ▸ (ρ.absolutelyContinuous_iff_support_le σ).mp h)

/-- A positive weight on a strictly positive first state suffices for a full-support mixture. -/
theorem isStrictlyPositive_mix_left {ρ : Density H} (σ : Density H) {p : ℝ}
    (hp : 0 < p) (hp₁ : p ≤ 1) (hρ : IsStrictlyPositive ρ.op) :
    IsStrictlyPositive (mix p hp.le hp₁ ρ σ).op :=
  (ρ.absolutelyContinuous_mix_left σ p hp hp₁).isStrictlyPositive hρ

/-- A positive weight on a strictly positive second state suffices for a full-support mixture. -/
theorem isStrictlyPositive_mix_right (ρ : Density H) {σ : Density H} {p : ℝ}
    (hp₀ : 0 ≤ p) (hp : p < 1) (hσ : IsStrictlyPositive σ.op) :
    IsStrictlyPositive (mix p hp₀ hp.le ρ σ).op :=
  (ρ.absolutelyContinuous_mix_right σ p hp₀ hp).isStrictlyPositive hσ

/-- Mixtures of strictly positive states are strictly positive, including at the endpoints. -/
theorem isStrictlyPositive_mix {ρ σ : Density H} (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hρ : IsStrictlyPositive ρ.op) (hσ : IsStrictlyPositive σ.op) :
    IsStrictlyPositive (mix p hp₀ hp₁ ρ σ).op := by
  rcases hp₀.eq_or_lt with rfl | hp
  · simpa only [mix_zero] using hσ
  · exact isStrictlyPositive_mix_left σ hp hp₁ hρ

/-- The maximally mixed state is strictly positive in every positive dimension. -/
theorem isStrictlyPositive_maximallyMixed (H : Qudit) (hd : Module.finrank ℂ H.state ≠ 0) :
    IsStrictlyPositive (maximallyMixed H hd).op := by
  apply IsUnit.isStrictlyPositive _ (LinearMap.nonneg_iff_isPositive.mpr
    (maximallyMixed H hd).positive)
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  simp [op_maximallyMixed, hd]

/-- A trace-one state on a one-dimensional system has full support. -/
theorem isStrictlyPositive_of_finrank_eq_one (ρ : Density H) (hd : Module.finrank ℂ H.state = 1) :
    IsStrictlyPositive ρ.op := by
  rw [isStrictlyPositive_iff_support_eq_top, support, LinearMap.range_eq_top]
  exact surjective_of_ne_zero_of_finrank_eq_one hd ρ.op_ne_zero

end Qudit.Density
