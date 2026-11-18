/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Pure
public import FQFP.CQM.Qudit.State.Spectral.OperatorSqrt

/-!
# Support inclusion for density operators

Absolute continuity means support inclusion, equivalently reverse inclusion of kernels.
These definitions do not depend on entropy or on any choice of eigenbasis.

## Main definitions and results

* `Qudit.Density.support`: the range of a density operator.
* `Qudit.Density.AbsolutelyContinuous`: support inclusion via reverse inclusion of kernels.
* `Qudit.Density.absolutelyContinuous_iff_support_le`: equivalence of the two support conditions.
* `Qudit.Density.absolutelyContinuous_map_iff`: isometries preserve and reflect support inclusion.
-/

@[expose] public section

namespace Qudit.Density

open scoped BigOperators
open CategoryTheory DaggerCategory

variable {H : Qudit}

/-- The support of a density operator is its range. -/
def support (ρ : Density H) : Submodule ℂ H.state := LinearMap.range ρ.op

/-- A positive observable has zero expectation exactly when it annihilates the state's support. -/
lemma expectation_eq_zero_iff (ρ : Density H) {A : Operator H} (hA : A.IsPositive) :
    ρ.expectation A = 0 ↔ ρ.support ≤ LinearMap.ker A := by
  rw [support, LinearMap.range_le_ker_iff, ← Module.End.mul_eq_comp]
  change (A * ρ.op).trace.re = 0 ↔ A * ρ.op = 0
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  obtain ⟨v, hv⟩ := Operator.exists_sum_outer_of_isPositive ρ.op ρ.positive
  rw [hv, Finset.mul_sum] at h ⊢
  simp only [map_sum, Operator.trace_mul_outer, Complex.re_sum] at h
  have hz (i) : A (v i) = 0 :=
    (A.apply_eq_zero_iff_re_inner_eq_zero hA _).mpr
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hA.re_inner_nonneg_right (v j))).mp h i
        (Finset.mem_univ i))
  ext x
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Operator.outer_apply, map_smul, hz,
    smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/-- An observable bounded above by one has expectation one exactly when it fixes the support. -/
lemma expectation_eq_one_iff (ρ : Density H) {A : Operator H} (hA : A ≤ 1) :
    ρ.expectation A = 1 ↔ ρ.support ≤ LinearMap.ker (1 - A) := by
  rw [← ρ.expectation_eq_zero_iff (LinearMap.le_def.mp hA), expectation_sub, expectation_one,
    sub_eq_zero, eq_comm]

/-- Quantum absolute continuity, expressed by reverse inclusion of kernels. -/
def AbsolutelyContinuous (ρ σ : Density H) : Prop := LinearMap.ker σ.op ≤ LinearMap.ker ρ.op

/-- For density operators, absolute continuity is exactly inclusion of supports. -/
lemma absolutelyContinuous_iff_support_le (ρ σ : Density H) :
    ρ.AbsolutelyContinuous σ ↔ ρ.support ≤ σ.support := by
  have hρ : (LinearMap.ker ρ.op)ᗮ = ρ.support := by
    rw [LinearMap.orthogonal_ker, ρ.positive.adjoint_eq]
    rfl
  have hσ : (LinearMap.ker σ.op)ᗮ = σ.support := by
    rw [LinearMap.orthogonal_ker, σ.positive.adjoint_eq]
    rfl
  rw [AbsolutelyContinuous, ← hρ, ← hσ]
  exact ⟨Submodule.orthogonal_le, fun h => by
    simpa using Submodule.orthogonal_le h⟩

/-- Every state is absolutely continuous with respect to itself. -/
@[refl]
lemma AbsolutelyContinuous.refl (ρ : Density H) : ρ.AbsolutelyContinuous ρ := le_rfl

/-- Absolute continuity is transitive. -/
lemma AbsolutelyContinuous.trans {ρ σ τ : Density H}
    (hρσ : ρ.AbsolutelyContinuous σ) (hστ : σ.AbsolutelyContinuous τ) :
    ρ.AbsolutelyContinuous τ := le_trans hστ hρσ

/-- A zero reference eigenvalue cannot overlap a positive source eigenvalue. -/
lemma AbsolutelyContinuous.eigenvalue_mul_overlap_eq_zero {ρ σ : Density H}
    (h : ρ.AbsolutelyContinuous σ) (i j : Fin (Module.finrank ℂ H.state))
    (hj : σ.eigenvalue j = 0) :
    ρ.eigenvalue i * ‖inner ℂ (σ.eigenbasis j) (ρ.eigenbasis i)‖ ^ 2 = 0 := by
  have hz : ρ.op (σ.eigenbasis j) = 0 :=
    h (by simp [LinearMap.mem_ker, σ.apply_eigenbasis, hj])
  have he := ρ.positive.isSymmetric (σ.eigenbasis j) (ρ.eigenbasis i)
  rw [hz, inner_zero_left, ρ.apply_eigenbasis, inner_smul_right] at he
  rcases mul_eq_zero.mp he.symm with hi | hi
  · simp [Complex.ofReal_eq_zero.mp hi]
  · simp [hi]

/-- Support inclusion can be checked on the zero eigenvectors of any reference eigenbasis. -/
lemma absolutelyContinuous_iff_of_right_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (b : OrthonormalBasis ι ℂ H.state) (q : ι → ℝ)
    (hσ : ∀ i, σ.op (b i) = (q i : ℂ) • b i) :
    ρ.AbsolutelyContinuous σ ↔ ∀ i, q i = 0 → ρ.op (b i) = 0 := by
  constructor
  · intro h i hi
    exact h (by simp [LinearMap.mem_ker, hσ, hi])
  · intro h v hv
    change σ.op v = 0 at hv
    change ρ.op v = 0
    have hc (i) : (q i : ℂ) * inner ℂ (b i) v = 0 := by
      have he := σ.positive.isSymmetric (b i) v
      simpa only [hσ, hv, inner_smul_left, inner_zero_right, Complex.conj_ofReal] using he
    calc
      ρ.op v = ρ.op (∑ i, inner ℂ (b i) v • b i) :=
        congrArg ρ.op (b.sum_repr' v).symm
      _ = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [map_smul]
        rcases mul_eq_zero.mp (hc i) with hi | hi
        · rw [h i (Complex.ofReal_eq_zero.mp hi), smul_zero]
        · rw [hi, zero_smul]

/-- In a common orthonormal eigenbasis, support inclusion is scalar absolute continuity. -/
lemma absolutelyContinuous_iff_of_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (b : OrthonormalBasis ι ℂ H.state) (p q : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hσ : ∀ i, σ.op (b i) = (q i : ℂ) • b i) :
    ρ.AbsolutelyContinuous σ ↔ ∀ i, q i = 0 → p i = 0 := by
  rw [absolutelyContinuous_iff_of_right_eigenbasis ρ σ b q hσ]
  have hb (i) : b i ≠ 0 := b.toBasis.ne_zero i
  simp only [hρ, smul_eq_zero, hb, or_false, Complex.ofReal_eq_zero]

/-- Every state is absolutely continuous with respect to the maximally mixed state. -/
lemma absolutelyContinuous_maximallyMixed (ρ : Density H)
    (hn : Module.finrank ℂ H.state ≠ 0) : ρ.AbsolutelyContinuous (maximallyMixed H hn) := by
  intro v hv
  change (maximallyMixed H hn).op v = 0 at hv
  simp only [op_maximallyMixed, LinearMap.smul_apply, Module.End.one_apply, smul_eq_zero,
    inv_eq_zero, Nat.cast_eq_zero, hn, false_or] at hv
  simp [hv]

/-- A state supported on a pure state must equal that pure state. -/
lemma absolutelyContinuous_pure_iff (ρ : Density H) (ψ : UnitState H) :
    ρ.AbsolutelyContinuous (pure ψ) ↔ ρ = pure ψ := by
  rw [absolutelyContinuous_iff_support_le]
  change LinearMap.range ρ.op ≤ LinearMap.range (pure ψ).op ↔ _
  rw [range_pure]
  exact ⟨ρ.eq_pure_of_range_le ψ, fun h => by rw [h, range_pure]⟩

/-- Isometric embeddings preserve and reflect absolute continuity. -/
lemma absolutelyContinuous_map_iff {K : Qudit} (ρ σ : Density H)
    (U : H ⟶ K) [IsIsometry U] :
    (ρ.map U).AbsolutelyContinuous (σ.map U) ↔ ρ.AbsolutelyContinuous σ := by
  constructor
  · intro h v hz
    have he : U.hom (ρ.op v) = 0 := by
      have he := h (x := U.hom v)
      simpa only [LinearMap.mem_ker, op_map, LinearMap.comp_apply,
        hom_adjoint_apply_of_isIsometry, hz, map_zero]
        using he (by simp [LinearMap.mem_ker, hom_adjoint_apply_of_isIsometry,
          show σ.op v = 0 from hz])
    exact (hom_injective_of_isIsometry U) (he.trans U.hom.map_zero.symm)
  · intro h v hz
    have he : σ.op (U.hom.adjoint v) = 0 :=
      (hom_injective_of_isIsometry U) (hz.trans U.hom.map_zero.symm)
    change U.hom (ρ.op (U.hom.adjoint v)) = 0
    rw [show ρ.op (U.hom.adjoint v) = 0 from h he, map_zero]

/-- Every component of positive weight is supported on its binary mixture. -/
lemma absolutelyContinuous_mix_left (ρ σ : Density H) (p : ℝ)
    (hp : 0 < p) (hp₁ : p ≤ 1) : ρ.AbsolutelyContinuous (mix p hp.le hp₁ ρ σ) := by
  intro v hv
  change (mix p hp.le hp₁ ρ σ).op v = 0 at hv
  have he := congrArg (fun x => (inner ℂ v x).re) hv
  simp only [op_mix, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, inner_zero_right, Complex.zero_re] at he
  apply (ρ.op.apply_eq_zero_iff_re_inner_eq_zero ρ.positive v).mpr
  have hρ := ρ.positive.re_inner_nonneg_right v
  have hσ := σ.positive.re_inner_nonneg_right v
  change 0 ≤ (inner ℂ v (ρ.op v)).re at hρ
  change 0 ≤ (inner ℂ v (σ.op v)).re at hσ
  nlinarith [mul_nonneg (sub_nonneg.mpr hp₁) hσ]

/-- The second component is supported on a binary mixture whenever its weight is positive. -/
lemma absolutelyContinuous_mix_right (ρ σ : Density H) (p : ℝ)
    (hp₀ : 0 ≤ p) (hp : p < 1) : σ.AbsolutelyContinuous (mix p hp₀ hp.le ρ σ) := by
  rw [mix_comm]
  exact σ.absolutelyContinuous_mix_left ρ (1 - p) (sub_pos.mpr hp) (by linarith)

end Qudit.Density
