/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
Physlib reference for pure-state equality, rank and mixtures of pure ensembles.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean

QuantumInfo/States/Ensemble.lean
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Spectral.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pure states and ensembles

`Density.IsPure` means representation by a unit vector. It is equivalent to the underlying
operator having a one-dimensional range, or to matrix rank one in any orthonormal basis.
Equality of pure density operators is equality of unit vectors up to global phase.
A pure ensemble mixes to a pure state exactly when every positive-weight component
has that same density operator. Zero-weight components remain unrestricted.
These are coordinate-free versions of physlib's `MState.pure_eq_pure_iff` and
`Ensemble.mix_pEnsemble_pure_iff_pure`, together with `MState.pure_iff_rank_eq_one`.

## Main definitions and results

* `Qudit.Density.IsPure`: densities arising from unit vectors.
* `Qudit.Density.isPure_iff_finrank_range_eq_one`: purity is equivalent to operator rank one.
* `Qudit.Density.pure_eq_pure_iff`: pure vectors determine the same density exactly up to phase.
* `Qudit.Ensemble.mix_ofPure_eq_pure_iff`: purity of a mixture of pure states.
-/

@[expose] public section

open scoped BigOperators

namespace Qudit

noncomputable section

variable {H : Qudit}

namespace Density

/-- A density operator is pure if it comes from a unit vector, without choosing its phase. -/
def IsPure (ρ : Density H) : Prop := ∃ v : UnitState H, ρ = pure v

/-- The density operator of a unit vector is pure. -/
lemma isPure_pure (v : UnitState H) : (pure v).IsPure := ⟨v, rfl⟩

/-- The range of a pure density operator is the line spanned by its unit vector. -/
lemma range_pure (v : UnitState H) :
    LinearMap.range (pure v).op = Submodule.span ℂ {v.val} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v.val))
  · apply Submodule.span_le.mpr
    rintro _ ⟨rfl⟩
    exact ⟨v.val, by simp only [pure_apply, v.inner_self, one_smul]⟩

/-- A pure density operator has a one-dimensional range. -/
lemma finrank_range_pure (v : UnitState H) :
    Module.finrank ℂ (LinearMap.range (pure v).op) = 1 := by
  rw [range_pure]
  exact finrank_span_singleton v.ne_zero

/-- A density operator supported on the line of a unit vector is its pure density operator. -/
lemma eq_pure_of_range_le (ρ : Density H) (v : UnitState H)
    (h : LinearMap.range ρ.op ≤ Submodule.span ℂ {v.val}) : ρ = pure v := by
  have hp : (pure v).op * ρ.op = ρ.op := by
    ext x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (h (LinearMap.mem_range_self ρ.op x))
    simp only [mul_apply_eq_comp, ← hc, pure_apply, inner_smul_right,
      v.inner_self, mul_one]
  have hq : ρ.op * (pure v).op = ρ.op := by
    have := congrArg LinearMap.adjoint hp
    simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, adjoint_op] using this
  have ho : ρ.op = Operator.outer (ρ.op v.val) v.val := by
    rw [← Operator.mul_outer, ← op_pure, hq]
  have ht : inner ℂ v.val (ρ.op v.val) = 1 := by
    rw [← Operator.trace_outer, ← ho, ρ.trace_one]
  have hv : ρ.op v.val = v.val := by
    have := congrArg (fun A : Operator H => A v.val) hp
    simpa only [mul_apply_eq_comp, pure_apply, ht, one_smul] using this.symm
  apply Density.ext
  rw [ho, hv, op_pure]

/-- A density operator is pure exactly when its range has dimension one. -/
lemma isPure_iff_finrank_range_eq_one (ρ : Density H) :
    ρ.IsPure ↔ Module.finrank ℂ (LinearMap.range ρ.op) = 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact finrank_range_pure v
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, ρ.eigenvalue i ≠ 0 := by
      by_contra! hz
      have hs := ρ.sum_eigenvalue
      simp only [hz, Finset.sum_const_zero] at hs
      exact zero_ne_one hs
    let v := UnitState.ofBasis ρ.eigenbasis i
    have hv : v.val ∈ LinearMap.range ρ.op := by
      refine ⟨(ρ.eigenvalue i : ℂ)⁻¹ • v.val, ?_⟩
      change ρ.op ((ρ.eigenvalue i : ℂ)⁻¹ • ρ.eigenbasis i) = ρ.eigenbasis i
      rw [map_smul, apply_eigenbasis, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hi),
        one_smul]
    refine ⟨v, eq_pure_of_range_le ρ v ?_⟩
    exact (eq_span_singleton_of_mem_of_finrank_eq_one h hv v.ne_zero).le

/-- The matrix rank of a density operator equals the dimension of its range in any basis. -/
lemma rank_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Density H) (b : OrthonormalBasis ι ℂ H.state) :
    (ρ.toMatrix b).rank = Module.finrank ℂ (LinearMap.range ρ.op) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ b.toBasis b.toBasis]
  change Module.finrank ℂ (LinearMap.range
    (Matrix.toLin b.toBasis b.toBasis (LinearMap.toMatrix b.toBasis b.toBasis ρ.op))) = _
  rw [Matrix.toLin_toMatrix]

/-- Purity is equivalent to matrix rank one in every orthonormal coordinate system. -/
lemma isPure_iff_rank_toMatrix_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Density H) (b : OrthonormalBasis ι ℂ H.state) :
    ρ.IsPure ↔ (ρ.toMatrix b).rank = 1 := by
  rw [rank_toMatrix, isPure_iff_finrank_range_eq_one]

/-- Equal pure density operators are represented by unit vectors differing by a phase. -/
lemma pure_eq_pure_iff (v w : UnitState H) :
    pure v = pure w ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ v.val = c • w.val := by
  constructor
  · intro h
    have hv : v.val = inner ℂ w.val v.val • w.val := by
      have he := congrArg (fun ρ : Density H => ρ.op v.val) h
      simpa only [pure_apply, v.inner_self, one_smul] using he
    refine ⟨inner ℂ w.val v.val, ?_, hv⟩
    have hn := congrArg norm hv
    simpa only [norm_smul, v.norm_eq_one, w.norm_eq_one, mul_one] using hn.symm
  · rintro ⟨c, hc, hv⟩
    apply Density.ext
    simpa only [op_pure, hv] using Operator.outer_smul_self_of_norm_eq_one c hc w.val

/-- The overlap of two pure states is the squared modulus of their vector inner product. -/
lemma expectation_pure_pure (v w : UnitState H) :
    (pure v).expectation (pure w).op = ‖inner ℂ w.val v.val‖ ^ 2 := by
  rw [expectation_pure, pure_apply, inner_smul_right, ← inner_conj_symm v.val w.val,
    Complex.mul_conj']
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- A pure-state overlap is at most one. -/
lemma expectation_pure_pure_le_one (v w : UnitState H) :
    (pure v).expectation (pure w).op ≤ 1 := by
  rw [expectation_pure_pure]
  have h := norm_inner_le_norm (𝕜 := ℂ) w.val v.val
  rw [v.norm_eq_one, w.norm_eq_one, one_mul] at h
  nlinarith [norm_nonneg (inner ℂ w.val v.val)]

/-- Overlap one characterizes equality of pure density operators, including global phase. -/
lemma expectation_pure_pure_eq_one_iff (v w : UnitState H) :
    (pure v).expectation (pure w).op = 1 ↔ pure v = pure w := by
  constructor
  · intro h
    rw [expectation_pure_pure] at h
    have hn : ‖inner ℂ w.val v.val‖ = ‖w.val‖ * ‖v.val‖ := by
      rw [w.norm_eq_one, v.norm_eq_one, one_mul]
      nlinarith [norm_nonneg (inner ℂ w.val v.val)]
    obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff w.ne_zero v.ne_zero).mp hn
    apply (pure_eq_pure_iff v w).mpr
    refine ⟨c, ?_, hc⟩
    have := congrArg norm hc
    simpa only [norm_smul, v.norm_eq_one, w.norm_eq_one, mul_one] using this.symm
  · intro h
    rw [h, expectation_pure_pure, w.inner_self]
    simp

end Density

namespace Ensemble

/-- A pure mixture has no distinct positive-weight pure components. -/
lemma mix_ofPure_eq_pure_iff {ι : Type*} [Fintype ι]
    (w : Convexity.StdSimplex ℝ ι) (v : ι → UnitState H) (ψ : UnitState H) :
    (ofPure w v).mix = Density.pure ψ ↔
      ∀ i, w.weights i ≠ 0 → Density.pure (v i) = Density.pure ψ := by
  constructor
  · intro h i hi
    have hs : ∑ j, w.weights j * (Density.pure (v j)).expectation (Density.pure ψ).op = 1 := by
      have he := congrArg (fun ρ : Density H => ρ.expectation (Density.pure ψ).op) h
      simpa only [expectation_mix, ofPure, weight, Density.expectation_pure_pure,
        ψ.inner_self, norm_one, one_pow] using he
    apply (Density.expectation_pure_pure_eq_one_iff (v i) ψ).mp
    by_contra hn
    have hlt : ∑ j, w.weights j * (Density.pure (v j)).expectation (Density.pure ψ).op <
        ∑ j, w.weights j := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_of_le_one_right (w.weights_nonneg j)
          (Density.expectation_pure_pure_le_one (v j) ψ)
      · exact ⟨i, Finset.mem_univ i, mul_lt_of_lt_one_right
          (lt_of_le_of_ne (w.weights_nonneg i) (Ne.symm hi))
          (lt_of_le_of_ne (Density.expectation_pure_pure_le_one (v i) ψ) hn)⟩
    rw [hs, w.total_of_fintype] at hlt
    exact (lt_irrefl _ hlt)
  · intro h
    apply Density.ext
    rw [op_mix]
    calc
      _ = ∑ i, (w.weights i : ℂ) • (Density.pure ψ).op := by
        apply Finset.sum_congr rfl
        intro i _
        change (w.weights i : ℂ) • (Density.pure (v i)).op = _
        by_cases hi : w.weights i = 0
        · simp only [hi, Complex.ofReal_zero, zero_smul]
        · rw [h i hi]
      _ = _ := by rw [← Finset.sum_smul, ← Complex.ofReal_sum,
          w.total_of_fintype, Complex.ofReal_one, one_smul]

end Ensemble

end

end Qudit
