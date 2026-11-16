/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Error.Fidelity
public import FQFP.CQM.Qudit.Error.Channel
public import FQFP.Analysis.InnerProductSpace.TraceNormBounds

/-!
# Fidelity and trace distance

The Fuchs–van de Graaf inequalities use the existing unsquared fidelity and
half-trace-norm distance: `1 - F ≤ D ≤ sqrt (1 - F²)`.
The lower bound follows from the positive square-root estimate; the upper bound
uses Uhlmann attainment and contractivity under partial trace.
See Watrous, *The Theory of Quantum Information*, Theorem 3.33 and Lemma 3.34.

## Main results

* `Qudit.Density.one_sub_fidelity_le_traceDistance`: the lower Fuchs–van de Graaf inequality.
* `Qudit.Density.traceDistance_le_sqrt_one_sub_fidelity_sq`: the upper Fuchs–van de Graaf
  inequality.
* `Qudit.Density.traceDistance_pure_pure`: the exact trace-distance formula for pure states.
* `Qudit.Density.traceDistance_sq_add_fidelity_sq_le_one`: the square-root-free upper bound.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped ComplexOrder

namespace Qudit

noncomputable section

namespace Density

variable {H : Qudit}

/-- The lower **Fuchs–van de Graaf bound**, with unsquared fidelity. -/
theorem one_sub_fidelity_le_traceDistance (ρ σ : Density H) :
    1 - ρ.fidelity σ ≤ ρ.traceDistance σ := by
  have h := ρ.op.sqrt_positive.re_trace_sub_mul_self_le_traceNorm σ.op.sqrt_positive
  rw [ρ.op.sqrt_mul_sqrt ρ.positive, σ.op.sqrt_mul_sqrt σ.positive] at h
  have ht : LinearMap.trace ℂ H.state
      ((ρ.op.sqrt - σ.op.sqrt) * (ρ.op.sqrt - σ.op.sqrt)) =
      2 - 2 * LinearMap.trace ℂ H.state (ρ.op.sqrt * σ.op.sqrt) := by
    rw [sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
      ρ.op.sqrt_mul_sqrt ρ.positive, σ.op.sqrt_mul_sqrt σ.positive,
      LinearMap.trace_mul_comm ℂ σ.op.sqrt ρ.op.sqrt,
      show LinearMap.trace ℂ H.state ρ.op = 1 from ρ.trace_one,
      show LinearMap.trace ℂ H.state σ.op = 1 from σ.trace_one]
    ring
  rw [ht] at h
  have hf : (LinearMap.trace ℂ H.state (ρ.op.sqrt * σ.op.sqrt)).re ≤ ρ.fidelity σ :=
    (Complex.re_le_norm _).trans (LinearMap.norm_trace_le_traceNorm _)
  simp only [Complex.sub_re, Complex.mul_re] at h
  norm_num at h
  dsimp only [traceDistance]
  linarith

/-- The difference of two pure densities satisfies a cubic polynomial determined by
their squared overlap. -/
lemma pure_sub_mul_self_mul_self (v w : UnitState H) :
    ((pure v).op - (pure w).op) * ((pure v).op - (pure w).op) *
        ((pure v).op - (pure w).op) =
      ((1 - ‖inner ℂ v.val w.val‖ ^ 2 : ℝ) : ℂ) • ((pure v).op - (pure w).op) := by
  have h (v w : UnitState H) : (pure v).op * (pure w).op * (pure v).op =
      (‖inner ℂ v.val w.val‖ ^ 2 : ℂ) • (pure v).op := by
    ext x
    simp only [Module.End.mul_apply, pure_apply, inner_smul_right, smul_smul,
      LinearMap.smul_apply]
    congr 1
    rw [← inner_conj_symm w.val v.val]
    calc
      _ = (starRingEnd ℂ (inner ℂ v.val w.val) * inner ℂ v.val w.val) *
          inner ℂ v.val x := by ring
      _ = _ := by rw [Complex.conj_mul']
  calc
    _ = (pure v).op - (pure w).op - (pure v).op * (pure w).op * (pure v).op +
        (pure w).op * (pure v).op * (pure w).op := by
      noncomm_ring [pure_mul_self v, pure_mul_self w]
    _ = _ := by
      rw [h v w, h w v, norm_inner_symm w.val v.val,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
        sub_smul, one_smul, smul_sub]
      abel

/-- The real trace of the squared difference of pure densities is twice one minus
their squared overlap. -/
lemma re_trace_pure_sub_mul_self (v w : UnitState H) :
    (LinearMap.trace ℂ H.state
      (((pure v).op - (pure w).op) * ((pure v).op - (pure w).op))).re =
      2 * (1 - ‖inner ℂ v.val w.val‖ ^ 2) := by
  rw [sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
    pure_mul_self, pure_mul_self, LinearMap.trace_mul_comm ℂ (pure w).op (pure v).op]
  have ht : LinearMap.trace ℂ H.state ((pure v).op * (pure w).op) =
      (‖inner ℂ v.val w.val‖ ^ 2 : ℂ) := by
    change Operator.trace ((pure v).op * Operator.outer w.val w.val) = _
    rw [Operator.trace_mul_outer, pure_apply, inner_smul_right,
      ← inner_conj_symm w.val v.val, Complex.mul_conj']
  rw [ht, show LinearMap.trace ℂ H.state (pure v).op = 1 from (pure v).trace_one,
    show LinearMap.trace ℂ H.state (pure w).op = 1 from (pure w).trace_one]
  simp only [← Complex.ofReal_pow, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  ring

/-- For pure states the upper **Fuchs–van de Graaf bound** is an equality. -/
theorem traceDistance_pure_pure (v w : UnitState H) :
    (pure v).traceDistance (pure w) = Real.sqrt (1 - ‖inner ℂ v.val w.val‖ ^ 2) := by
  have hn : ‖inner ℂ v.val w.val‖ ≤ 1 := by
    simpa only [v.norm_eq_one, w.norm_eq_one, one_mul] using
      norm_inner_le_norm (𝕜 := ℂ) v.val w.val
  have ht : 0 ≤ 1 - ‖inner ℂ v.val w.val‖ ^ 2 := by
    nlinarith [norm_nonneg (inner ℂ v.val w.val)]
  rcases eq_or_lt_of_le ht with h | h
  · have hf : (pure v).fidelity (pure w) = 1 := by
      rw [fidelity_pure_pure]
      nlinarith [norm_nonneg (inner ℂ v.val w.val)]
    rw [(fidelity_eq_one_iff _ _).mp hf, traceDistance_self, ← h, Real.sqrt_zero]
  · have hsym := (pure v).positive.isSymmetric.sub (pure w).positive.isSymmetric
    have he := hsym.traceNorm_mul_eq_re_trace_sq
      (Real.sqrt_nonneg (1 - ‖inner ℂ v.val w.val‖ ^ 2))
        (by
          rw [← Complex.ofReal_pow, Real.sq_sqrt ht]
          exact pure_sub_mul_self_mul_self v w)
    rw [re_trace_pure_sub_mul_self] at he
    have hs := Real.sq_sqrt ht
    have hp := Real.sqrt_pos.mpr h
    dsimp only [traceDistance]
    nlinarith

/-- The upper **Fuchs–van de Graaf bound**, with the square of unsquared fidelity. -/
theorem traceDistance_le_sqrt_one_sub_fidelity_sq (ρ σ : Density H) :
    ρ.traceDistance σ ≤ Real.sqrt (1 - ρ.fidelity σ ^ 2) := by
  obtain ⟨φ, hφ, he⟩ := ρ.exists_purification_norm_inner_eq_fidelity σ ρ.purify
    ρ.partialTraceRight_pure_purify (LinearMap.finrank_range_le σ.op)
  have h := (pure ρ.purify).traceDistance_partialTraceRight_le (pure φ)
  rwa [ρ.partialTraceRight_pure_purify, hφ, traceDistance_pure_pure, he] at h

/-- A square-root-free form of the upper bound. -/
theorem traceDistance_sq_add_fidelity_sq_le_one (ρ σ : Density H) :
    ρ.traceDistance σ ^ 2 + ρ.fidelity σ ^ 2 ≤ 1 := by
  have h := ρ.traceDistance_le_sqrt_one_sub_fidelity_sq σ
  have ht : 0 ≤ 1 - ρ.fidelity σ ^ 2 := by
    nlinarith [ρ.fidelity_nonneg σ, ρ.fidelity_le_one σ]
  have hs := Real.sq_sqrt ht
  nlinarith [ρ.traceDistance_nonneg σ]

/-- The **Fuchs–van de Graaf lower bound** expressed as a lower bound on fidelity. -/
theorem one_sub_traceDistance_le_fidelity (ρ σ : Density H) :
    1 - ρ.traceDistance σ ≤ ρ.fidelity σ := by
  linarith [ρ.one_sub_fidelity_le_traceDistance σ]

/-- The **Fuchs–van de Graaf upper bound** expressed as an upper bound on fidelity. -/
theorem fidelity_le_sqrt_one_sub_traceDistance_sq (ρ σ : Density H) :
    ρ.fidelity σ ≤ Real.sqrt (1 - ρ.traceDistance σ ^ 2) := by
  apply (Real.le_sqrt (ρ.fidelity_nonneg σ)
    (by nlinarith [ρ.traceDistance_nonneg σ, ρ.traceDistance_le_one σ])).mpr
  linarith [ρ.traceDistance_sq_add_fidelity_sq_le_one σ]

end Density

end

end Qudit
