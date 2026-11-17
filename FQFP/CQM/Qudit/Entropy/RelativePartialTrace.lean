/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.RelativeTensor
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Monotonicity of relative entropy under partial trace

Interpolate the logarithm between each source and reference eigenvalue. A quadratic
variational formula compares the derivatives before and after discarding a subsystem.
In the two eigenbases the test operator has independent matrix entries. Completing the square
in each entry gives the minimum, and lifting a test operator by tensoring with the identity
preserves its cost. Hence the minimum can only increase when a subsystem is discarded.
Support inclusion makes every term involving a zero reference eigenvalue identically zero.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

private lemma expectation_adjoint_mul (ρ : Density H) (X : Operator H) :
    ρ.expectation (X.adjoint * X) = ∑ i, ρ.eigenvalue i * ‖X (ρ.eigenbasis i)‖ ^ 2 := by
  rw [expectation, expectationComplex, Operator.trace, LinearMap.trace_eq_sum_inner _ ρ.eigenbasis]
  simp only [Module.End.mul_apply, ρ.apply_eigenbasis, map_smul, inner_smul_right,
    LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.re_sum,
    RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

private def cost (ρ σ : Density H) (t : ℝ) (X : Operator H) : ℝ :=
  (1 - t) * ρ.expectation ((1 - X).adjoint * (1 - X)) + t * σ.expectation (X * X.adjoint)

private abbrev entry (ρ σ : Density H) (X : Operator H)
    (i j : Fin (Module.finrank ℂ H.state)) : ℂ :=
  inner ℂ (σ.eigenbasis j) (X (ρ.eigenbasis i))

private lemma cost_eq_sum (ρ σ : Density H) (t : ℝ) (X : Operator H) :
    cost ρ σ t X = ∑ i, ∑ j,
      ((1 - t) * ρ.eigenvalue i * ‖entry ρ σ 1 i j - entry ρ σ X i j‖ ^ 2 +
        t * σ.eigenvalue j * ‖entry ρ σ X i j‖ ^ 2) := by
  have hσ := expectation_adjoint_mul σ X.adjoint
  rw [LinearMap.adjoint_adjoint] at hσ
  rw [cost, expectation_adjoint_mul, hσ]
  simp only [Finset.sum_add_distrib]
  congr 1
  · simp only [entry, Module.End.one_apply, ← inner_sub_right, ← Finset.mul_sum,
      σ.eigenbasis.sum_sq_norm_inner_right, LinearMap.sub_apply, mul_assoc]
  · rw [Finset.sum_comm]
    simp only [entry, ← LinearMap.adjoint_inner_left, ← Finset.mul_sum,
      ρ.eigenbasis.sum_sq_norm_inner_left, mul_assoc]

private def parallelSum (a b : ℝ) : ℝ := a * b / (a + b)

private lemma complete_square {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c x : ℂ) :
    a * ‖c - x‖ ^ 2 + b * ‖x‖ ^ 2 =
      parallelSum a b * ‖c‖ ^ 2 + (a + b) * ‖x - (↑(a / (a + b)) : ℂ) * c‖ ^ 2 := by
  by_cases hz : a + b = 0
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    simp [ha', hb', parallelSum]
  simp only [parallelSum, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  field_simp
  ring

private def minimumCost (ρ σ : Density H) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, parallelSum ((1 - t) * ρ.eigenvalue i) (t * σ.eigenvalue j) *
    ‖entry ρ σ 1 i j‖ ^ 2

private lemma minimumCost_le (ρ σ : Density H) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (X : Operator H) : minimumCost ρ σ t ≤ cost ρ σ t X := by
  rw [cost_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have ha := mul_nonneg (sub_nonneg.mpr ht.2) (ρ.eigenvalue_nonneg i)
  have hb := mul_nonneg ht.1 (σ.eigenvalue_nonneg j)
  rw [complete_square ha hb]
  exact le_add_of_nonneg_right (mul_nonneg (add_nonneg ha hb) (sq_nonneg _))

private lemma exists_cost_eq (ρ σ : Density H) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ X, cost ρ σ t X = minimumCost ρ σ t := by
  classical
  let e := LinearMap.toMatrix ρ.eigenbasis.toBasis σ.eigenbasis.toBasis
  let M : Matrix _ _ ℂ := fun j i =>
    (↑(((1 - t) * ρ.eigenvalue i) / ((1 - t) * ρ.eigenvalue i + t * σ.eigenvalue j)) : ℂ) *
      entry ρ σ 1 i j
  refine ⟨e.symm M, ?_⟩
  have hX (i j) : entry ρ σ (e.symm M) i j = M j i := by
    have h := congrFun (congrFun (e.apply_symm_apply M) j) i
    simpa [e, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, entry] using h
  rw [cost_eq_sum, minimumCost]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [complete_square (mul_nonneg (sub_nonneg.mpr ht.2) (ρ.eigenvalue_nonneg i))
    (mul_nonneg ht.1 (σ.eigenvalue_nonneg j)), hX]
  simp [M]

private lemma cost_partialTraceRight (ρ σ : Density (H ⊗ K)) (t : ℝ) (X : Operator H) :
    cost ρ.partialTraceRight σ.partialTraceRight t X = cost ρ σ t (Operator.tensor X 1) := by
  have hsub : Operator.tensor (1 - X) (1 : Operator K) = 1 - Operator.tensor X 1 := by
    rw [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_sub]
    simp only [LinearMap.sub_apply, TensorProduct.mapBilinear_apply, TensorProduct.map_one,
      Operator.tensor]
  rw [cost, cost, expectation_partialTraceRight, expectation_partialTraceRight, ← hsub]
  have hmul (A B : Operator H) :
      Operator.tensor (A * B) (1 : Operator K) = Operator.tensor A 1 * Operator.tensor B 1 := by
    change TensorProduct.map (A * B) 1 = TensorProduct.map A 1 * TensorProduct.map B 1
    rw [← TensorProduct.map_mul, one_mul]
  have hadj (A : Operator H) :
      (Operator.tensor A (1 : Operator K)).adjoint = Operator.tensor A.adjoint 1 := by
    change (TensorProduct.map A (1 : Operator K)).adjoint = TensorProduct.map A.adjoint 1
    rw [TensorProduct.adjoint_map, LinearMap.adjoint_one]
  rw [hadj, hadj, hmul, hmul X]

private lemma minimumCost_partialTraceRight (ρ σ : Density (H ⊗ K)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : minimumCost ρ σ t ≤ minimumCost ρ.partialTraceRight
      σ.partialTraceRight t := by
  obtain ⟨X, hX⟩ := exists_cost_eq ρ.partialTraceRight σ.partialTraceRight ht
  rw [← hX, cost_partialTraceRight]
  exact minimumCost_le ρ σ ht _

private def logPath (ρ σ : Density H) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (ρ.eigenvalue i * ‖entry ρ σ 1 i j‖ ^ 2) *
    (Real.log (ρ.eigenvalue i) - Real.log ((1 - t) * ρ.eigenvalue i + t * σ.eigenvalue j))

private def logSlope (ρ σ : Density H) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, (ρ.eigenvalue i * ‖entry ρ σ 1 i j‖ ^ 2) *
    ((ρ.eigenvalue i - σ.eigenvalue j) / ((1 - t) * ρ.eigenvalue i + t * σ.eigenvalue j))

private lemma hasDerivAt_logPath (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : HasDerivAt (logPath ρ σ) (logSlope ρ σ t) t := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  let p := ρ.eigenvalue i
  let q := σ.eigenvalue j
  let w := p * ‖entry ρ σ 1 i j‖ ^ 2
  change HasDerivAt (fun s => w * (Real.log p - Real.log ((1 - s) * p + s * q)))
    (w * ((p - q) / ((1 - t) * p + t * q))) t
  by_cases hw : w = 0
  · simp [hw, hasDerivAt_const]
  have hp : 0 < p := (ρ.eigenvalue_nonneg i).lt_of_ne' fun hz => hw (by simp [w, p, hz])
  have hq : 0 < q := (σ.eigenvalue_nonneg j).lt_of_ne' fun hz =>
    hw (h.eigenvalue_mul_overlap_eq_zero i j hz)
  have hd : 0 < (1 - t) * p + t * q := by
    by_cases ht' : t = 0
    · simpa [ht'] using hp
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) hp.le)
      (mul_pos (ht.1.lt_of_ne' ht') hq)
  have hd' := (((hasDerivAt_id t).const_sub 1).mul_const p).add ((hasDerivAt_id t).mul_const q)
  convert (((hd'.log hd.ne').const_sub (Real.log p)).const_mul w) using 1 <;> simp
  ring

-- Subtract the minimum cost from the scaled source mass to recover the scaled derivative.
private lemma scaled_logSlope (ρ σ : Density H) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    t * (1 - t) ^ 2 * logSlope ρ σ t = t * (1 - t) - minimumCost ρ σ t := by
  have hmass : ∑ i, ∑ j, ρ.eigenvalue i * ‖entry ρ σ 1 i j‖ ^ 2 = 1 := by
    simp only [entry, Module.End.one_apply, ← Finset.mul_sum, σ.eigenbasis.sum_sq_norm_inner_right,
      ρ.eigenbasis.norm_eq_one, one_pow, mul_one, ρ.sum_eigenvalue]
  conv_rhs =>
    lhs
    rw [← mul_one (t * (1 - t))]
    rhs
    rw [← hmass]
  rw [logSlope, minimumCost]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hp : ρ.eigenvalue i = 0
  · simp [hp, parallelSum]
  have hd := add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr ht.2) ((ρ.eigenvalue_nonneg i).lt_of_ne' hp))
    (mul_nonneg ht.1.le (σ.eigenvalue_nonneg j))
  unfold parallelSum
  field_simp [hd.ne']
  ring

private lemma logPath_one (ρ σ : Density H) : logPath ρ σ 1 = ρ.relativeEntropyReal σ := by
  simp only [logPath, sub_self, zero_mul, one_mul, zero_add, relativeEntropyReal_eq_sum,
    entry, Module.End.one_apply, mul_right_comm]

/-- Discarding the right factor decreases finite relative entropy, including for singular
reference states. -/
lemma relativeEntropyReal_partialTraceRight_le (ρ σ : Density (H ⊗ K))
    (h : ρ.AbsolutelyContinuous σ) :
    ρ.partialTraceRight.relativeEntropyReal σ.partialTraceRight ≤ ρ.relativeEntropyReal σ := by
  let f (t : ℝ) := logPath ρ σ t - logPath ρ.partialTraceRight σ.partialTraceRight t
  let g (t : ℝ) := logSlope ρ σ t - logSlope ρ.partialTraceRight σ.partialTraceRight t
  have hf (t : ℝ) (ht : t ∈ Set.Icc 0 1) : HasDerivAt f (g t) t :=
    (hasDerivAt_logPath _ _ h ht).sub (hasDerivAt_logPath _ _ h.partialTraceRight ht)
  have hm : MonotoneOn f (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hf t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    have hs := minimumCost_partialTraceRight ρ σ (Set.Ioo_subset_Icc_self ht)
    have hmul : 0 ≤ t * (1 - t) ^ 2 * g t := by
      dsimp only [g]
      rw [mul_sub, scaled_logSlope _ _ ht, scaled_logSlope _ _ ht]
      linarith
    exact nonneg_of_mul_nonneg_right hmul (mul_pos ht.1 (sq_pos_of_pos (sub_pos.mpr ht.2)))
  have hend := hm (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  have hz {D : Qudit} (a b : Density D) : logPath a b 0 = 0 := by simp [logPath]
  simpa only [f, hz, sub_zero, logPath_one, sub_nonneg] using hend

/-- Discarding the right subsystem cannot increase extended relative entropy. -/
lemma relativeEntropy_partialTraceRight_le (ρ σ : Density (H ⊗ K)) :
    ρ.partialTraceRight.relativeEntropy σ.partialTraceRight ≤ ρ.relativeEntropy σ := by
  by_cases h : ρ.AbsolutelyContinuous σ
  · simpa only [relativeEntropy, h, h.partialTraceRight, reduceIte] using
      ENNReal.ofReal_le_ofReal (ρ.relativeEntropyReal_partialTraceRight_le σ h)
  · rw [(relativeEntropy_eq_top_iff ρ σ).mpr h]
    exact le_top

end

end Qudit.Density
