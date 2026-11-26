/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/Entropy/Relative.lean: lower semicontinuity via truncated logarithms.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative
public import FQFP.CQM.Qudit.State.Spectral.Continuity
public import FQFP.CQM.Qudit.State.Spectral.OperatorSqrt
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of quantum relative entropy

Truncating the logarithm below `exp (-n)` gives continuous approximants in the
reference state. Their supremum recovers the divergence even when support inclusion fails.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology ENNReal

namespace Qudit.Density

variable {H : Qudit}

private def clippedNegLog (n : ℕ) (x : ℝ) : ℝ :=
  -Real.log (max (Real.exp (-(n : ℝ))) x)

private lemma continuous_clippedNegLog (n : ℕ) : Continuous (clippedNegLog n) := by
  unfold clippedNegLog
  refine ((continuous_const.max continuous_id).log fun x => ?_).neg
  exact ((Real.exp_pos _).trans_le (le_max_left _ x)).ne'

private lemma clippedNegLog_nonneg (n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    0 ≤ clippedNegLog n x := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact max_le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))) hx

private lemma clippedNegLog_zero (n : ℕ) : clippedNegLog n 0 = n := by
  simp [clippedNegLog, max_eq_left (Real.exp_pos _).le]

private def diagonalWeight (ρ σ : Density H) (i : Fin (Module.finrank ℂ H.state)) : ℝ :=
  (inner ℂ (σ.eigenbasis i) (ρ.op (σ.eigenbasis i))).re

private lemma diagonalWeight_nonneg (ρ σ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    0 ≤ diagonalWeight ρ σ i :=
  ρ.positive.re_inner_nonneg_right _

private def clippedRelativeEntropy (ρ σ : Density H) (n : ℕ) : ℝ :=
  ρ.expectation ρ.logOp + ρ.expectation (σ.spectralMap (clippedNegLog n))

private lemma clippedRelativeEntropy_eq_sum (ρ σ : Density H) (n : ℕ) :
    clippedRelativeEntropy ρ σ n =
      ρ.expectation ρ.logOp + ∑ i, clippedNegLog n (σ.eigenvalue i) * diagonalWeight ρ σ i := by
  unfold clippedRelativeEntropy
  rw [expectation_eq_sum_of_diagonal ρ σ.eigenbasis _ _ (σ.spectralMap_apply_eigenbasis _)]
  rfl

private lemma relativeEntropyReal_eq_weightedLog (ρ σ : Density H) :
    ρ.relativeEntropyReal σ =
      ρ.expectation ρ.logOp + ∑ i, -Real.log (σ.eigenvalue i) * diagonalWeight ρ σ i := by
  rw [relativeEntropyReal, expectation_sub, show σ.logOp = σ.spectralMap Real.log from rfl,
    expectation_eq_sum_of_diagonal ρ σ.eigenbasis _ _ (σ.spectralMap_apply_eigenbasis _)]
  simp only [neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

private lemma relativeEntropy_eq_iSup_clipped (ρ σ : Density H) :
    ρ.relativeEntropy σ = ⨆ n, ENNReal.ofReal (clippedRelativeEntropy ρ σ n) := by
  by_cases h : ρ.AbsolutelyContinuous σ
  · have hz (i) (hi : σ.eigenvalue i = 0) : diagonalWeight ρ σ i = 0 := by
      have hw := (absolutelyContinuous_iff_of_right_eigenbasis ρ σ σ.eigenbasis σ.eigenvalue
        σ.apply_eigenbasis).mp h i hi
      simp [diagonalWeight, hw]
    rw [relativeEntropy, ite_eq_left h]
    apply le_antisymm
    · have ht : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hn⟩ := (eventually_all.mpr fun (i : Fin (Module.finrank ℂ H.state)) => by
        by_cases hi : σ.eigenvalue i = 0
        · exact Eventually.of_forall fun _ => by simp [hi]
        · have hp := (σ.eigenvalue_nonneg i).lt_of_ne' hi
          exact (ht.eventually (gt_mem_nhds hp)).mono fun m hm => fun _ => hm.le :
        ∀ᶠ n : ℕ in atTop, ∀ i, σ.eigenvalue i ≠ 0 → Real.exp (-(n : ℝ)) ≤ σ.eigenvalue i).exists
      refine le_iSup_of_le n (le_of_eq (congrArg ENNReal.ofReal ?_))
      rw [relativeEntropyReal_eq_weightedLog, clippedRelativeEntropy_eq_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : σ.eigenvalue i = 0
      · simp [hz i hi]
      · rw [clippedNegLog, max_eq_right (hn i hi)]
    · refine iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
      rw [relativeEntropyReal_eq_weightedLog, clippedRelativeEntropy_eq_sum]
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : σ.eigenvalue i = 0
      · simp [hz i hi]
      · have hp := (σ.eigenvalue_nonneg i).lt_of_ne' hi
        exact mul_le_mul_of_nonneg_right
          (neg_le_neg (Real.log_le_log hp (le_max_right _ _))) (diagonalWeight_nonneg ρ σ i)
  · rw [(relativeEntropy_eq_top_iff ρ σ).mpr h]
    symm
    apply iSup_eq_top.2
    rw [absolutelyContinuous_iff_of_right_eigenbasis ρ σ σ.eigenbasis σ.eigenvalue
      σ.apply_eigenbasis] at h
    push Not at h
    obtain ⟨i, hi, hρ⟩ := h
    have hp : 0 < diagonalWeight ρ σ i := (diagonalWeight_nonneg ρ σ i).lt_of_ne'
      ((ρ.op.apply_eq_zero_iff_re_inner_eq_zero ρ.positive _).not.mp hρ)
    intro y hy
    obtain ⟨n, hn⟩ := exists_nat_gt ((y.toReal - ρ.expectation ρ.logOp) / diagonalWeight ρ σ i)
    have hs : (n : ℝ) * diagonalWeight ρ σ i ≤
        ∑ j, clippedNegLog n (σ.eigenvalue j) * diagonalWeight ρ σ j := by
      rw [← clippedNegLog_zero n, ← hi]
      exact Finset.single_le_sum (fun j _ =>
        mul_nonneg (clippedNegLog_nonneg n (σ.eigenvalue_le_one j))
          (diagonalWeight_nonneg ρ σ j)) (Finset.mem_univ i)
    refine ⟨n, ?_⟩
    rw [← ENNReal.ofReal_toReal hy.ne, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
      clippedRelativeEntropy_eq_sum]
    linarith [(div_lt_iff₀ hp).mp hn]

/-- Umegaki relative entropy is lower semicontinuous in its reference state. -/
theorem lowerSemicontinuous_relativeEntropy (ρ : Density H) :
    LowerSemicontinuous fun σ : Density H => ρ.relativeEntropy σ := by
  simp_rw [relativeEntropy_eq_iSup_clipped]
  refine lowerSemicontinuous_iSup fun n => (ENNReal.continuous_ofReal.comp ?_).lowerSemicontinuous
  exact continuous_const.add
    (ρ.continuous_expectation.comp
      (continuous_spectralMap _ (continuous_clippedNegLog n).continuousOn))

end Qudit.Density
