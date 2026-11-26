/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/SteinsLemma.lean: logarithmic rounding of the reference
spectrum and the resulting relative entropy comparison, equations (S45)–(S61).

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative.Pinching
public import FQFP.CQM.Qudit.State.Spectral.Continuity
public import FQFP.CQM.Qudit.State.StrictPositivity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Spectral rounding of free alternatives

Rounding the logarithm of a full-support density operator upward on a fixed grid and
renormalizing bounds the number of spectral values while changing the density by only
a fixed multiplicative factor in the operator order.
-/

@[expose] public noncomputable section

open scoped ComplexOrder

namespace Qudit.Density

variable {H : Qudit}

private def roundedWeight (L x : ℝ) : ℝ := Real.exp (-(L * ⌊-Real.log x / L⌋₊))

private lemma le_roundedWeight {L x : ℝ} (hL : 0 < L) (hx : 0 < x) (hx₁ : x ≤ 1) :
    x ≤ roundedWeight L x := by
  have hf := Nat.floor_le (div_nonneg (neg_nonneg.mpr (Real.log_nonpos hx.le hx₁)) hL.le)
  have he := (le_div_iff₀ hL).mp hf
  calc
    x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ roundedWeight L x := Real.exp_le_exp.mpr (by linarith)

private lemma roundedWeight_le {L x : ℝ} (hL : 0 < L) (hx : 0 < x) :
    roundedWeight L x ≤ Real.exp L * x := by
  have hf := Nat.lt_floor_add_one (-Real.log x / L)
  have he := (div_lt_iff₀ hL).mp hf
  calc
    roundedWeight L x ≤ Real.exp (L + Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp L * x := by rw [Real.exp_add, Real.exp_log hx]

private lemma spectralMap_mono_eigenvalues (σ : Density H) (f g : ℝ → ℝ)
    (h : ∀ i, f (σ.eigenvalue i) ≤ g (σ.eigenvalue i)) : σ.spectralMap f ≤ σ.spectralMap g := by
  rw [LinearMap.le_def, spectralMap, spectralMap, ← Finset.sum_sub_distrib]
  refine LinearMap.isPositive_sum _ fun i _ => ?_
  rw [← sub_smul, ← Complex.ofReal_sub]
  exact (Operator.isPositive_outer _).smul_of_nonneg (by exact_mod_cast sub_nonneg.mpr (h i))

private lemma real_smul_op_eq_spectralMap (σ : Density H) (c : ℝ) :
    c • σ.op = σ.spectralMap (fun x => c * x) := by
  apply σ.eigenbasis.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.smul_apply, apply_eigenbasis,
    spectralMap_apply_eigenbasis, Complex.ofReal_mul]
  exact smul_smul (c : ℂ) (σ.eigenvalue i : ℂ) (σ.eigenbasis i)

/-- A spectral lower bound (e^{-NL}) permits rounding to at most (N+1) spectral values
while perturbing the density operator multiplicatively by at most (e^L). -/
theorem exists_spectralRounding (σ : Density H) {N : ℕ} {L : ℝ} (hL : 0 < L)
    (hσ : IsStrictlyPositive σ.op) (hmin : ∀ i, Real.exp (-(N * L)) ≤ σ.eigenvalue i) :
    ∃ τ : Density H, IsStrictlyPositive τ.op ∧ τ.spectralValues.card ≤ N + 1 ∧
      Real.exp (-L) • σ.op ≤ τ.op ∧ τ.op ≤ Real.exp L • σ.op := by
  let z := ∑ i, roundedWeight L (σ.eigenvalue i)
  let w (x : ℝ) := roundedWeight L x / z
  have hp (i) : 0 < σ.eigenvalue i := (Real.exp_pos _).trans_le (hmin i)
  have hz₁ : 1 ≤ z := σ.sum_eigenvalue ▸ Finset.sum_le_sum fun i _ =>
    le_roundedWeight hL (hp i) (σ.eigenvalue_le_one i)
  have hzp : 0 < z := zero_lt_one.trans_le hz₁
  have hz₂ : z ≤ Real.exp L := calc
    z ≤ ∑ i, Real.exp L * σ.eigenvalue i := Finset.sum_le_sum fun i _ => roundedWeight_le hL (hp i)
    _ = Real.exp L := by rw [← Finset.mul_sum, σ.sum_eigenvalue, mul_one]
  let τ := Density.mixture (fun i => w (σ.eigenvalue i)) (fun i => by
    exact div_nonneg (Real.exp_pos _).le hzp.le)
    (by simp only [w, ← Finset.sum_div, z, div_self hzp.ne'])
    (fun i => Density.pure (UnitState.ofBasis σ.eigenbasis i))
  have hop : τ.op = σ.spectralMap w := rfl
  have hlo : Real.exp (-L) • σ.op ≤ τ.op := by
    rw [hop, real_smul_op_eq_spectralMap]
    refine spectralMap_mono_eigenvalues _ _ _ fun i => ?_
    rw [Real.exp_neg, inv_mul_eq_div]
    exact (div_le_div_of_nonneg_left (hp i).le hzp hz₂).trans
      (div_le_div_of_nonneg_right (le_roundedWeight hL (hp i) (σ.eigenvalue_le_one i)) hzp.le)
  have hhi : τ.op ≤ Real.exp L • σ.op := by
    rw [hop, real_smul_op_eq_spectralMap]
    refine spectralMap_mono_eigenvalues _ _ _ fun i => ?_
    exact ((div_le_self (Real.exp_pos _).le hz₁ : w (σ.eigenvalue i) ≤ _)).trans
      (roundedWeight_le hL (hp i))
  have he (i) : τ.op (σ.eigenbasis i) = (w (σ.eigenvalue i) : ℂ) • σ.eigenbasis i := by
    rw [hop, spectralMap_apply_eigenbasis]
  have hstrict : IsStrictlyPositive (Real.exp (-L) • σ.op) := hσ.smul (Real.exp_pos _)
  refine ⟨τ, IsStrictlyPositive.of_le hstrict hlo, ?_, hlo, hhi⟩
  classical
  let W (j : Fin (N + 1)) := Real.exp (-(L * (j.val : ℝ))) / z
  have hsub : Finset.univ.image (w ∘ σ.eigenvalue) ⊆ Finset.univ.image W := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    have hl := (Real.log_le_log (Real.exp_pos _) (hmin i))
    rw [Real.log_exp] at hl
    have hd : -Real.log (σ.eigenvalue i) / L ≤ N := (div_le_iff₀ hL).mpr (by linarith)
    have hj : ⌊-Real.log (σ.eigenvalue i) / L⌋₊ ≤ N := Nat.floor_le_of_le hd
    exact Finset.mem_image.mpr ⟨⟨_, Nat.lt_succ_of_le hj⟩, Finset.mem_univ _, rfl⟩
  rw [τ.spectralValues_eq_image_of_eigenbasis σ.eigenbasis _ he]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

private lemma logOp_eq_cfc_log (σ : Density H) (hσ : IsStrictlyPositive σ.op) :
    σ.logOp = CFC.log σ.op := by
  rw [logOp, CFC.log, cfc_eq_spectralMap]
  exact Real.continuousOn_log.mono fun x hx => (hσ.spectrum_pos hx).ne'

/-- If the right-hand reference dominates the left one up to a factor, the finite relative
entropies differ by at most the logarithm of that factor in the corresponding direction. -/
theorem relativeEntropyReal_le_of_reference_le_smul (ρ σ τ : Density H) {c : ℝ}
    (hc : 0 < c) (hσ : IsStrictlyPositive σ.op) (hτ : IsStrictlyPositive τ.op)
    (h : τ.op ≤ c • σ.op) : ρ.relativeEntropyReal σ ≤ ρ.relativeEntropyReal τ + Real.log c := by
  have hlog := CFC.log_monotoneOn hτ (hσ.smul hc) h
  rw [CFC.log_smul' _ hc hσ, ← logOp_eq_cfc_log _ hτ, ← logOp_eq_cfc_log _ hσ,
    Algebra.algebraMap_eq_smul_one] at hlog
  have hpos := ρ.expectation_nonneg (LinearMap.le_def.mp hlog)
  rw [expectation_sub, expectation_add, expectation_smul, expectation_one, mul_one] at hpos
  simp only [relativeEntropyReal, expectation_sub]
  linarith

end Qudit.Density
