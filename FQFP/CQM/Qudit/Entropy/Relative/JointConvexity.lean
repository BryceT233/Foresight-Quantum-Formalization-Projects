/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for joint convexity of relative entropy.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/DPI.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import FQFP.CQM.Qudit.Measurement.ClassicalRegister

/-!
# Joint convexity of quantum relative entropy

With a shared distribution of classical labels, the relative entropy of the flagged pair
is the weighted sum of the branch divergences. Only positive-weight branches contribute
to support inclusion. Discarding the label gives joint convexity by data processing.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H C : Qudit} {ι : Type*} [Fintype ι]

/-- Each label may use its own eigenbasis, even for noncommuting branch states. -/
private def flaggedBasis (b : OrthonormalBasis ι ℂ C.state) (σ : ι → Density H) :
    OrthonormalBasis (ι × Fin (Module.finrank ℂ H.state)) ℂ (H ⊗ C).state := by
  classical
  let v (a : ι × Fin (Module.finrank ℂ H.state)) : (H ⊗ C).state :=
    (σ a.1).eigenbasis a.2 ⊗ₜ[ℂ] b a.1
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, k⟩ ⟨j, l⟩
    dsimp only [v]
    rw [TensorProduct.inner_tmul ℂ ((σ i).eigenbasis k) ((σ j).eigenbasis l) (b i) (b j)]
    by_cases hij : i = j
    · subst j
      simp [(σ i).eigenbasis.inner_eq_ite]
    · simp [b.inner_eq_ite, hij]
  apply OrthonormalBasis.mk hv
  apply (hv.linearIndependent.span_eq_top_of_card_eq_finrank' _).ge
  change Fintype.card _ = Module.finrank ℂ (H.state ⊗[ℂ] C.state)
  rw [Module.finrank_tensorProduct, Module.finrank_eq_card_basis b.toBasis,
    Fintype.card_prod, Fintype.card_fin, mul_comm]

private lemma flaggedBasis_apply (b : OrthonormalBasis ι ℂ C.state) (σ : ι → Density H)
    (i : ι) (j : Fin (Module.finrank ℂ H.state)) :
    flaggedBasis b σ (i, j) = (σ i).eigenbasis j ⊗ₜ[ℂ] b i := by
  simp [flaggedBasis]

section

variable (b : OrthonormalBasis ι ℂ C.state) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
  (hs : ∑ i, w i = 1) (ρ σ : ι → Density H)

private lemma flaggedMixture_eigen (a : ι × Fin (Module.finrank ℂ H.state)) :
    (flaggedMixture b w hw hs σ).op (flaggedBasis b σ a) =
      (↑(w a.1 * (σ a.1).eigenvalue a.2) : ℂ) • flaggedBasis b σ a := by
  rcases a with ⟨i, j⟩
  rw [flaggedBasis_apply, flaggedMixture_apply_tmul, apply_eigenbasis,
    ← TensorProduct.smul_tmul', smul_smul, Complex.ofReal_mul]

/-- Support inclusion of flagged states is exactly support inclusion at positive-weight labels. -/
lemma absolutelyContinuous_flaggedMixture_iff :
    (flaggedMixture b w hw hs ρ).AbsolutelyContinuous (flaggedMixture b w hw hs σ) ↔
      ∀ i, 0 < w i → (ρ i).AbsolutelyContinuous (σ i) := by
  rw [absolutelyContinuous_iff_of_right_eigenbasis _ _ _ _ (flaggedMixture_eigen b w hw hs σ)]
  constructor
  · intro h i hi
    rw [absolutelyContinuous_iff_of_right_eigenbasis _ _ _ _ (σ i).apply_eigenbasis]
    intro j hj
    have he := h (i, j) (by simp [hj])
    rw [flaggedBasis_apply, flaggedMixture_apply_tmul] at he
    have hn := congrArg norm he
    simpa [norm_smul, TensorProduct.norm_tmul (𝕜 := ℂ) (E := H.state) (F := C.state),
      b.norm_eq_one, hi.ne'] using hn
  · rintro h ⟨i, j⟩ hij
    rw [flaggedBasis_apply, flaggedMixture_apply_tmul]
    rcases mul_eq_zero.mp hij with hi | hj
    · simp [hi]
    · by_cases hi : w i = 0
      · simp [hi]
      have hz := (absolutelyContinuous_iff_of_right_eigenbasis _ _ _ _
        (σ i).apply_eigenbasis).mp (h i ((hw i).lt_of_ne' hi)) j hj
      simp [hz]

private lemma expectation_logOp_flaggedMixture
    (h : ∀ i, 0 < w i → (ρ i).AbsolutelyContinuous (σ i)) :
    (flaggedMixture b w hw hs ρ).expectation (flaggedMixture b w hw hs σ).logOp =
      ∑ i, w i * (Real.log (w i) + (ρ i).expectation (σ i).logOp) := by
  rw [expectation_eq_sum_of_diagonal _ (flaggedBasis b σ) _ _
    (fun a => logOp_apply_of_eigenvector _ (flaggedMixture_eigen b w hw hs σ a)),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [flaggedBasis_apply, flaggedMixture_apply_tmul, inner_smul_right,
    TensorProduct.inner_tmul (𝕜 := ℂ) (E := H.state) (F := C.state), b.inner_eq_one,
    mul_one, Complex.re_ofReal_mul]
  by_cases hi : w i = 0
  · simp [hi]
  let e := (σ i).eigenbasis
  have hmass : ∑ j, (inner ℂ (e j) ((ρ i).op (e j))).re = 1 := by
    rw [← Complex.re_sum, ← LinearMap.trace_eq_sum_inner]
    exact congrArg Complex.re (ρ i).trace_one
  rw [(ρ i).expectation_eq_sum_of_diagonal e _ _
    (fun j => (σ i).logOp_apply_of_eigenvector ((σ i).apply_eigenbasis j))]
  calc
    _ = ∑ j, w i * ((Real.log (w i) + Real.log ((σ i).eigenvalue j)) *
        (inner ℂ (e j) ((ρ i).op (e j))).re) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : (σ i).eigenvalue j = 0
      · have hz := (absolutelyContinuous_iff_of_right_eigenbasis _ _ _ _
          (σ i).apply_eigenbasis).mp (h i ((hw i).lt_of_ne' hi)) j hj
        simp [e, hz]
      · rw [Real.log_mul hi hj]
        ring
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hmass, mul_one]

/-- The relative entropy of two states with the same classical flag distribution is the
weighted sum of their branch divergences, with `0 * ⊤ = 0`. -/
theorem relativeEntropy_flaggedMixture :
    (flaggedMixture b w hw hs ρ).relativeEntropy (flaggedMixture b w hw hs σ) =
      ∑ i, ENNReal.ofReal (w i) * (ρ i).relativeEntropy (σ i) := by
  classical
  by_cases h : ∀ i, 0 < w i → (ρ i).AbsolutelyContinuous (σ i)
  · have ha := (absolutelyContinuous_flaggedMixture_iff b w hw hs ρ σ).mpr h
    have hr : (flaggedMixture b w hw hs ρ).relativeEntropyReal (flaggedMixture b w hw hs σ) =
        ∑ i, w i * (ρ i).relativeEntropyReal (σ i) := by
      simp only [relativeEntropyReal, expectation_sub,
        expectation_logOp_flaggedMixture b w hw hs ρ ρ (fun i _ => .refl (ρ i)),
        expectation_logOp_flaggedMixture b w hw hs ρ σ h, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hn (i) : 0 ≤ w i * (ρ i).relativeEntropyReal (σ i) := by
      rcases (hw i).eq_or_lt with hi | hi
      · simp [← hi]
      · exact mul_nonneg hi.le ((ρ i).relativeEntropyReal_nonneg _ (h i hi))
    rw [relativeEntropy, ite_eq_left ha, hr, ENNReal.ofReal_sum_of_nonneg (fun i _ => hn i)]
    apply Finset.sum_congr rfl
    intro i _
    rcases (hw i).eq_or_lt with hi | hi
    · simp [← hi]
    · rw [relativeEntropy, ite_eq_left (h i hi), ENNReal.ofReal_mul hi.le]
  · have ha := (absolutelyContinuous_flaggedMixture_iff b w hw hs ρ σ).not.mpr h
    rw [(relativeEntropy_eq_top_iff _ _).mpr ha]
    symm
    push Not at h
    obtain ⟨i, hi, hfail⟩ := h
    apply ENNReal.sum_eq_top.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [(relativeEntropy_eq_top_iff _ _).mpr hfail, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hi).ne']

end

/-- Joint convexity of Umegaki relative entropy for a finite probability distribution. -/
theorem relativeEntropy_mixture_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ρ σ : ι → Density H) :
    (mixture w hw hs ρ).relativeEntropy (mixture w hw hs σ) ≤
      ∑ i, ENNReal.ofReal (w i) * (ρ i).relativeEntropy (σ i) := by
  classical
  let b := (ZBasis (Fintype.card ι)).reindex (Fintype.equivFin ι).symm
  have hd := (QuantumChannel.partialTraceRight H _).relativeEntropy_map_le
    (flaggedMixture b w hw hs ρ) (flaggedMixture b w hw hs σ)
  simpa only [QuantumChannel.map_partialTraceRight, partialTraceRight_flaggedMixture,
    relativeEntropy_flaggedMixture] using hd

/-- Binary joint convexity, including endpoint weights and infinite branch divergences. -/
theorem relativeEntropy_mix_le (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ρ₁ ρ₂ σ₁ σ₂ : Density H) :
    (mix p hp₀ hp₁ ρ₁ ρ₂).relativeEntropy (mix p hp₀ hp₁ σ₁ σ₂) ≤
      ENNReal.ofReal p * ρ₁.relativeEntropy σ₁ +
        ENNReal.ofReal (1 - p) * ρ₂.relativeEntropy σ₂ := by
  rw [← mixture_fin_two p hp₀ hp₁ ρ₁ ρ₂, ← mixture_fin_two p hp₀ hp₁ σ₁ σ₂]
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    relativeEntropy_mixture_le ![p, 1 - p] (by
      intro i
      fin_cases i
      · exact hp₀
      · exact sub_nonneg.mpr hp₁) (by simp) ![ρ₁, ρ₂] ![σ₁, σ₂]

end

end Qudit.Density
