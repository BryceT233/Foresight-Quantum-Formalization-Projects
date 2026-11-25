/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.FilteredCoding
public import FQFP.CQM.Qudit.Channel.Capacity.TypicalSubspace

/-!
# Typical projections in the phase code

Projecting the two outputs of a dilation loses at most the sum of their rejection
probabilities. The retained receiver purity only involves its typical spectral weights.
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory DaggerCategory
open scoped BigOperators TensorProduct
namespace Qudit

variable {A B E : Qudit}

open Superoperator

private lemma re_trace_sq_mono {X Y : Operator B} (hX : X.IsPositive) (hY : Y.IsPositive)
    (h : X ≤ Y) : (X ^ 2).trace.re ≤ (Y ^ 2).trace.re := by
  have hp := LinearMap.le_def.mp h
  have h₁ := (Complex.nonneg_iff.mp (hp.trace_mul_nonneg hY)).1
  have h₂ := (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hp)).1
  simp only [sub_mul, mul_sub, map_sub, Complex.sub_re] at h₁ h₂
  change (LinearMap.trace ℂ _ (X * X)).re ≤ (LinearMap.trace ℂ _ (Y * Y)).re
  linarith only [h₁, h₂]

private lemma trace_conjugate_projection (P X : Operator E) (h : IsStarProjection P) :
    (conjugate P X).trace = (P * X).trace := by
  rw [conjugate_apply, Operator.trace, LinearMap.trace_comp_comm', LinearMap.comp_assoc,
    show P.adjoint = P from h.isSelfAdjoint, show P ∘ₗ P = P from h.isIdempotentElem.eq]
  exact LinearMap.trace_mul_comm ℂ X P

private lemma partialTraceLeft_projection_le (P : Operator E) (hP : IsStarProjection P)
    (Q : Operator B) (X : Operator (E ⊗ B)) (hX : X.IsPositive) :
    Operator.partialTraceLeft (conjugate (Operator.tensor P Q) X) ≤
      conjugate Q (Operator.partialTraceLeft X) := by
  let M (F : Operator E) : Superoperator (E ⊗ B) B :=
    Operator.partialTraceLeft ∘ₗ conjugate (Operator.tensor F Q)
  have he : M P + M (1 - P) = conjugate Q ∘ₗ Operator.partialTraceLeft := by
    apply Operator.tensor_ext
    intro A C
    simp only [M, LinearMap.add_apply, LinearMap.comp_apply, Operator.tensor, conjugate_tensor]
    change Operator.partialTraceLeft (Superoperator.tensor (conjugate P) (conjugate Q)
      (Operator.tensor A C)) + Operator.partialTraceLeft
      (Superoperator.tensor (conjugate (1 - P)) (conjugate Q) (Operator.tensor A C)) = _
    rw [Superoperator.tensor_apply, Superoperator.tensor_apply, Operator.partialTraceLeft_tensor,
      Operator.partialTraceLeft_tensor, ← add_smul, trace_conjugate_projection _ _ hP,
      trace_conjugate_projection _ _ hP.one_sub, ← map_add, ← add_mul, add_sub_cancel,
      one_mul, LinearMap.partialTraceLeft_map, map_smul]
  have hn : (M (1 - P) X).IsPositive :=
    (hX.conj_adjoint (Operator.tensor (1 - P) Q)).partialTraceLeft
  have hsum := LinearMap.congr_fun he X
  change M P X + M (1 - P) X = conjugate Q (Operator.partialTraceLeft X) at hsum
  change M P X ≤ _
  rw [← hsum]
  exact le_add_of_nonneg_right (LinearMap.nonneg_iff_isPositive.mpr hn)

private lemma tensor_projection (P : Operator E) (Q : Operator B)
    (hp : IsStarProjection P) (hq : IsStarProjection Q) :
    IsStarProjection (Operator.tensor P Q) := by
  constructor
  · change TensorProduct.map P Q * TensorProduct.map P Q = _
    rw [← TensorProduct.map_mul, hp.isIdempotentElem.eq, hq.isIdempotentElem.eq]
    rfl
  · change (TensorProduct.map P Q).adjoint = _
    rw [TensorProduct.adjoint_map, show P.adjoint = P from hp.isSelfAdjoint,
      show Q.adjoint = Q from hq.isSelfAdjoint]
    rfl

private lemma norm_projection_le (P : Operator B) (hp : IsStarProjection P) (x : B.state) :
    ‖P x‖ ≤ ‖x‖ := by
  have hs : P.IsSymmetricProjection :=
    ⟨hp.isIdempotentElem, (LinearMap.eq_adjoint_iff _ _).mp hp.isSelfAdjoint.symm⟩
  obtain ⟨_, he⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hs
  conv_lhs => rw [he]
  exact Submodule.norm_starProjection_apply_le _ _

private lemma rejection_tensor_le (η : Density (E ⊗ B)) (P : Operator E) (Q : Operator B)
    (hp : IsStarProjection P) (hq : IsStarProjection Q) :
    η.expectation (1 - Operator.tensor P Q) ≤
      (1 - η.partialTraceRight.expectation P) + (1 - η.partialTraceLeft.expectation Q) := by
  have he : Operator.tensor (1 - P) (1 - Q) = 1 - Operator.tensor P 1 -
      Operator.tensor 1 Q + Operator.tensor P Q := by
    apply TensorProduct.ext'
    intro x y
    change (x - P x) ⊗ₜ[ℂ] (y - Q y) =
      x ⊗ₜ[ℂ] y - P x ⊗ₜ[ℂ] y - x ⊗ₜ[ℂ] Q y + P x ⊗ₜ[ℂ] Q y
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_sub]
    abel
  have hn := η.expectation_nonneg (Operator.isPositive_tensor
    (LinearMap.nonneg_iff_isPositive.mp hp.one_sub_nonneg)
    (LinearMap.nonneg_iff_isPositive.mp hq.one_sub_nonneg))
  rw [he, Density.expectation_add, Density.expectation_sub, Density.expectation_sub,
    Density.expectation_one] at hn
  rw [Density.expectation_sub, Density.expectation_one, Density.expectation_partialTraceRight,
    Density.expectation_partialTraceLeft]
  linarith only [hn]

namespace QuantumChannel

/-- Finite spectral truncation for a dilation. The two eigenvalue tails pay for the
discarded mass; the fluctuation term uses only the retained rank and squared weights. -/
theorem Dilation.exists_input_of_typical_projections {Φ : QuantumChannel A E}
    (d : Φ.Dilation B) (ρ : Density A) (w u : ℝ) :
    let σ := Φ.map ρ
    let μ := d.complementary.map ρ
    ∃ v : UnitState A, (2 * (Φ.map (Density.pure v)).traceDistance σ) ^ 2 ≤
      3 * (8 * ((1 - σ.expectation (σ.typicalProjection w)) +
        (1 - μ.expectation (μ.typicalProjection u))) + (σ.typicalIndices w).card *
          (∑ i ∈ μ.typicalIndices u, μ.eigenvalue i ^ 2)) := by
  intro σ μ
  let P := σ.typicalProjection w
  let Q := μ.typicalProjection u
  let S := LinearMap.range P
  let E' := Qudit.of S
  let V : E' ⟶ E := ofLinearIsometry S.subtypeₗᵢ
  have : IsIsometry V := isIsometry_ofLinearIsometry _
  let T : A.state →ₗ[ℂ] (E' ⊗ B).state := TensorProduct.map P.rangeRestrict Q ∘ₗ d.toHom.hom
  let F := Operator.tensor P Q
  let η := ρ.map d.toHom
  have hp := σ.isStarProjection_typicalProjection w
  have hq := μ.isStarProjection_typicalProjection u
  have hf := tensor_projection P Q hp hq
  have hT : (V ⊗ₘ 𝟙 B).hom ∘ₗ T = F ∘ₗ d.toHom.hom := by
    dsimp only [T]
    rw [hom_tensorHom, hom_id, ← LinearMap.comp_assoc, ← TensorProduct.map_comp]
    rfl
  have hcontract (x) : ‖T x‖ ≤ ‖x‖ := by
    rw [← norm_hom_of_isIsometry (V ⊗ₘ 𝟙 B) (T x)]
    have hx := LinearMap.congr_fun hT x
    simp only [LinearMap.comp_apply] at hx
    rw [hx]
    exact (norm_projection_le F hf _).trans_eq (norm_hom_of_isIsometry _ _)
  obtain ⟨v, hv⟩ := d.exists_input_of_compressed_dilation ρ V (𝟙 B) T hcontract
  refine ⟨v, hv.trans ?_⟩
  have hL : d.toHom.hom - (V ⊗ₘ 𝟙 B).hom ∘ₗ T = (1 - F) ∘ₗ d.toHom.hom := by
    rw [hT, LinearMap.sub_comp]
    rfl
  have hloss : ρ.expectation
      (((1 - F) ∘ₗ d.toHom.hom).adjoint ∘ₗ ((1 - F) ∘ₗ d.toHom.hom)) = η.expectation (1 - F) := by
    have he : ((1 - F) ∘ₗ d.toHom.hom).adjoint ∘ₗ ((1 - F) ∘ₗ d.toHom.hom) =
        conjugate d.toHom.hom.adjoint (1 - F) := by
      rw [LinearMap.adjoint_comp, show (1 - F).adjoint = 1 - F from hf.one_sub.isSelfAdjoint,
        conjugate_apply, LinearMap.adjoint_adjoint, LinearMap.comp_assoc]
      have hh : ((1 - F) ∘ₗ (1 - F)) ∘ₗ d.toHom.hom = (1 - F) ∘ₗ d.toHom.hom := by
        rw [show (1 - F) ∘ₗ (1 - F) = 1 - F from hf.one_sub.isIdempotentElem.eq]
      exact congrArg (d.toHom.hom.adjoint ∘ₗ ·) hh
    rw [he]
    exact congrArg Complex.re (trace_conjugate_adjoint d.toHom.hom ρ.op (1 - F))
  have htail := rejection_tensor_le η P Q hp hq
  have hout : η.partialTraceRight = σ := (d.map_eq_partialTraceRight ρ).symm
  have henv : η.partialTraceLeft = μ := rfl
  rw [hout, henv] at htail
  let Y := conjugate T ρ.op
  have htr : Operator.partialTraceLeft Y = Operator.partialTraceLeft (conjugate F η.op) := by
    have h := partialTraceLeft_comp_tensor (ofIsometry V) (ofIsometry (𝟙 B))
    rw [← ofIsometry_tensor, ofIsometry_id, id_comp] at h
    have he := congrArg (fun Γ => Γ.toSuperoperator Y) h
    change Operator.partialTraceLeft (conjugate (V ⊗ₘ 𝟙 B).hom (conjugate T ρ.op)) = _ at he
    have hc : conjugate (V ⊗ₘ 𝟙 B).hom ∘ₗ conjugate T = conjugate F ∘ₗ conjugate d.toHom.hom := by
      rw [← conjugate_comp, hT, conjugate_comp]
    exact he.symm.trans (congrArg Operator.partialTraceLeft (LinearMap.congr_fun hc ρ.op))
  have hsmall : Operator.partialTraceLeft Y ≤ conjugate Q μ.op := by
    rw [htr]
    exact partialTraceLeft_projection_le P hp Q η.op η.positive
  have hpur := re_trace_sq_mono (ρ.positive.conj_adjoint T).partialTraceLeft
    (μ.positive.conj_adjoint Q) hsmall
  have hb := hpur.trans_eq (μ.re_trace_sq_conjugate_typicalProjection u)
  have hnonneg : 0 ≤ ((Operator.partialTraceLeft Y) ^ 2).trace.re := by
    exact (Complex.nonneg_iff.mp ((ρ.positive.conj_adjoint T).partialTraceLeft.trace_mul_nonneg
      (ρ.positive.conj_adjoint T).partialTraceLeft)).1
  rw [hL, hloss]
  apply mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left htail (by norm_num))
    (mul_le_mul (Nat.cast_le.mpr (σ.finrank_range_typicalProjection_le w)) hb hnonneg
      (Nat.cast_nonneg _))) (by norm_num)

/-- Typical selection on the environment with its reference, and separately on the
receiver, gives an input with a decoupled reference in the original channel. -/
theorem Dilation.exists_decoupled_input_of_typical_projections {Φ : QuantumChannel A B}
    (d : Φ.Dilation E) {R : Qudit} (ρ : Density A) (τ : Density R) (w : ℝ) :
    let σ := (d.complementary.map ρ).tensor τ
    let μ := Φ.map ρ
    ∃ v : UnitState (A ⊗ R),
      (2 * (((d.complementary.tensor (id R)).map (Density.pure v)).traceDistance σ)) ^ 2 ≤
        3 * (8 * ((1 - σ.expectation (σ.typicalProjection w)) +
          (1 - μ.expectation (μ.typicalProjection w))) + (σ.typicalIndices w).card *
            (∑ i ∈ μ.typicalIndices w, μ.eigenvalue i ^ 2)) := by
  let D : (Φ.comp (partialTraceRight A R)).Dilation (E ⊗ R) :=
    ⟨d.lift R, inferInstance, (d.partialTraceRight_lift R).symm⟩
  have hc : D.complementary = d.complementary.tensor (id R) :=
    (hasMarginals_iff.mp (d.hasMarginals_lift R)).2
  simpa only [D.complementary_symm, hc, map_tensor, map_id, map_comp, map_partialTraceRight,
    Density.partialTraceRight_tensor] using
    D.symm.exists_input_of_typical_projections (ρ.tensor τ) w w

end QuantumChannel

end Qudit
