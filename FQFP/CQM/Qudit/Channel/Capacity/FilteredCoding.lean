/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Capacity.PhaseCoding

/-!
# Random coding with a compressed joint output

A contraction into smaller output registers gives a finite coding estimate on the original
channel. The estimate includes the mean loss from compressing the dilation and the purity
of the subnormalized compressed marginal.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped BigOperators

namespace Qudit.QuantumChannel

open Superoperator

variable {H E B E' B' : Qudit}

private lemma traceNorm_sub_sq_le_three (a b c d : Operator E) :
    LinearMap.traceNorm (a - d) ^ 2 ≤ 3 * (LinearMap.traceNorm (a - b) ^ 2 +
      LinearMap.traceNorm (b - c) ^ 2 + LinearMap.traceNorm (d - c) ^ 2) := by
  have hs : a - d = ((a - b) + (b - c)) + -(d - c) := by abel
  have ht := (LinearMap.traceNorm_add_le ((a - b) + (b - c)) (-(d - c))).trans
    (add_le_add (LinearMap.traceNorm_add_le (a - b) (b - c)) le_rfl)
  rw [← hs, LinearMap.traceNorm_neg] at ht
  have hpos := fun x : Operator E => LinearMap.traceNorm_nonneg x
  apply ((sq_le_sq₀ (hpos _) (add_nonneg (add_nonneg (hpos _) (hpos _)) (hpos _))).mpr ht).trans
  nlinarith only [sq_nonneg (LinearMap.traceNorm (a - b) - LinearMap.traceNorm (b - c)),
    sq_nonneg (LinearMap.traceNorm (a - b) - LinearMap.traceNorm (d - c)),
    sq_nonneg (LinearMap.traceNorm (b - c) - LinearMap.traceNorm (d - c))]

/-- A filtered dilation yields a normalized physical phase input. Its physical marginal
obeys a trace-distance bound using the smaller register dimension, compressed purity and
mean squared dilation loss. No lower bound on the trace of the filtered state is needed. -/
theorem Dilation.exists_input_of_compressed_dilation {Φ : QuantumChannel H E} (d : Φ.Dilation B)
    (ρ : Density H) (V : E' ⟶ E) (W : B' ⟶ B) [IsIsometry V] [IsIsometry W]
    (T : H.state →ₗ[ℂ] (E' ⊗ B').state) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    let L := d.toHom.hom - (V ⊗ₘ W).hom ∘ₗ T
    let τ := Operator.partialTraceLeft (conjugate T ρ.op)
    ∃ v : UnitState H, (2 * (Φ.map (Density.pure v)).traceDistance (Φ.map ρ)) ^ 2 ≤
      3 * (8 * ρ.expectation (L.adjoint ∘ₗ L) + Module.finrank ℂ E'.state * (τ ^ 2).trace.re) := by
  classical
  intro L τ
  let U := (V ⊗ₘ W).hom ∘ₗ T
  let M (F : H.state →ₗ[ℂ] (E ⊗ B).state) := Operator.partialTraceRight ∘ₗ conjugate F
  let C : Superoperator H E' := Operator.partialTraceRight ∘ₗ conjugate T
  let t z := (Density.pure (ρ.spectralPhaseState z)).op
  let loss := ρ.expectation (L.adjoint ∘ₗ L)
  have hU (x) : ‖U x‖ ≤ ‖x‖ := by
    simpa only [U, LinearMap.comp_apply, norm_hom_of_isIsometry] using hT x
  have hcut (A : Operator H) : M U A = conjugate V.hom (C A) := by
    change Operator.partialTraceRight (conjugate ((V ⊗ₘ W).hom ∘ₗ T) A) = _
    rw [conjugate_comp, LinearMap.comp_apply, hom_tensorHom, partialTraceRight_conjugate_tensor,
      show W.hom.adjoint ∘ₗ W.hom = 1 from hom_adjoint_comp_of_isIsometry W, map_one, one_mul]
    rfl
  have h₁ : (𝔼 z, LinearMap.traceNorm (M d.toHom.hom (t z) - M U (t z)) ^ 2) ≤ 4 * loss := by
    simpa only [M, t, loss, L, U, Density.op_pure, LinearMap.comp_apply, conjugate_outer, map_sub,
      LIOfIsIsometry_apply, LIOfIsIsometry_toLinearMap] using
      ρ.expect_phase_marginal_disturbance_sq_le (LIOfIsIsometry d.toHom) U hU
  have h₂ : (𝔼 z, LinearMap.traceNorm (M U (t z) - M U ρ.op) ^ 2) ≤
      Module.finrank ℂ E'.state * (τ ^ 2).trace.re := by
    simp only [hcut, ← map_sub]
    have hiso (a : Operator E') : LinearMap.traceNorm (conjugate V.hom a) =
        LinearMap.traceNorm a :=
      Operator.traceNorm_isometry_sandwich a (LIOfIsIsometry V) (LIOfIsIsometry V)
    simp only [hiso]
    simp only [map_sub]
    exact ρ.expect_phase_partialTraceRight_sq_le T
  have h₃ : LinearMap.traceNorm (M d.toHom.hom ρ.op - M U ρ.op) ^ 2 ≤ 4 * loss := by
    simpa only [M, loss, L, U, LinearMap.comp_apply, map_sub, LIOfIsIsometry_toLinearMap] using
      ρ.traceNorm_mixed_marginal_disturbance_sq_le (LIOfIsIsometry d.toHom) U hU
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun z _ =>
    traceNorm_sub_sq_le_three (M d.toHom.hom (t z)) (M U (t z)) (M U ρ.op) (M d.toHom.hom ρ.op))
  simp only [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const] at hav
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hav
  refine ⟨ρ.spectralPhaseState z, ?_⟩
  rw [Density.traceDistance, show ∀ x : ℝ, 2 * (x / 2) = x by intro x; ring]
  change LinearMap.traceNorm (Φ.toSuperoperator (t z) - Φ.toSuperoperator ρ.op) ^ 2 ≤ _
  rw [d.channel_eq]
  change LinearMap.traceNorm (M d.toHom.hom (t z) - M d.toHom.hom ρ.op) ^ 2 ≤ _
  linarith only [hz, h₁, h₂, h₃]

end Qudit.QuantumChannel
