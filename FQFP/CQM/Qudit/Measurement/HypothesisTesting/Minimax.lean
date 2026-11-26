/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/HypothesisTesting.lean: reduction of compact convex
composite alternatives to singleton testing by a minimax theorem.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.Attainment
public import Mathlib.Topology.Sion

/-!
# Least favorable alternatives in quantum hypothesis testing

With a compact convex alternative set, the bilinear acceptance probability has a saddle point
on the feasible effects and the alternative operators. The alternative at that saddle point
has the same optimal type II error as the whole set.
-/

public noncomputable section

open scoped ComplexOrder

namespace Qudit.Density

variable {H : Qudit}

/-- Some single alternative realizes the optimal error of a compact convex composite test. -/
theorem exists_leastFavorableAlternative (ρ : Density H) (ε : unitInterval) {S : Set (Density H)}
    (hne : S.Nonempty) (hS : IsCompact S) (hc : Convex ℝ (Density.op '' S)) :
    ∃ σ ∈ S, ρ.optimalTypeIIError ε {σ} = ρ.optimalTypeIIError ε S := by
  let X := Set.Icc (0 : Operator H) 1 ∩ {T | 1 - ε.val ≤ ρ.expectation T}
  let tr : Operator H →ₗ[ℝ] ℝ :=
    Complex.reCLM.toLinearMap.comp ((LinearMap.trace ℂ H.state).restrictScalars ℝ)
  let left (A : Operator H) := tr.comp ((LinearMap.mulRight ℂ A).restrictScalars ℝ)
  let right (T : Operator H) := tr.comp ((LinearMap.mulLeft ℂ T).restrictScalars ℝ)
  have hXne : X.Nonempty := ⟨1,
    ⟨LinearMap.nonneg_iff_isPositive.mpr LinearMap.isPositive_one, le_rfl⟩, by
      change 1 - ε.val ≤ ρ.expectation 1
      rw [expectation_one]
      linarith [ε.2.1]⟩
  have hXc : Convex ℝ X :=
    (convex_Icc 0 1).inter ((convex_Ici (1 - ε.val)).linear_preimage (left ρ.op))
  have hXk : IsCompact X :=
    Operator.isCompact_effects.inter_right (isClosed_le continuous_const ρ.continuous_expectation)
  have : FiniteDimensional ℝ (Operator H) := FiniteDimensional.trans ℝ ℂ _
  obtain ⟨T, hT, B, ⟨σ, hσ, rfl⟩, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn (f := fun T A => left A T) hXne hXc hXk
      (fun A _ => (left A).continuous_of_finiteDimensional.continuousOn.lowerSemicontinuousOn)
      (fun A _ => ((left A).convexOn hXc).quasiconvexOn)
      hc (hne.image Density.op) (hS.image continuous_op)
      (fun T _ => (right T).continuous_of_finiteDimensional.continuousOn.upperSemicontinuousOn)
      (fun T _ => ((right T).concaveOn hc).quasiconcaveOn)
  let E : Set.Icc (0 : Operator H) 1 := ⟨T, hT.1⟩
  have he : ρ.expectation (1 - E.val) ≤ ε := by
    rw [expectation_sub, expectation_one]
    exact sub_le_comm.mp (show 1 - ε.val ≤ ρ.expectation T from hT.2)
  let p : unitInterval := ⟨σ.expectation E, σ.expectation_mem_Icc E.2.1 E.2.2⟩
  have hleft : worstCaseTypeIIError E S ≤ p :=
    iSup_le fun τ => iSup_le fun hτ => hsaddle T hT τ.op (Set.mem_image_of_mem _ hτ)
  have hright : p ≤ ρ.optimalTypeIIError ε {σ} := by
    refine le_iInf fun U => ?_
    rw [worstCaseTypeIIError_singleton]
    have hu : U.val.val ∈ X := ⟨U.val.2, by
      have ht := U.2
      rw [expectation_sub, expectation_one] at ht
      change 1 - ε.val ≤ ρ.expectation U.val.val
      linarith⟩
    exact hsaddle U.val.val hu σ.op (Set.mem_image_of_mem _ hσ)
  refine ⟨σ, hσ, le_antisymm (ρ.optimalTypeIIError_mono ε (Set.singleton_subset_iff.mpr hσ)) ?_⟩
  exact (ρ.optimalTypeIIError_le ε S E he).trans (hleft.trans hright)

/-- The optimal error against a compact convex set is the supremum of its singleton errors. -/
theorem optimalTypeIIError_eq_iSup_singleton (ρ : Density H) (ε : unitInterval)
    {S : Set (Density H)} (hS : IsCompact S) (hc : Convex ℝ (Density.op '' S)) :
    ρ.optimalTypeIIError ε S = ⨆ σ ∈ S, ρ.optimalTypeIIError ε {σ} := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [optimalTypeIIError_empty, ← bot_eq_zero]
  · apply le_antisymm _ (iSup_le fun σ => iSup_le fun hσ =>
      ρ.optimalTypeIIError_mono ε (Set.singleton_subset_iff.mpr hσ))
    obtain ⟨σ, hσ, he⟩ := ρ.exists_leastFavorableAlternative ε hne hS hc
    exact le_iSup_of_le σ (le_iSup_of_le hσ he.ge)

end Qudit.Density
