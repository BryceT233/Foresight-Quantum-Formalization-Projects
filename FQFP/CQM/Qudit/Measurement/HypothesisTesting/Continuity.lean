/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
Physlib reference for continuity in the alternative state.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/ResourceTheory/HypothesisTesting.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.Attainment
public import FQFP.CQM.Qudit.State.Topology

/-!
# Stability in the alternative state

At a fixed null state and type I error budget, the optimal type II error for a single
alternative is 1-Lipschitz in trace distance. This gives the singleton continuity theorem
of physlib's `OptimalHypothesisRate`. Closing a composite alternative preserves the optimal error.
-/

public section

namespace Qudit

variable {H : Qudit}

namespace Density

/-- Changing a single alternative changes the optimal error by at most its trace distance. -/
theorem lipschitzWith_optimalTypeIIError_singleton (ρ : Density H) (ε : unitInterval) :
    LipschitzWith 1 (fun σ => ρ.optimalTypeIIError ε {σ}) := by
  have bound (σ τ : Density H) :
      (ρ.optimalTypeIIError ε {σ} : ℝ) - ρ.optimalTypeIIError ε {τ} ≤ σ.traceDistance τ := by
    obtain ⟨T, hT, hmin⟩ := ρ.exists_test_attaining_optimalTypeIIError ε {τ}
    have hle := ρ.optimalTypeIIError_le ε {σ} T hT.le
    rw [worstCaseTypeIIError_singleton] at hle hmin
    have h := (le_abs_self _).trans (σ.abs_expectation_sub_le_traceDistance τ T.2.1 T.2.2)
    exact (sub_le_sub (show (ρ.optimalTypeIIError ε {σ} : ℝ) ≤ σ.expectation T from hle)
      (congrArg Subtype.val hmin).le).trans h
  apply LipschitzWith.of_dist_le_mul
  intro σ τ
  rw [NNReal.coe_one, one_mul, dist_eq_traceDistance, Subtype.dist_eq, Real.dist_eq, abs_sub_le_iff]
  exact ⟨bound σ τ, (bound τ σ).trans_eq (traceDistance_comm τ σ)⟩

/-- The optimal error varies continuously with the single alternative at every budget. -/
@[fun_prop]
theorem continuous_optimalTypeIIError_singleton (ρ : Density H) (ε : unitInterval) :
    Continuous (fun σ => ρ.optimalTypeIIError ε {σ}) :=
  (ρ.lipschitzWith_optimalTypeIIError_singleton ε).continuous

end Density

/-- Closing a composite alternative preserves every test's worst-case acceptance probability. -/
theorem worstCaseTypeIIError_closure (T : Set.Icc (0 : Operator H) 1)
    (S : Set (Density H)) : worstCaseTypeIIError T (closure S) = worstCaseTypeIIError T S := by
  apply le_antisymm _ (iSup_le_iSup_of_subset subset_closure)
  have hc : IsClosed {σ : Density H | σ.expectation T ≤ (worstCaseTypeIIError T S : ℝ)} :=
    isClosed_le (Density.lipschitzWith_expectation T.2.1 T.2.2).continuous continuous_const
  have hs : S ⊆ {σ : Density H | σ.expectation T ≤ (worstCaseTypeIIError T S : ℝ)} := by
    intro σ hσ
    exact (le_iSup_of_le σ (le_iSup_of_le hσ le_rfl) :
      (⟨σ.expectation T, σ.expectation_mem_Icc T.2.1 T.2.2⟩ : unitInterval) ≤
        worstCaseTypeIIError T S)
  exact iSup_le fun σ => iSup_le fun hσ => (closure_minimal hs hc hσ)

/-- A dense subset of the alternatives yields the same optimal error as its closure. -/
theorem Density.optimalTypeIIError_closure (ρ : Density H) (ε : unitInterval)
    (S : Set (Density H)) :
    ρ.optimalTypeIIError ε (closure S) = ρ.optimalTypeIIError ε S := by
  simp only [optimalTypeIIError, worstCaseTypeIIError_closure]

end Qudit
