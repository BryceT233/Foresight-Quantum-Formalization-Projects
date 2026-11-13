/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.SchmidtRank
import FQFP.CQM.Qudit.State.Purification
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Schmidt rank regressions

The clients distinguish Schmidt rank from the rank of the joint pure density, retain
repeated Schmidt coefficients, and exercise rectangular systems and purification.
-/

open CategoryTheory MonoidalCategory Qudit

noncomputable section

private lemma bell_schmidtRank : (UnitState.ofBasis bellBasis 0).schmidtRank = 2 := by
  rw [UnitState.schmidtRank_eq_finrank_range_partialTraceRight]
  change Module.finrank ℂ (LinearMap.range bellDensity.partialTraceRight.op) = 2
  rw [bellDensity_partialTraceRight_op, LinearMap.range_smul _ _ (by norm_num)]
  change Module.finrank ℂ (LinearMap.range (LinearMap.id : Operator Qubit)) = 2
  rw [LinearMap.range_id, finrank_top]
  simp [Qubit]

-- The Bell density has rank one, but its Schmidt rank is two (not one distinct eigenvalue).
example : Module.finrank ℂ (LinearMap.range bellDensity.op) = 1 ∧
    (UnitState.ofBasis bellBasis 0).schmidtRank = 2 :=
  ⟨Density.finrank_range_pure _, bell_schmidtRank⟩

-- The new criterion detects Bell entanglement directly from Schmidt rank.
example : ¬ bellDensity.IsSeparable := by
  rw [bellDensity, Density.isSeparable_pure_iff_schmidtRank_eq_one, bell_schmidtRank]
  norm_num

-- Nontrivial phase and reversing unequal systems preserve product rank one.
example (v : UnitState (std 3)) (w : UnitState Qubit) :
    ((v.tensor w).phase Complex.I (by simp)).swap.schmidtRank = 1 := by
  rw [UnitState.schmidtRank_swap, UnitState.schmidtRank_phase, UnitState.schmidtRank_tensor]

-- Arbitrary rectangular states have the same rank in both reduced coordinate matrices.
example (ψ : UnitState (std 3 ⊗ Qubit)) :
    ((Density.pure ψ).partialTraceRight.toMatrix (ZBasis 3)).rank =
      ((Density.pure ψ).partialTraceLeft.toMatrix (ZBasis 2)).rank := by
  rw [← ψ.schmidtRank_eq_rank_toMatrix_partialTraceRight,
    ← ψ.schmidtRank_eq_rank_toMatrix_partialTraceLeft]

-- The coefficient-matrix interface composes with separability without a square-matrix premise.
example (ψ : UnitState (std 3 ⊗ Qubit)) :
    (Density.pure ψ).IsSeparable ↔ (ψ.coefficientMatrix (ZBasis 3) (ZBasis 2)).rank = 1 := by
  rw [Density.isSeparable_pure_iff_schmidtRank_eq_one,
    ψ.schmidtRank_eq_rank_coefficientMatrix (ZBasis 3) (ZBasis 2)]

-- The criterion constructs actual normalized product factors, not only a rank certificate.
example {H K : Qudit} (ψ : UnitState (H ⊗ K)) (hψ : ψ.schmidtRank = 1) :
    ∃ (v : UnitState H) (w : UnitState K), ψ = v.tensor w :=
  ψ.isProduct_iff_schmidtRank_eq_one.mpr hψ

-- Purifying any mixed state produces Schmidt rank equal to that state's operator rank.
example {H : Qudit} (ρ : Density H) :
    ρ.purify.schmidtRank = Module.finrank ℂ (LinearMap.range ρ.op) := by
  rw [UnitState.schmidtRank_eq_finrank_range_partialTraceRight,
    ρ.partialTraceRight_pure_purify]

-- Joint purity cannot be dropped from the equality of marginal ranks.
example : let v := UnitState.ofBasis (ZBasis 3) 0
    let σ := Density.maximallyMixed Qubit (by simp [Qubit])
    Module.finrank ℂ (LinearMap.range ((Density.pure v).tensor σ).partialTraceRight.op) ≠
      Module.finrank ℂ (LinearMap.range ((Density.pure v).tensor σ).partialTraceLeft.op) := by
  dsimp only
  rw [Density.partialTraceRight_tensor, Density.partialTraceLeft_tensor,
    Density.finrank_range_pure]
  have hop : (Density.maximallyMixed Qubit (by simp [Qubit])).op =
      (1 / 2 : ℂ) • (1 : Operator Qubit) := by simp [Qubit]
  rw [hop, LinearMap.range_smul _ _ (by norm_num)]
  change 1 ≠ Module.finrank ℂ (LinearMap.range (LinearMap.id : Operator Qubit))
  rw [LinearMap.range_id, finrank_top]
  norm_num [Qubit]

end
