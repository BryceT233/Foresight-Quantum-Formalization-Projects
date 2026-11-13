/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.Separable
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Purity, rank and reduced states

These clients distinguish the rank-one Bell density from its rank-two marginals, test
factor recovery with a prescribed phase and unequal dimensions, and show why the
separability/marginal-purity equivalence needs the joint state to be pure.
-/

open CategoryTheory MonoidalCategory Qudit
open scoped ComplexOrder

noncomputable section

-- Matrix rank one constructs an actual unit vector in an arbitrary coordinate system.
example {H : Qudit} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (htr : M.trace = 1) (hr : M.rank = 1) :
    ∃ v : UnitState H, Density.ofMatrix b M hM htr = Density.pure v := by
  apply (Density.isPure_iff_rank_toMatrix_eq_one _ b).mpr
  simpa only [Density.toMatrix_ofMatrix] using hr

-- The joint Bell state has rank one in every orthonormal coordinate system.
example (b : OrthonormalBasis (Fin 4) ℂ (Qubit ⊗ Qubit).state) :
    (bellDensity.toMatrix b).rank = 1 :=
  (Density.isPure_iff_rank_toMatrix_eq_one _ b).mp
    (Density.isPure_pure (UnitState.ofBasis bellBasis 0))

private lemma finrank_range_half_id :
    Module.finrank ℂ (LinearMap.range ((1 / 2 : ℂ) • (1 : Operator Qubit))) = 2 := by
  rw [LinearMap.range_smul _ _ (by norm_num)]
  change Module.finrank ℂ (LinearMap.range (LinearMap.id : Operator Qubit)) = 2
  rw [LinearMap.range_id, finrank_top]
  simp [Qubit]

-- Each marginal, in contrast, has rank two and is not pure.
example : Module.finrank ℂ (LinearMap.range bellDensity.partialTraceRight.op) = 2 := by
  rw [bellDensity_partialTraceRight_op]
  exact finrank_range_half_id

example : ¬ bellDensity.partialTraceRight.IsPure := by
  rw [Density.isPure_iff_finrank_range_eq_one, bellDensity_partialTraceRight_op,
    finrank_range_half_id]
  norm_num

example : ¬ bellDensity.partialTraceLeft.IsPure := by
  rw [Density.isPure_iff_finrank_range_eq_one, bellDensity_partialTraceLeft_op,
    finrank_range_half_id]
  norm_num

-- The new marginal criterion itself detects Bell entanglement.
example : ¬ bellDensity.IsSeparable := by
  have hPure : bellDensity.IsPure := Density.isPure_pure (UnitState.ofBasis bellBasis 0)
  rw [hPure.isSeparable_iff_isPure_partialTraceLeft,
    Density.isPure_iff_finrank_range_eq_one, bellDensity_partialTraceLeft_op,
    finrank_range_half_id]
  norm_num

-- A prescribed phase of the left factor is retained exactly; it is absorbed on the right.
example (ψ : UnitState (Qubit ⊗ std 3)) (v : UnitState Qubit)
    (h : (Density.pure ψ).partialTraceRight = Density.pure v) :
    ∃ w : UnitState (std 3), ψ = (v.phase Complex.I (by simp)).tensor w := by
  apply ψ.exists_eq_tensor_of_partialTraceRight_eq_pure
  simpa only [Density.pure_phase] using h

-- Discarding the qubit retains the qutrit, and recovers the right factor.
example (ψ : UnitState (Qubit ⊗ std 3)) (w : UnitState (std 3))
    (h : (Density.pure ψ).partialTraceLeft = Density.pure w) :
    ∃ v : UnitState Qubit, ψ = v.tensor w :=
  ψ.exists_eq_tensor_of_partialTraceLeft_eq_pure w h

-- Separability of a pure state can be decided from either marginal's operator rank.
example {H K : Qudit} (ρ : Density (H ⊗ K)) (hρ : ρ.IsPure) :
    ρ.IsSeparable ↔ Module.finrank ℂ (LinearMap.range ρ.partialTraceRight.op) = 1 := by
  rw [hρ.isSeparable_iff_isPure_partialTraceRight, Density.isPure_iff_finrank_range_eq_one]

-- A separable mixed product may have mixed marginals: joint purity cannot be omitted.
example : let ρ := Density.maximallyMixed Qubit (by simp [Qubit])
    (ρ.tensor ρ).IsSeparable ∧ ¬ (ρ.tensor ρ).partialTraceRight.IsPure := by
  dsimp only
  refine ⟨Density.isSeparable_tensor _ _, ?_⟩
  rw [Density.partialTraceRight_tensor, Density.isPure_iff_finrank_range_eq_one]
  have hop : (Density.maximallyMixed Qubit (by simp [Qubit])).op =
      (1 / 2 : ℂ) • (1 : Operator Qubit) := by simp [Qubit]
  rw [hop, finrank_range_half_id]
  norm_num

-- Dimension one remains allowed, and every density on it is pure.
example (ρ : Density (std 1)) : ρ.IsPure := by
  refine ⟨UnitState.ofBasis (ZBasis 1) 0, Density.eq_pure_of_range_le _ _ ?_⟩
  have hs : Submodule.span ℂ {(UnitState.ofBasis (ZBasis 1) 0).val} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero _ (UnitState.ne_zero _)).mp (by simp)
  rw [hs]
  exact le_top

end
