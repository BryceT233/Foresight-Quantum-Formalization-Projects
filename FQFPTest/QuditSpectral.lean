/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.Separable
import FQFP.CQM.Qudit.Teleportation.BellDensity

/-!
# Spectral ensembles and pure-state separability regressions

The clients cover independent systems of unequal dimensions, singular input states,
unrestricted zero-weight components, nontrivial global phase and Bell entanglement.
-/

open CategoryTheory MonoidalCategory Qudit
open scoped BigOperators TensorProduct

noncomputable section

local notation "v₀" => UnitState.ofBasis (ZBasis 2) (0 : Fin 2)
local notation "v₁" => UnitState.ofBasis (ZBasis 2) (1 : Fin 2)
local notation "ρ₀" => Density.pure v₀

-- Reconstruct independent systems of unequal dimensions, with a singular left input.
example (σ : Density (std 3)) :
    ((ρ₀).spectralEnsemble.tensor σ.spectralEnsemble).mix = (ρ₀).tensor σ := by
  rw [Ensemble.mix_tensor, Density.mix_spectralEnsemble, Density.mix_spectralEnsemble]

-- A zero-weight vector need not agree with the pure mixture, even up to phase.
example : (Ensemble.ofPure (Convexity.StdSimplex.single (0 : Fin 2))
    (UnitState.ofBasis (ZBasis 2))).mix = ρ₀ := by
  apply (Ensemble.mix_ofPure_eq_pure_iff _ _ _).mpr
  intro i hi
  have hi0 : i = 0 := by simpa [Finsupp.single_apply, eq_comm] using hi
  subst i
  rfl

-- The rigidity theorem identifies densities, so opposite vectors can mix to a pure state.
example (w : Convexity.StdSimplex ℝ (Fin 2)) :
    (Ensemble.ofPure w (fun i => if i = 0 then v₀ else (v₀).phase (-1) (by simp))).mix =
      ρ₀ := by
  apply (Ensemble.mix_ofPure_eq_pure_iff _ _ _).mpr
  intro i _
  split_ifs <;> simp

-- Conversely, positive weights on orthogonal vectors cannot give this pure density.
example (w : Convexity.StdSimplex ℝ (Fin 2)) (hw : w.weights 1 ≠ 0) :
    (Ensemble.ofPure w (UnitState.ofBasis (ZBasis 2))).mix ≠ ρ₀ := by
  intro h
  have he := (Ensemble.mix_ofPure_eq_pure_iff _ _ _).mp h 1 hw
  have hf := congrArg (fun ρ : Density Qubit => ρ.expectation (ρ₀).op) he
  norm_num [Density.expectation_pure_pure] at hf

-- Separability permits a global phase and unequal tensor-factor dimensions.
example (u : UnitState (std 3)) :
    (Density.pure (((v₀).tensor u).phase Complex.I (by simp))).IsSeparable := by
  rw [Density.pure_phase, ← Density.tensor_pure]
  exact Density.isSeparable_tensor _ _

-- Bell separability would force its maximally mixed marginal to be a pure projection.
example : ¬ bellDensity.IsSeparable := by
  intro h
  obtain ⟨v, u, hv⟩ := (Density.isSeparable_pure_iff (UnitState.ofBasis bellBasis 0)).mp h
  have hb : bellDensity = (Density.pure v).tensor (Density.pure u) := by
    rw [Density.tensor_pure, bellDensity, hv]
  have hm : bellDensity.partialTraceRight = Density.pure v := by
    rw [hb, Density.partialTraceRight_tensor]
  have hidem : bellDensity.partialTraceRight.op * bellDensity.partialTraceRight.op =
      bellDensity.partialTraceRight.op := by
    rw [hm, Density.pure_mul_self]
  rw [bellDensity_partialTraceRight_op] at hidem
  have he := congrArg (fun A : Operator Qubit =>
    inner ℂ (ZBasis 2 0) (A (ZBasis 2 0))) hidem
  norm_num [Module.End.mul_apply, LinearMap.smul_apply, inner_smul_right] at he

end
