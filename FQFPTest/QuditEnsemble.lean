/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Channel.EntanglementBreaking
import FQFP.CQM.Qudit.Channel.Classical

/-!
# Finite ensembles, classical correlations and measurement-preparation clients

These checks cover zero-probability outcomes, phase-invariant pure ensembles, unequal
input/output dimensions, a classically correlated separable state that is not a product,
and an entangled Bell input to a measurement-preparation channel.
-/

open CategoryTheory MonoidalCategory Qudit
open scoped BigOperators TensorProduct

noncomputable section

local notation "v₀" => UnitState.ofBasis (ZBasis 2) (0 : Fin 2)
local notation "v₁" => UnitState.ofBasis (ZBasis 2) (1 : Fin 2)
local notation "ρ₀" => Density.pure v₀
local notation "ρ₁" => Density.pure v₁
local notation "E₀" => Operator.outer (ZBasis 2 0) (ZBasis 2 0)
local notation "E₁" => Operator.outer (ZBasis 2 1) (ZBasis 2 1)

-- A zero weight contributes nothing, without requiring that its state be pure or invertible.
example (σ : Density Qubit) :
    (Ensemble.mk (Convexity.StdSimplex.single (0 : Fin 2))
      (fun i => if i = 0 then ρ₀ else σ)).mix = ρ₀ := by
  apply Density.ext
  simp [Ensemble.op_mix, Ensemble.weight]

-- Every label may carry a different global phase; its density mixture is unchanged.
example {H : Qudit} {ι : Type*} [Fintype ι] (w : Convexity.StdSimplex ℝ ι)
    (v : ι → UnitState H) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    (Ensemble.ofPure w (fun i => (v i).phase (c i) (hc i))).mix =
      (Ensemble.ofPure w v).mix := by
  apply congrArg Ensemble.mix
  apply Ensemble.ext
  · rfl
  · funext i
    exact Density.pure_phase _ _ _

-- Relabel and evolve: the mixed result is independent of the classical names.
example {H K : Qudit} (e : Ensemble H (Fin 2)) (Φ : QuantumChannel H K) :
    ((e.reindex (Equiv.swap 0 1)).map Φ).mix = Φ.map e.mix := by simp

private def correlated : Density (Qubit ⊗ Qubit) :=
  Density.mix (1 / 2) (by norm_num) (by norm_num) ((ρ₀).tensor ρ₀) ((ρ₁).tensor ρ₁)

example : correlated.IsSeparable :=
  (Density.isSeparable_tensor ρ₀ ρ₀).mix (Density.isSeparable_tensor ρ₁ ρ₁) _ _ _

-- A separable state may have classical correlations and therefore fail to be a product.
example : correlated ≠ correlated.partialTraceRight.tensor correlated.partialTraceLeft := by
  intro h
  have he := congrArg (fun ρ : Density (Qubit ⊗ Qubit) =>
    ρ.op (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 1)) h
  norm_num [correlated, Density.partialTraceRight_mix, Density.partialTraceLeft_mix,
    Density.op_mix, Operator.tensor_apply, LinearMap.add_apply, LinearMap.smul_apply] at he
  have hn := congrArg ((ZBasis 2).toBasis.tensorProduct (ZBasis 2).toBasis).repr he
  have hc := congrArg (fun f => f (0, 1)) hn
  norm_num [map_smul] at hc

-- Local noise on two different factors preserves a correlated separable input.
example (Φ : QuantumChannel Qubit (std 3)) (Ψ : QuantumChannel Qubit (std 4)) :
    ((Φ.tensor Ψ).map correlated).IsSeparable :=
  ((Density.isSeparable_tensor ρ₀ ρ₀).mix
    (Density.isSeparable_tensor ρ₁ ρ₁) _ _ _).map_tensor Φ Ψ

-- Impossible outcomes get a fallback label but still contribute zero operator.
example (fallback : Density Qubit) :
    ((POVM.computational 2).luders.outputEnsemble ρ₀ fallback).state 1 = fallback := by
  simp [Instrument.outputEnsemble, Ensemble.ofWeights, POVM.probability_luders,
    POVM.computational, POVM.probability_ofBasis_pure]

-- The unread mixed output cannot depend on how impossible labels were filled.
example {H K : Qudit} {ι : Type*} [Fintype ι] (I : Instrument H K ι) (ρ : Density H)
    (σ τ : Density K) : (I.outputEnsemble ρ σ).mix = (I.outputEnsemble ρ τ).mix := by simp

-- Qubit measurement may prepare qutrits: no equal-dimension assumption is introduced.
example : ((POVM.computational 2).measurePrepare
    (fun i => Density.pure (UnitState.ofBasis (ZBasis 3) (Fin.castSucc i)))).map ρ₁ =
      Density.pure (UnitState.ofBasis (ZBasis 3) (1 : Fin 3)) := by
  apply Density.ext
  rw [QuantumChannel.op_map, POVM.measurePrepare_apply]
  simp [POVM.computational, POVM.ofBasis, Operator.trace_mul_outer, Operator.outer_apply]

-- For a Bell input, the reference dimension is retained and the output is separable.
example (σ : Fin 2 → Density (std 3)) :
    (((QuantumChannel.id Qubit).tensor ((POVM.computational 2).measurePrepare σ)).map
      bellDensity).IsSeparable :=
  (POVM.computational 2).isEntanglementBreaking_measurePrepare σ Qubit bellDensity

-- Categorical execution prepares exactly the ensemble mixture.
example {H K : Qudit} {ι : Type*} [Fintype ι] (M : POVM H ι)
    (σ : ι → Density K) (ρ : Density H) :
    ρ.toState ≫ (M.measurePrepare σ) = (M.prepareEnsemble σ ρ).mix.toState := by
  rw [Density.toState_comp, M.map_measurePrepare]

-- Replacement does not need an inhabited input space, even in dimension zero.
example : QuantumChannel (std 0) Qubit := QuantumChannel.replacement (std 0) ρ₀

end
