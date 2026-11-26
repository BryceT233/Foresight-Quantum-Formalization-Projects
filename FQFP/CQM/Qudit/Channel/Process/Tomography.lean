/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Process.State
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Pure preparations distinguish quantum channels

Complex polarization recovers an operator from its expectations on unit vectors.
Trace duality then shows that agreement on pure inputs determines a quantum channel.
In particular the tensor unit separates arrows of the causal category, as in
Definition 1.12 of *Categorical Quantum Mechanics*.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit

variable {H K : Qudit}

/-- Pure-state complex expectations determine an arbitrary operator. -/
lemma Operator.ext_expectationComplex_pure {A B : Operator H}
    (h : ∀ v : UnitState H, (Density.pure v).expectationComplex A =
      (Density.pure v).expectationComplex B) : A = B := by
  apply (ext_inner_map A B).mp
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let v : UnitState H := ⟨NormedSpace.normalize x,
    inner_self_eq_one_of_norm_eq_one (NormedSpace.norm_normalize hx)⟩
  have he := congrArg (starRingEnd ℂ) (h v)
  simp only [Density.expectationComplex_pure, inner_conj_symm] at he
  have hv : (‖x‖ : ℂ) • v.val = x := by
    simpa only [Complex.coe_smul] using NormedSpace.norm_smul_normalize x
  rw [← hv, map_smul, map_smul, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, he]

/-- Agreement on pure input densities suffices for equality on all input operators. -/
lemma QuantumChannel.ext_map_pure {Φ Ψ : QuantumChannel H K}
    (h : ∀ v : UnitState H, Φ.map (Density.pure v) = Ψ.map (Density.pure v)) : Φ = Ψ := by
  apply QuantumChannel.asCPHom_injective
  suffices hd : Φ.toCPMap.dual = Ψ.toCPMap.dual by
    simpa only [CPMap.dual_dual] using congrArg CPMap.dual hd
  apply CPMap.ext
  apply LinearMap.ext
  intro B
  apply Operator.ext_expectationComplex_pure
  intro v
  simp only [Density.expectationComplex, CPMap.trace_dual]
  exact congrArg (fun ρ : Density K => (B * ρ.op).trace) (h v)

/-- The causal category is well-pointed, including on zero-dimensional systems. -/
theorem CausalQudit.isSeparator_tensorUnit : IsSeparator (𝟙_ CausalQudit) := by
  apply (isSeparator_def _).mpr
  intro X Y f g h
  apply QuantumChannel.ext_map_pure
  intro v
  apply Density.toState_injective
  simpa only [Density.toState_comp] using h (Density.pure v).toState

end Qudit
