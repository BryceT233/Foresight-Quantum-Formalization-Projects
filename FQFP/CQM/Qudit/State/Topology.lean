/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
Physlib reference for the topology and compactness of density states.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Error.TraceDistance
public import FQFP.CQM.Qudit.State.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Topology of density operators

Trace distance metrizes the subspace topology from the operator norm. The density operators
form a compact space, including when the state space is zero-dimensional.
-/

@[expose] public section

open scoped ComplexOrder

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

instance : MetricSpace (Density H) where
  dist := traceDistance
  dist_self := traceDistance_self
  dist_comm := traceDistance_comm
  dist_triangle := traceDistance_triangle
  eq_of_dist_eq_zero := fun {ρ σ} => (traceDistance_eq_zero_iff ρ σ).mp

/-- Metric distance between density operators is their trace distance. -/
lemma dist_eq_traceDistance (ρ σ : Density H) : dist ρ σ = ρ.traceDistance σ := rfl

private def halfTraceFunctional (H : Qudit) : Operator H →ₗ[ℂ] (Operator H →L[ℂ] ℂ) where
  toFun A := (2 : ℂ)⁻¹ • (LinearMap.traceFunctional A).comp
    (Operator.continuousLinearMapEquiv H).toContinuousLinearEquiv.toContinuousLinearMap
  map_add' A B := by
    rw [LinearMap.traceFunctional_add, ContinuousLinearMap.add_comp, smul_add]
  map_smul' c A := by
    rw [LinearMap.traceFunctional_smul, ContinuousLinearMap.smul_comp, smul_comm]
    rfl

private lemma norm_halfTraceFunctional (A : Operator H) :
    ‖halfTraceFunctional H A‖ = LinearMap.traceNorm A / 2 := by
  change ‖(2 : ℂ)⁻¹ • (LinearMap.traceFunctional A).comp _‖ = _
  rw [norm_smul, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_inv,
    Complex.norm_two, inv_mul_eq_div, LinearMap.traceNorm]

private lemma isClosedEmbedding_halfTraceFunctional :
    Topology.IsClosedEmbedding (halfTraceFunctional H) := by
  apply LinearMap.isClosedEmbedding_of_injective
  rw [LinearMap.ker_eq_bot']
  intro A h
  let : NormedAddCommGroup (Operator H →L[ℂ] ℂ) := inferInstance
  have hn := norm_halfTraceFunctional A
  rw [h, norm_zero, eq_comm, div_eq_zero_iff] at hn
  exact (LinearMap.traceNorm_eq_zero_iff _).mp (hn.resolve_right (by norm_num))

private lemma isometry_halfTraceFunctional_op :
    Isometry (fun ρ : Density H =>
      halfTraceFunctional H ρ.op) := by
  apply Isometry.of_dist_eq
  intro ρ σ
  rw [dist_eq_norm_sub]
  rw [← map_sub]
  exact norm_halfTraceFunctional _

/-- Density operators embed as a closed subspace of the operator-norm space. -/
theorem isClosedEmbedding_op :
    Topology.IsClosedEmbedding (fun ρ : Density H => ρ.op) := by
  refine ⟨isClosedEmbedding_halfTraceFunctional.isEmbedding.of_comp_iff.mp
    isometry_halfTraceFunctional_op.isEmbedding, ?_⟩
  have hr : Set.range (fun ρ : Density H => ρ.op) =
      Set.Ici 0 ∩ {A : Operator H | LinearMap.trace ℂ H.state A = 1} := by
    ext A
    constructor
    · rintro ⟨ρ, rfl⟩
      exact ⟨LinearMap.nonneg_iff_isPositive.mpr ρ.positive, ρ.trace_one⟩
    · rintro ⟨hp, ht⟩
      exact ⟨⟨A, LinearMap.nonneg_iff_isPositive.mp hp, ht⟩, rfl⟩
  rw [hr]
  exact isClosed_Ici.inter (isClosed_eq (LinearMap.trace ℂ H.state).continuous_of_finiteDimensional
    continuous_const)

/-- The underlying operator varies continuously in operator norm. -/
@[fun_prop]
lemma continuous_op :
    Continuous (fun ρ : Density H => ρ.op) :=
  isClosedEmbedding_op.continuous

instance : CompactSpace (Density H) := by
  let D := Operator H →L[ℂ] ℂ
  let : ProperSpace D := FiniteDimensional.proper ℂ _
  have he := isClosedEmbedding_halfTraceFunctional.comp
    (isClosedEmbedding_op (H := H))
  constructor
  have hc := he.isCompact_preimage (isCompact_closedBall (0 : D) (1 / 2))
  convert hc using 1
  symm
  apply Set.eq_univ_of_forall
  intro ρ
  change dist (halfTraceFunctional H ρ.op) 0 ≤ 1 / 2
  rw [dist_zero_right, norm_halfTraceFunctional, traceNorm_op]

/-- The expectation in a fixed state depends continuously on the observable. -/
@[fun_prop]
lemma continuous_expectation (ρ : Density H) :
    Continuous (fun A : Operator H => ρ.expectation A) :=
  Complex.continuous_re.comp <| LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℂ H.state) ∘ₗ LinearMap.mulRight ℂ ρ.op)

/-- An effect's acceptance probability is 1-Lipschitz in the input density operator. -/
lemma lipschitzWith_expectation {A : Operator H} (h₀ : 0 ≤ A) (h₁ : A ≤ 1) :
    LipschitzWith 1 (fun ρ : Density H => ρ.expectation A) := by
  apply LipschitzWith.of_dist_le_mul
  intro ρ σ
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_traceDistance] using
    ρ.abs_expectation_sub_le_traceDistance σ h₀ h₁

end

end Qudit.Density
