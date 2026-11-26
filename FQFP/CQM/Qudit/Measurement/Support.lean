/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Measurement.POVM
public import FQFP.CQM.Qudit.State.Support

/-!
# Supports and measurement outcomes

An impossible outcome annihilates the support of the input density. A certain outcome
acts as the identity there. These criteria characterize perfect binary discrimination and
give an operational interpretation of absolute continuity in terms of impossible outcomes.
-/

@[expose] public section

namespace Qudit

variable {H : Qudit} {ι : Type*} [Fintype ι]

namespace POVM

/-- A POVM outcome is impossible exactly when its effect kills the support. -/
lemma probability_eq_zero_iff (M : POVM H ι) (ρ : Density H) (i : ι) :
    M.probability ρ i = 0 ↔ ρ.support ≤ LinearMap.ker (M.op i) :=
  ρ.expectation_eq_zero_iff (M.positive i)

/-- A POVM outcome is certain exactly when its effect fixes the support. -/
lemma probability_eq_one_iff (M : POVM H ι) (ρ : Density H) (i : ι) :
    M.probability ρ i = 1 ↔ ρ.support ≤ LinearMap.ker (1 - M.op i) :=
  ρ.expectation_eq_one_iff (M.op_le_one i)

/-- A subspace test accepts with probability zero exactly for support orthogonal to it. -/
lemma probability_ofSubmodule_eq_zero_iff (S : Submodule ℂ H.state) (ρ : Density H) :
    (ofSubmodule S).probability ρ true = 0 ↔ ρ.support ⟂ S := by
  rw [probability_eq_zero_iff, Submodule.isOrtho_iff_le, ← S.ker_starProjection]
  rfl

/-- A subspace test accepts with certainty exactly when it contains the state's support. -/
lemma probability_ofSubmodule_eq_one_iff (S : Submodule ℂ H.state) (ρ : Density H) :
    (ofSubmodule S).probability ρ true = 1 ↔ ρ.support ≤ S := by
  rw [probability_eq_one_iff]
  change ρ.support ≤ LinearMap.ker (1 - S.starProjection.toLinearMap) ↔ _
  have hk : LinearMap.ker (1 - S.starProjection.toLinearMap) = S := by
    ext x
    change x - S.starProjection x = 0 ↔ x ∈ S
    rw [sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]
  rw [hk]

/-- A binary measurement distinguishes two states perfectly exactly for orthogonal supports. -/
theorem exists_probability_one_zero_iff (ρ σ : Density H) :
    (∃ M : POVM H Bool, M.probability ρ true = 1 ∧ M.probability σ true = 0) ↔
      ρ.support ⟂ σ.support := by
  constructor
  · rintro ⟨M, hρ, hσ⟩
    have hfix := (M.probability_eq_one_iff ρ true).mp hρ
    have hr : ρ.support ≤ LinearMap.range (M.op true) := by
      intro x hx
      have he : x - M.op true x = 0 := hfix hx
      exact ⟨x, (sub_eq_zero.mp he).symm⟩
    have ho : σ.support ⟂ LinearMap.range (M.op true) := by
      rw [Submodule.isOrtho_iff_le, (M.positive true).isSymmetric.orthogonal_range]
      exact (M.probability_eq_zero_iff σ true).mp hσ
    exact ho.symm.mono_left hr
  · intro ho
    exact ⟨ofSubmodule ρ.support, (probability_ofSubmodule_eq_one_iff _ _).mpr le_rfl,
      (probability_ofSubmodule_eq_zero_iff _ _).mpr ho.symm⟩

end POVM

/-- Under support inclusion every impossible outcome for the reference is impossible for the
source, for any finite measurement. -/
lemma Density.AbsolutelyContinuous.probability_eq_zero {ρ σ : Density H}
    (h : ρ.AbsolutelyContinuous σ) (M : POVM H ι) (i : ι) (hi : M.probability σ i = 0) :
    M.probability ρ i = 0 :=
  (M.probability_eq_zero_iff ρ i).mpr
    (((ρ.absolutelyContinuous_iff_support_le σ).mp h).trans ((M.probability_eq_zero_iff σ i).mp hi))

/-- Binary measurements suffice to characterize quantum absolute continuity by null outcomes. -/
theorem Density.absolutelyContinuous_iff_forall_probability_eq_zero (ρ σ : Density H) :
    ρ.AbsolutelyContinuous σ ↔
      ∀ M : POVM H Bool, M.probability σ true = 0 → M.probability ρ true = 0 := by
  refine ⟨fun h M => h.probability_eq_zero M true, fun h => ?_⟩
  have hz := h (POVM.ofSubmodule σ.supportᗮ)
    ((POVM.probability_ofSubmodule_eq_zero_iff _ _).mpr (Submodule.isOrtho_orthogonal_right _))
  rw [POVM.probability_ofSubmodule_eq_zero_iff, Submodule.isOrtho_iff_le,
    Submodule.orthogonal_orthogonal] at hz
  exact (ρ.absolutelyContinuous_iff_support_le σ).mpr hz

end Qudit
