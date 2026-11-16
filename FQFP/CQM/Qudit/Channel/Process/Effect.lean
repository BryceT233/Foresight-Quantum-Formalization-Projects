/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.State

/-!
# Positive effects in the CP process category

Positive operators are precisely CP effects. The effect associated to `E` sends `A`
to `Tr(EA)` on the scalar system. Trace-nonincreasing effects correspond to `E ≤ 1`;
deterministic effects correspond to the identity operator, hence to discarding.
Composing a density preparation with an effect evaluates the Born pairing directly,
without squaring an already probabilistic scalar.

## Main definitions and results

* `Qudit.CPQudit.effectEquiv`: positive operators correspond to categorical CP effects.
* `Qudit.CPQudit.boundedEffectEquiv`: bounded positive operators correspond to subnormalized
  effects.
* `Qudit.CPQudit.scalarValue`: the nonnegative real value of a CP scalar.
* `Qudit.Density.scalarValue_comp_effect`: the preparation-effect pairing gives the expectation.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped ComplexOrder

namespace Qudit

noncomputable section

namespace Operator

/-- A positive operator is bounded by one exactly when all positive trace tests are bounded. -/
lemma le_one_iff_trace_mul_le {H : Qudit} {E : Operator H} (hE : E.IsPositive) :
    E ≤ 1 ↔ ∀ A : Operator H, A.IsPositive → (E * A).trace ≤ A.trace := by
  constructor
  · intro h A hA
    have ht := (LinearMap.le_def.mp h).trace_mul_nonneg hA
    simpa only [sub_mul, one_mul, map_sub, sub_nonneg] using ht
  · intro h
    apply LinearMap.le_def.mpr
    apply (LinearMap.isPositive_iff _).mpr
    refine ⟨LinearMap.IsSymmetric.one.sub hE.isSymmetric, fun x => ?_⟩
    have hx := h (outer x x) (isPositive_outer x)
    rw [trace_mul_outer, trace_outer, ← hE.isSymmetric x x] at hx
    simpa only [LinearMap.sub_apply, Module.End.one_apply, inner_sub_left, sub_nonneg] using hx

end Operator

namespace Superoperator

/-- A process does not increase the trace of any positive input operator. -/
def IsTraceNonincreasing {H K : Qudit} (Φ : Superoperator H K) : Prop :=
  ∀ A : Operator H, A.IsPositive → (Φ A).trace ≤ A.trace

end Superoperator

namespace CPMap

/-- Trace nonincrease is subunitality of the Heisenberg dual, including in dimension zero. -/
lemma isTraceNonincreasing_iff_dual_one_le {H K : Qudit} (f : CPMap H K) :
    f.toSuperoperator.IsTraceNonincreasing ↔ f.dual.toSuperoperator 1 ≤ 1 := by
  rw [Operator.le_one_iff_trace_mul_le
    (f.dual.completelyPositive.isPositive 1 LinearMap.isPositive_one)]
  simp only [Superoperator.IsTraceNonincreasing, trace_dual, one_mul]

end CPMap

namespace CPQudit

variable {H K : Qudit}

/-- The CP effect of a positive operator, with no upper bound assumed. -/
def effectOfPositive (E : Operator H) (hE : E.IsPositive) :
    (⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit := (ofPositive E hE)†

/-- A positive effect is the trace pairing on every operator, including non-Hermitian ones. -/
lemma effectOfPositive_apply (E : Operator H) (hE : E.IsPositive) (A : Operator H) :
    (effectOfPositive E hE).toSuperoperator A = (E * A).trace • 1 := by
  calc
    _ = ((effectOfPositive E hE).toSuperoperator A).trace •
        (1 : Operator (𝟙_ Qudit)) := by
      rw [Operator.trace_scalar]
      exact Operator.scalar_eq _
    _ = _ := by
      congr 1
      have h := (ofPositive E hE).trace_dual (1 : Operator (𝟙_ Qudit)) A
      change ((effectOfPositive E hE).toSuperoperator A * 1).trace =
        (A * Superoperator.prepare E 1).trace at h
      rw [mul_one, Superoperator.prepare_one] at h
      exact h.trans (LinearMap.trace_mul_comm ℂ A E)

/-- Positive operators are exactly CP effects, by the state-effect dagger correspondence. -/
def effectEquiv (H : Qudit) :
    {E : Operator H // E.IsPositive} ≃ ((⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit) where
  toFun E := effectOfPositive E.1 E.2
  invFun f := (stateEquiv H).symm f†
  left_inv E := by
    change (stateEquiv H).symm ((stateEquiv H E)†)† = E
    rw [involutive_dagger, Equiv.symm_apply_apply]
  right_inv f := by
    change ((stateEquiv H) ((stateEquiv H).symm f†))† = f
    rw [Equiv.apply_symm_apply, involutive_dagger]

/-- Discarding is the effect of the identity operator. -/
lemma effectOfPositive_one (H : Qudit) :
    effectOfPositive (1 : Operator H) LinearMap.isPositive_one = discard ⟨H⟩ := by
  apply hom_ext
  apply LinearMap.ext
  intro A
  rw [effectOfPositive_apply, one_mul]
  rfl

/-- A rank-one effect is the CP image of its amplitude bra. -/
lemma effectOfPositive_outer (v : H.state) :
    effectOfPositive (Operator.outer v v) (Operator.isPositive_outer v) =
      pure.map (braArrow v) := by
  change (ofPositive (Operator.outer v v) (Operator.isPositive_outer v))† = _
  exact (congrArg (fun f : 𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit) => f†)
    (ofPositive_outer v)).trans
      ((dagger_pure (ketArrow v)).trans (congrArg pure.map (ketArrow_dagger v)))

/-- Bounded positive operators correspond precisely to trace-nonincreasing effects. -/
lemma effectOfPositive_isTraceNonincreasing_iff (E : Operator H) (hE : E.IsPositive) :
    (effectOfPositive E hE).toSuperoperator.IsTraceNonincreasing ↔ E ≤ 1 := by
  rw [CPMap.isTraceNonincreasing_iff_dual_one_le]
  change (ofPositive E hE).dual.dual.toSuperoperator 1 ≤ 1 ↔ E ≤ 1
  rw [CPMap.dual_dual]
  change Superoperator.prepare E 1 ≤ 1 ↔ E ≤ 1
  rw [Superoperator.prepare_one]

/-- A positive effect is deterministic exactly when its operator is the identity. -/
lemma effectOfPositive_isCausal_iff (E : Operator H) (hE : E.IsPositive) :
    IsCausal (effectOfPositive E hE) ↔ E = 1 := by
  rw [isCausal_iff, CPMap.isTracePreserving_iff_dual_one]
  change (ofPositive E hE).dual.dual.toSuperoperator 1 = 1 ↔ E = 1
  rw [CPMap.dual_dual]
  change Superoperator.prepare E 1 = 1 ↔ E = 1
  rw [Superoperator.prepare_one]

/-- Normalized operator effects are exactly the trace-nonincreasing CP effects. -/
def boundedEffectEquiv (H : Qudit) :
    {E : Operator H // E.IsPositive ∧ E ≤ 1} ≃
      {f : (⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit // f.toSuperoperator.IsTraceNonincreasing} where
  toFun E := ⟨effectOfPositive E.1 E.2.1,
    (effectOfPositive_isTraceNonincreasing_iff E.1 E.2.1).mpr E.2.2⟩
  invFun f := ⟨((effectEquiv H).symm f.1).1, ((effectEquiv H).symm f.1).2, by
    apply (effectOfPositive_isTraceNonincreasing_iff _ _).mp
    change ((effectEquiv H) ((effectEquiv H).symm f.1)).toSuperoperator.IsTraceNonincreasing
    rw [Equiv.apply_symm_apply]
    exact f.2⟩
  left_inv E := by
    apply Subtype.ext
    exact congrArg (fun A : {E : Operator H // E.IsPositive} => A.1)
      ((effectEquiv H).symm_apply_apply ⟨E.1, E.2.1⟩)
  right_inv f := Subtype.ext ((effectEquiv H).apply_symm_apply f.1)

/-- Pulling an effect back through a CP process is its Heisenberg dual action. -/
lemma comp_effectOfPositive (f : (⟨H⟩ : CPQudit) ⟶ ⟨K⟩)
    (E : Operator K) (hE : E.IsPositive) :
    f ≫ effectOfPositive E hE =
      effectOfPositive (f.dual.toSuperoperator E) (f.dual.completelyPositive.isPositive E hE) := by
  apply hom_ext
  apply LinearMap.ext
  intro A
  change (effectOfPositive E hE).toSuperoperator (f.toSuperoperator A) = _
  rw [effectOfPositive_apply, effectOfPositive_apply, f.trace_dual]

/-- Discarding a process output extracts its Heisenberg effect at one. -/
lemma comp_discard_eq_effect (f : (⟨H⟩ : CPQudit) ⟶ ⟨K⟩) :
    f ≫ discard ⟨K⟩ = effectOfPositive (f.dual.toSuperoperator 1)
      (f.dual.completelyPositive.isPositive 1 LinearMap.isPositive_one) := by
  rw [← effectOfPositive_one, comp_effectOfPositive]

/-- The real value of a CP scalar. It is a weight, not an amplitude. -/
def scalarValue (s : 𝟙_ CPQudit ⟶ 𝟙_ CPQudit) : ℝ := (s.toSuperoperator 1).trace.re

/-- CP scalars have nonnegative real values. -/
lemma scalarValue_nonneg (s : 𝟙_ CPQudit ⟶ 𝟙_ CPQudit) : 0 ≤ scalarValue s :=
  (Complex.nonneg_iff.mp
    (s.completelyPositive.isPositive 1 LinearMap.isPositive_one).trace_nonneg).1

/-- A CP scalar is real, so taking its real value loses no probability data. -/
lemma scalarValue_eq_trace (s : 𝟙_ CPQudit ⟶ 𝟙_ CPQudit) :
    (scalarValue s : ℂ) = (s.toSuperoperator 1).trace := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp
      (s.completelyPositive.isPositive 1 LinearMap.isPositive_one).trace_nonneg).2

end CPQudit

namespace Density

/-- Preparation followed by an effect evaluates the Born trace on any scalar input. -/
lemma toCPState_comp_effect_apply {H : Qudit} (ρ : Density H)
    (E : Operator H) (hE : E.IsPositive) (B : Operator (𝟙_ Qudit)) :
    (ρ.toCPState ≫ CPQudit.effectOfPositive E hE).toSuperoperator B =
      B.trace • ((E * ρ.op).trace • (1 : Operator (𝟙_ Qudit))) := by
  change (CPQudit.effectOfPositive E hE).toSuperoperator
    (ρ.toCPState.toSuperoperator B) = _
  rw [toCPState_apply, map_smul, CPQudit.effectOfPositive_apply]

/-- The categorical scalar is the existing mixed-state expectation, without another square. -/
lemma scalarValue_comp_effect {H : Qudit} (ρ : Density H)
    (E : Operator H) (hE : E.IsPositive) :
    CPQudit.scalarValue (ρ.toCPState ≫ CPQudit.effectOfPositive E hE) = ρ.expectation E := by
  change ((CPQudit.effectOfPositive E hE).toSuperoperator
    (ρ.toCPState.toSuperoperator 1)).trace.re = _
  rw [toCPState_one, CPQudit.effectOfPositive_apply, Operator.trace_scalar]
  simp only [Module.End.one_apply, LinearMap.smul_apply, smul_eq_mul, mul_one]
  rfl

end Density

end

end Qudit
