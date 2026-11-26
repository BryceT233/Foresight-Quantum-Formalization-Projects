/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Category.Instrument
public import FQFP.CQM.Qudit.Channel.Process.Effect
public import FQFP.CQM.Qudit.Channel.Process.Semiadditive
public import FQFP.CQM.Qudit.Measurement.Luders
public import FQFP.CQM.Qudit.Measurement.ClassicalRegister

/-!
# POVMs and instruments as CP processes

The existing POVM effects become trace-nonincreasing CP effects. An instrument retains
its unnormalized CP branches, and discarding each branch gives its induced POVM.
Preparation and effect composition recovers the existing Born probabilities. Recorded
measurements are deterministic, but selecting an individual outcome need not be.
Conditional density states are used only at strictly positive probability.

## Main definitions and results

* `Qudit.POVM.effect`: a POVM outcome as a categorical CP effect.
* `Qudit.Instrument.branchCPMap`: an instrument outcome as a completely positive process.
* `Qudit.Instrument.toPOVM`: the POVM obtained by discarding each branch output.
* `Qudit.POVM.toPOVM_luders`: the Lüders instrument realizes its original POVM.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped ComplexOrder BigOperators

namespace Qudit

noncomputable section

namespace POVM

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- A POVM outcome as a CP effect, rather than an amplitude bra. -/
def effect (M : POVM H ι) (i : ι) : (⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit :=
  CPQudit.effectOfPositive (M.op i) (M.positive i)

/-- The outcome effect evaluates its trace pairing on every input operator. -/
lemma effect_apply (M : POVM H ι) (i : ι) (A : Operator H) :
    (M.effect i).toSuperoperator A = (M.op i * A).trace • 1 :=
  CPQudit.effectOfPositive_apply _ _ _

/-- Every individual outcome is trace-nonincreasing. -/
lemma effect_isTraceNonincreasing (M : POVM H ι) (i : ι) :
    (M.effect i).toSuperoperator.IsTraceNonincreasing :=
  (CPQudit.effectOfPositive_isTraceNonincreasing_iff _ _).mpr (M.op_le_one i)

/-- Summing outcome effects is discarding, as equality on the full operator algebra. -/
lemma sum_effect (M : POVM H ι) :
    ∑ i, (M.effect i).toSuperoperator = (CPQudit.discard ⟨H⟩).toSuperoperator := by
  apply LinearMap.ext
  intro A
  simp only [LinearMap.sum_apply, M.effect_apply, ← Finset.sum_smul, ← map_sum,
    ← Finset.sum_mul, M.sum_op, one_mul]
  rfl

/-- POVM normalization as an equality of CP arrows. -/
lemma sum_effect_eq_discard (M : POVM H ι) : ∑ i, M.effect i = CPQudit.discard ⟨H⟩ :=
  CPQudit.hom_ext ((CPMap.toSuperoperator_sum _ _).trans M.sum_effect)

/-- The effects of a POVM form an instrument with trivial output. -/
lemma isInstrument_effect (M : POVM H ι) : CPQudit.discarding.IsInstrument M.effect :=
  (CPQudit.discarding.isInstrument_effect_iff _).mpr M.sum_effect_eq_discard

/-- A measurement is determined by its categorical outcome effects. -/
lemma ext_effect {M N : POVM H ι} (h : ∀ i, M.effect i = N.effect i) : M = N := by
  apply POVM.ext
  funext i
  exact CPQudit.eq_of_effectOfPositive_eq (h i)

/-- Preparation followed by an outcome has exactly the existing Born probability. -/
lemma scalarValue_toCPState_comp_effect (M : POVM H ι) (ρ : Density H) (i : ι) :
    CPQudit.scalarValue (ρ.toCPState ≫ M.effect i) = M.probability ρ i :=
  ρ.scalarValue_comp_effect _ _

/-- Basis outcomes agree with the pure-to-mixed interpretation of basis bras. -/
lemma effect_ofBasis (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    (ofBasis b).effect i = CPQudit.pure.map (braArrow (b i)) :=
  CPQudit.effectOfPositive_outer (b i)

/-- On a basis preparation the matching CP effect returns the identity scalar
and each other effect returns zero. -/
lemma toCPState_ofBasis_comp_effect [DecidableEq ι] (b : OrthonormalBasis ι ℂ H.state)
    (i j : ι) :
    (Density.pure (UnitState.ofBasis b i)).toCPState ≫ (ofBasis b).effect j =
      if i = j then 𝟙 _ else 0 := by
  apply CPQudit.state_ext
  rw [CPQudit.hom_comp, LinearMap.comp_apply, Density.toCPState_one, effect_apply,
    ← probability_eq_trace, probability_ofBasis_ofBasis]
  split_ifs
  · simp
  · simp only [Complex.ofReal_zero, zero_smul]
    rfl

end POVM

namespace Instrument

variable {H K L C : Qudit} {ι : Type*} [Fintype ι]

/-- An existing instrument branch regarded as a categorical CP process. -/
def branchCPMap (I : Instrument H K ι) (i : ι) : (⟨H⟩ : CPQudit) ⟶ ⟨K⟩ :=
  ⟨I.branch i, I.completelyPositive i⟩

/-- Forgetting the branch wrapper recovers the original superoperator. -/
@[simp]
lemma toSuperoperator_branchCPMap (I : Instrument H K ι) (i : ι) :
    (I.branchCPMap i).toSuperoperator = I.branch i := rfl

/-- An individual branch need not preserve trace, but cannot increase it. -/
lemma branchCPMap_isTraceNonincreasing (I : Instrument H K ι) (i : ι) :
    (I.branchCPMap i).toSuperoperator.IsTraceNonincreasing :=
  fun _ hA => I.trace_branch_le i hA

/-- Forgetting the outcome sums the original CP branches. -/
lemma sum_branchCPMap (I : Instrument H K ι) :
    ∑ i, (I.branchCPMap i).toSuperoperator = I.toChannel.toCPMap.toSuperoperator := rfl

/-- Build an instrument from CP arrows satisfying categorical normalization. -/
def ofCPMaps (f : ι → ((⟨H⟩ : CPQudit) ⟶ ⟨K⟩)) (hf : CPQudit.discarding.IsInstrument f) :
    Instrument H K ι where
  branch i := (f i).toSuperoperator
  completelyPositive i := (f i).completelyPositive
  tracePreserving := by
    rw [← CPMap.toSuperoperator_sum]
    exact (CPQudit.isCausal_iff _).mp hf

/-- Forgetting outcomes takes the sum inside the CP process category. -/
lemma sum_branchCPMap_eq (I : Instrument H K ι) : ∑ i, I.branchCPMap i = I.toChannel.toCPMap :=
  CPQudit.hom_ext ((CPMap.toSuperoperator_sum _ _).trans I.sum_branchCPMap)

/-- Concrete instruments are exactly finite CP families with causal total. -/
def cpMapEquiv : Instrument H K ι ≃
    {f : ι → ((⟨H⟩ : CPQudit) ⟶ ⟨K⟩) // CPQudit.discarding.IsInstrument f} where
  toFun I := ⟨I.branchCPMap, by
    rw [CQM.Discarding.IsInstrument, I.sum_branchCPMap_eq]
    exact (CPQudit.isCausal_iff _).mpr I.tracePreserving⟩
  invFun f := ofCPMaps f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Run a second instrument selected by the first outcome and retain both outcomes. -/
def bind {κ : Type*} [Fintype κ] (I : Instrument H K ι) (J : ι → Instrument K L κ) :
    Instrument H L (ι × κ) :=
  ofCPMaps _ ((cpMapEquiv I).2.bind (g := fun i => (J i).branchCPMap)
    (fun i => (cpMapEquiv (J i)).2))

/-- The branch labeled by a pair is the sequential composite of the selected branches. -/
lemma branchCPMap_bind {κ : Type*} [Fintype κ] (I : Instrument H K ι)
    (J : ι → Instrument K L κ) (i : ι) (j : κ) :
    (I.bind J).branchCPMap (i, j) = I.branchCPMap i ≫ (J i).branchCPMap j := rfl

/-- Forgetting only the second outcome gives the first branch followed by its chosen channel. -/
lemma sum_branchCPMap_bind {κ : Type*} [Fintype κ] (I : Instrument H K ι)
    (J : ι → Instrument K L κ) (i : ι) :
    ∑ j, (I.bind J).branchCPMap (i, j) = I.branchCPMap i ≫ (J i).toChannel.toCPMap := by
  simp only [branchCPMap_bind, ← Semiadditive.comp_sum, sum_branchCPMap_eq]

/-- For a fixed second instrument, forgetting both outcomes composes the two channels. -/
lemma toChannel_bind_const {κ : Type*} [Fintype κ] (I : Instrument H K ι) (J : Instrument K L κ) :
    (I.bind (fun _ => J)).toChannel = J.toChannel.comp I.toChannel := by
  apply CausalQudit.inclusion.map_injective (X := ⟨H⟩) (Y := ⟨L⟩)
  have h := Semiadditive.sum_comp_sum I.branchCPMap J.branchCPMap
  rw [I.sum_branchCPMap_eq, J.sum_branchCPMap_eq] at h
  exact (I.bind (fun _ => J)).sum_branchCPMap_eq.symm.trans h.symm

/-- Discarding after each branch determines the instrument's operator POVM. -/
def toPOVM (I : Instrument H K ι) : POVM H ι where
  op i := (I.branchCPMap i).dual.toSuperoperator 1
  positive i := (I.branchCPMap i).dual.completelyPositive.isPositive 1 LinearMap.isPositive_one
  sum_op := by
    apply Operator.ext_trace
    intro A
    simp only [Finset.sum_mul, map_sum, CPMap.trace_dual, one_mul]
    exact I.sum_trace_branch A

/-- The induced POVM effect is precisely the branch followed by discarding. -/
lemma effect_toPOVM (I : Instrument H K ι) (i : ι) :
    I.toPOVM.effect i = I.branchCPMap i ≫ CPQudit.discard ⟨K⟩ :=
  (CPQudit.comp_discard_eq_effect _).symm

/-- An instrument with trivial quantum output already consists of its outcome effects. -/
lemma effect_toPOVM_of_effects (e : ι → ((⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit))
    (he : CPQudit.discarding.IsInstrument e) (i : ι) :
    (ofCPMaps e he).toPOVM.effect i = e i := by
  rw [effect_toPOVM]
  change e i ≫ CPQudit.discard (𝟙_ CPQudit) = e i
  rw [CPQudit.discard_unit, Category.comp_id]

/-- The induced POVM retains the instrument's outcome probabilities. -/
lemma probability_toPOVM (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    I.toPOVM.probability ρ i = I.probability ρ i := by
  change (((I.branchCPMap i).dual.toSuperoperator 1 * ρ.op).trace).re = _
  rw [CPMap.trace_dual, one_mul]
  rfl

/-- A complete branch experiment returns the existing instrument probability. -/
lemma scalarValue_branch (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    CPQudit.scalarValue (ρ.toCPState ≫ I.branchCPMap i ≫ CPQudit.discard ⟨K⟩) =
      I.probability ρ i := by
  rw [← effect_toPOVM, POVM.scalarValue_toCPState_comp_effect, probability_toPOVM]

/-- Reading a recorded classical result recovers the original branch as a CP arrow. -/
lemma record_comp_read (I : Instrument H K ι) (b : OrthonormalBasis ι ℂ C.state) (i : ι) :
    (I.record b).toCPMap ≫ (read K b).branchCPMap i = I.branchCPMap i := by
  apply CPQudit.hom_ext
  apply LinearMap.ext
  exact fun A => I.read_record b A i

/-- Outcome-dependent channel processing agrees with categorical branch composition. -/
lemma branchCPMap_postprocess (I : Instrument H K ι) (Φ : ι → QuantumChannel K L) (i : ι) :
    (I.postprocess Φ).branchCPMap i = I.branchCPMap i ≫ (Φ i).toCPMap := rfl

/-- Outcome-dependent deterministic processing preserves the induced measurement. -/
lemma toPOVM_postprocess (I : Instrument H K ι) (Φ : ι → QuantumChannel K L) :
    (I.postprocess Φ).toPOVM = I.toPOVM := by
  apply POVM.ext_effect
  intro i
  rw [effect_toPOVM, effect_toPOVM, branchCPMap_postprocess]
  exact ((CPQudit.isCausal_iff _).mpr (Φ i).tracePreserving).comp_discard_eq _

/-- After a possible outcome, its unnormalized CP state is its probability times its density. -/
lemma toCPState_comp_branch_conditional (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : 0 < I.probability ρ i) :
    (ρ.toCPState ≫ I.branchCPMap i).toSuperoperator =
      (I.probability ρ i : ℂ) • (I.conditional ρ i hp).toCPState.toSuperoperator := by
  apply Superoperator.ext_unit
  change I.branch i (ρ.toCPState.toSuperoperator 1) =
    ((I.probability ρ i : ℂ) • (I.conditional ρ i hp).toCPState.toSuperoperator) 1
  rw [Density.toCPState_one, LinearMap.smul_apply, Density.toCPState_one]
  exact (I.probability_smul_conditional ρ i hp).symm

/-- An impossible result gives the zero process on the scalar input, with no default density. -/
lemma toCPState_comp_branch_eq_zero (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : I.probability ρ i = 0) :
    (ρ.toCPState ≫ I.branchCPMap i).toSuperoperator = 0 := by
  apply Superoperator.ext_unit
  change I.branch i (ρ.toCPState.toSuperoperator 1) = 0
  rw [Density.toCPState_one]
  exact I.branch_eq_zero_of_probability_eq_zero ρ i hp

end Instrument

namespace POVM

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- In the Schrödinger picture a POVM is equivalently a finite family of CP effects
whose sum is discarding, including when the outcome type is empty. -/
def effectFamilyEquiv : POVM H ι ≃
    {e : ι → ((⟨H⟩ : CPQudit) ⟶ 𝟙_ CPQudit) // ∑ i, e i = CPQudit.discard ⟨H⟩} where
  toFun M := ⟨M.effect, M.sum_effect_eq_discard⟩
  invFun e := (Instrument.ofCPMaps e.1
    ((CPQudit.discarding.isInstrument_effect_iff _).mpr e.2)).toPOVM
  left_inv M := ext_effect (Instrument.effect_toPOVM_of_effects M.effect _)
  right_inv e := Subtype.ext (funext (Instrument.effect_toPOVM_of_effects e.1 _))

/-- Pull a whole measurement back along a quantum channel by composing its CP effects. -/
def pullback {K : Qudit} (M : POVM K ι) (Φ : QuantumChannel H K) : POVM H ι :=
  (Instrument.ofCPMaps (fun i => Φ.toCPMap ≫ M.effect i)
    (M.isInstrument_effect.precomp ((CPQudit.isCausal_iff _).mpr Φ.tracePreserving))).toPOVM

/-- Heisenberg transport of a POVM is precomposition of its outcome effects. -/
lemma effect_pullback {K : Qudit} (M : POVM K ι) (Φ : QuantumChannel H K) (i : ι) :
    (M.pullback Φ).effect i = Φ.toCPMap ≫ M.effect i :=
  Instrument.effect_toPOVM_of_effects _ _ i

/-- In operator coordinates the same pullback is the trace-pairing dual of the channel. -/
lemma op_pullback {K : Qudit} (M : POVM K ι) (Φ : QuantumChannel H K) (i : ι) :
    (M.pullback Φ).op i = Φ.toCPMap.dual.toSuperoperator (M.op i) :=
  CPQudit.eq_of_effectOfPositive_eq ((M.effect_pullback Φ i).trans
    (CPQudit.comp_effectOfPositive Φ.toCPMap (M.op i) (M.positive i)))

/-- Pulling back the measurement gives the same Born probability as evolving the state. -/
lemma probability_pullback {K : Qudit} (M : POVM K ι) (Φ : QuantumChannel H K)
    (ρ : Density H) (i : ι) : (M.pullback Φ).probability ρ i = M.probability (Φ.map ρ) i := by
  rw [← scalarValue_toCPState_comp_effect, effect_pullback, ← Category.assoc,
    Density.toCPState_comp, scalarValue_toCPState_comp_effect]

/-- The POVM induced by the Lüders instrument is the original POVM. -/
@[simp]
lemma toPOVM_luders (M : POVM H ι) : M.luders.toPOVM = M := by
  apply POVM.ext
  funext i
  apply Operator.ext_trace
  intro A
  change (((M.luders.branchCPMap i).dual.toSuperoperator 1) * A).trace = _
  rw [CPMap.trace_dual, one_mul]
  exact M.trace_luders_branch i A

/-- Discarding a Lüders output leaves exactly its original POVM effect. -/
lemma branchCPMap_luders_comp_discard (M : POVM H ι) (i : ι) :
    M.luders.branchCPMap i ≫ CPQudit.discard ⟨H⟩ = M.effect i := by
  rw [← Instrument.effect_toPOVM, toPOVM_luders]

end POVM

end

end Qudit
