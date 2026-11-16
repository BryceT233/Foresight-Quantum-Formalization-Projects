/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Effect
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

/-- Preparation followed by an outcome has exactly the existing Born probability. -/
lemma scalarValue_toCPState_comp_effect (M : POVM H ι) (ρ : Density H) (i : ι) :
    CPQudit.scalarValue (ρ.toCPState ≫ M.effect i) = M.probability ρ i :=
  ρ.scalarValue_comp_effect _ _

/-- Basis outcomes agree with the pure-to-mixed interpretation of basis bras. -/
lemma effect_ofBasis (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    (ofBasis b).effect i = CPQudit.pure.map (braArrow (b i)) :=
  CPQudit.effectOfPositive_outer (b i)

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
