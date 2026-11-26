/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.Analysis.InnerProductSpace.TraceNorm

/-!
# Finite quantum instruments

An instrument is a finite family of completely positive maps whose sum preserves trace.
Individual branches remain unnormalized. Conditioning requires strictly positive probability;
no default density state is assigned to an impossible outcome.

## Main definitions

* `Qudit.Instrument`: finite completely positive branches whose sum preserves trace.
* `Qudit.Instrument.toChannel`: the channel obtained by forgetting the outcome.
* `Qudit.Instrument.conditional`: the output state conditioned on positive probability.
* `Qudit.Instrument.postprocess`: outcome-dependent channel postprocessing.
-/

@[expose] public section

open scoped BigOperators ComplexOrder

namespace Qudit

/-- A finite quantum instrument, with quantum input/output and a classical outcome. -/
@[ext]
structure Instrument (H K : Qudit) (ι : Type*) [Fintype ι] where
  /-- The unnormalized operation for each outcome. -/
  branch : ι → Superoperator H K
  /-- Each outcome operation is completely positive. -/
  completelyPositive : ∀ i, (branch i).IsCompletelyPositive
  /-- Forgetting the outcome preserves trace. -/
  tracePreserving : (∑ i, branch i).IsTracePreserving

namespace Instrument

noncomputable section

variable {H K L : Qudit} {ι : Type*} [Fintype ι]

/-- The quantum channel obtained by forgetting the classical result. -/
def toChannel (I : Instrument H K ι) : QuantumChannel H K where
  toSuperoperator := ∑ i, I.branch i
  completelyPositive := Superoperator.IsCompletelyPositive.sum _ _ fun i _ => I.completelyPositive i
  tracePreserving := I.tracePreserving

/-- Every unnormalized output of a positive input is positive. -/
lemma branch_positive (I : Instrument H K ι) (i : ι) {A : Operator H}
    (hA : A.IsPositive) : (I.branch i A).IsPositive :=
  (I.completelyPositive i).isPositive A hA

/-- The traces of all branches sum to the input trace, even on nonpositive inputs. -/
lemma sum_trace_branch (I : Instrument H K ι) (A : Operator H) :
    ∑ i, (I.branch i A).trace = A.trace := by
  simpa only [LinearMap.sum_apply, map_sum] using I.tracePreserving A

/-- Each branch is trace-nonincreasing on all positive inputs. -/
lemma trace_branch_le (I : Instrument H K ι) (i : ι) {A : Operator H}
    (hA : A.IsPositive) : (I.branch i A).trace ≤ A.trace := by
  rw [← I.sum_trace_branch A]
  exact Finset.single_le_sum (fun j _ => (I.branch_positive j hA).trace_nonneg)
    (Finset.mem_univ i)

/-- The outcome probability is the real trace of the unnormalized branch. -/
def probability (I : Instrument H K ι) (ρ : Density H) (i : ι) : ℝ :=
  (I.branch i ρ.op).trace.re

/-- Outcome probabilities are nonnegative. -/
lemma probability_nonneg (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    0 ≤ I.probability ρ i :=
  (Complex.nonneg_iff.mp (I.branch_positive i ρ.positive).trace_nonneg).1

/-- The complex branch trace is exactly the real outcome probability. -/
lemma probability_eq_trace (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    (I.probability ρ i : ℂ) = (I.branch i ρ.op).trace := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (I.branch_positive i ρ.positive).trace_nonneg).2

/-- The outcome probabilities sum to one. -/
lemma sum_probability (I : Instrument H K ι) (ρ : Density H) :
    ∑ i, I.probability ρ i = 1 := by
  simpa only [probability, ← Complex.re_sum, ρ.trace_one, Complex.one_re] using
    congrArg Complex.re (I.sum_trace_branch ρ.op)

/-- Each outcome probability is at most one. -/
lemma probability_le_one (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    I.probability ρ i ≤ 1 := by
  rw [← I.sum_probability ρ]
  exact Finset.single_le_sum (fun j _ => I.probability_nonneg ρ j) (Finset.mem_univ i)

/-- The conditional quantum state, defined only for an outcome with positive probability. -/
def conditional (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : 0 < I.probability ρ i) : Density K :=
  Density.normalize (I.branch_positive i ρ.positive) (I.probability_eq_trace ρ i).symm
    (by exact_mod_cast hp.ne')

/-- Conditioning divides the branch operator by its probability. -/
lemma op_conditional (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : 0 < I.probability ρ i) :
    (I.conditional ρ i hp).op = (I.probability ρ i : ℂ)⁻¹ • I.branch i ρ.op := rfl

/-- Multiplying a conditional state by its probability recovers the unnormalized branch. -/
lemma probability_smul_conditional (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : 0 < I.probability ρ i) :
    (I.probability ρ i : ℂ) • (I.conditional ρ i hp).op = I.branch i ρ.op := by
  rw [op_conditional, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast hp.ne'

/-- A positive-probability branch proportional to a density state conditions to that state. -/
lemma conditional_eq_of_branch_eq_smul (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : 0 < I.probability ρ i) {σ : Density K} {a : ℂ} (h : I.branch i ρ.op = a • σ.op) :
    I.conditional ρ i hp = σ :=
  Density.normalize_eq_of_eq_smul _ _ _ h

/-- An outcome has zero probability exactly when its unnormalized output vanishes. -/
lemma probability_eq_zero_iff (I : Instrument H K ι) (ρ : Density H) (i : ι) :
    I.probability ρ i = 0 ↔ I.branch i ρ.op = 0 :=
  (I.branch_positive i ρ.positive).re_trace_eq_zero_iff

/-- An impossible outcome has the zero unnormalized output, not a chosen density state. -/
lemma branch_eq_zero_of_probability_eq_zero (I : Instrument H K ι) (ρ : Density H) (i : ι)
    (hp : I.probability ρ i = 0) : I.branch i ρ.op = 0 :=
  (I.probability_eq_zero_iff ρ i).mp hp

/-- The unread output is the sum of unnormalized branches. -/
lemma op_toChannel_map (I : Instrument H K ι) (ρ : Density H) :
    (I.toChannel.map ρ).op = ∑ i, I.branch i ρ.op := LinearMap.sum_apply _ _ _

/-- A normalized family of single Kraus operators, one per observed outcome. -/
def ofOperators (f : ι → H.state →ₗ[ℂ] K.state)
    (hf : ∑ i, (f i).adjoint ∘ₗ f i = 1) : Instrument H K ι where
  branch i := Superoperator.conjugate (f i)
  completelyPositive i := Superoperator.isCompletelyPositive_conjugate (f i)
  tracePreserving := Superoperator.isTracePreserving_kraus f hf

/-- Each observed outcome may itself contain several unobserved Kraus alternatives. -/
def ofKraus {κ : Type*} [Fintype κ] (f : ι → κ → H.state →ₗ[ℂ] K.state)
    (hf : ∑ i, ∑ j, (f i j).adjoint ∘ₗ f i j = 1) : Instrument H K ι where
  branch i := Superoperator.kraus (f i)
  completelyPositive i := Superoperator.isCompletelyPositive_kraus _
  tracePreserving A := by
    simp only [LinearMap.sum_apply, map_sum, Superoperator.trace_kraus]
    rw [← map_sum, ← Finset.sum_mul, hf, one_mul]

/-- Apply an outcome-dependent quantum channel after observing the instrument result. -/
def postprocess (I : Instrument H K ι) (Φ : ι → QuantumChannel K L) : Instrument H L ι where
  branch i := (Φ i).toSuperoperator ∘ₗ I.branch i
  completelyPositive i := (Φ i).completelyPositive.comp (I.completelyPositive i)
  tracePreserving A := by
    rw [LinearMap.sum_apply, Operator.trace, map_sum]
    change ∑ i, ((Φ i).toSuperoperator (I.branch i A)).trace = A.trace
    exact (Finset.sum_congr rfl fun i _ => (Φ i).tracePreserving (I.branch i A)).trans
      (I.sum_trace_branch A)

/-- The unnormalized output of a processed branch is the image under its selected channel. -/
lemma postprocess_branch_apply (I : Instrument H K ι) (Φ : ι → QuantumChannel K L)
    (i : ι) (A : Operator H) :
    (I.postprocess Φ).branch i A = (Φ i).toSuperoperator (I.branch i A) := rfl

/-- Outcome-dependent trace-preserving processing leaves the recorded probabilities unchanged. -/
lemma probability_postprocess (I : Instrument H K ι) (Φ : ι → QuantumChannel K L)
    (ρ : Density H) (i : ι) : (I.postprocess Φ).probability ρ i = I.probability ρ i :=
  congrArg Complex.re ((Φ i).tracePreserving (I.branch i ρ.op))

/-- Conditioning on a positive-probability outcome commutes with its selected channel. -/
lemma conditional_postprocess (I : Instrument H K ι) (Φ : ι → QuantumChannel K L)
    (ρ : Density H) (i : ι) (hp : 0 < I.probability ρ i) :
    (I.postprocess Φ).conditional ρ i (by simpa only [probability_postprocess] using hp) =
      (Φ i).map (I.conditional ρ i hp) := by
  apply Density.ext
  simp only [op_conditional, postprocess_branch_apply, probability_postprocess,
    QuantumChannel.op_map, map_smul]

end

end Instrument

end Qudit
