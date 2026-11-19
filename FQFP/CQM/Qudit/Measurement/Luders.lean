/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for measurement with the positive square roots of the effects.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Measurements/POVM.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.Instrument
public import FQFP.CQM.Qudit.Measurement.POVM
public import FQFP.CQM.Qudit.State.Spectral.OperatorSqrt

/-!
# The Lüders instrument of a POVM

The positive square roots of the effects give one particular instrument realizing a POVM.
The construction retains the quantum output, with branches `sqrt(Eᵢ) A sqrt(Eᵢ)`.
It does not assert that outcome probabilities uniquely determine post-measurement states.

## Main definitions and results

* `Qudit.POVM.luders`: the instrument with positive square roots as its Kraus operators.
* `Qudit.POVM.luders_branch_apply`: the unnormalized square-root update.
* `Qudit.POVM.probability_luders`: the instrument recovers the original Born probabilities.
* `Qudit.POVM.conditional_luders_ofBasis`: basis measurement prepares the observed basis state.
-/

@[expose] public section

open scoped ComplexOrder BigOperators

namespace Qudit

noncomputable section

namespace POVM

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- The Lüders instrument: one positive-square-root Kraus operator per outcome. -/
def luders (M : POVM H ι) : Instrument H H ι :=
  Instrument.ofOperators (fun i => (M.op i).sqrt) (by
    simp only [Operator.adjoint_sqrt, ← Module.End.mul_eq_comp,
      fun i => Operator.sqrt_mul_sqrt (M.op i) (M.positive i), M.sum_op])

/-- The unnormalized Lüders update. -/
lemma luders_branch_apply (M : POVM H ι) (i : ι) (A : Operator H) :
    M.luders.branch i A = (M.op i).sqrt * A * (M.op i).sqrt := by
  change (M.op i).sqrt ∘ₗ A ∘ₗ (M.op i).sqrt.adjoint = _
  rw [Operator.adjoint_sqrt]
  rfl

/-- Lüders branch traces recover the original POVM trace pairing. -/
lemma trace_luders_branch (M : POVM H ι) (i : ι) (A : Operator H) :
    (M.luders.branch i A).trace = (M.op i * A).trace := by
  rw [luders_branch_apply, Operator.trace, LinearMap.trace_mul_comm,
    ← mul_assoc, Operator.sqrt_mul_sqrt _ (M.positive i)]

/-- The Lüders instrument realizes exactly the original Born probabilities. -/
lemma probability_luders (M : POVM H ι) (ρ : Density H) (i : ι) :
    M.luders.probability ρ i = M.probability ρ i := by
  unfold Instrument.probability
  rw [trace_luders_branch]
  rfl

/-- For a projective effect, the Lüders update uses the projection itself. -/
lemma luders_branch_of_idempotent (M : POVM H ι) (i : ι)
    (hi : M.op i * M.op i = M.op i) (A : Operator H) :
    M.luders.branch i A = M.op i * A * M.op i := by
  rw [luders_branch_apply, Operator.sqrt_eq_self _ (M.positive i) hi]

/-- Basis measurement produces an unnormalized multiple of the observed basis projection. -/
lemma luders_ofBasis_branch (b : OrthonormalBasis ι ℂ H.state) (i : ι) (A : Operator H) :
    (ofBasis b).luders.branch i A = inner ℂ (b i) (A (b i)) • Operator.outer (b i) (b i) := by
  have hs : (ofBasis b).op i * (ofBasis b).op i = (ofBasis b).op i := by
    ext x
    simp [ofBasis]
  rw [luders_branch_of_idempotent _ _ hs]
  ext x
  simp [ofBasis, smul_smul, mul_comm]

/-- Conditioning a basis measurement gives the observed pure basis state. -/
lemma conditional_luders_ofBasis (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H)
    (i : ι) (hp : 0 < (ofBasis b).luders.probability ρ i) :
    (ofBasis b).luders.conditional ρ i hp = Density.pure (UnitState.ofBasis b i) := by
  have ht : ((ofBasis b).luders.probability ρ i : ℂ) = inner ℂ (b i) (ρ.op (b i)) := by
    rw [Instrument.probability_eq_trace, luders_ofBasis_branch, Operator.trace, map_smul]
    simp [Operator.trace_outer, smul_eq_mul]
  apply Density.ext
  rw [Instrument.op_conditional, luders_ofBasis_branch, ← ht, smul_smul, inv_mul_cancel₀]
  · exact one_smul _ _
  · exact_mod_cast hp.ne'

end POVM

end

end Qudit
