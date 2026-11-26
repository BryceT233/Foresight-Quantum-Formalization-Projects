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

public import FQFP.CQM.Qudit.Channel.RankOne
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

/-- The Lüders update of a projection-valued measure selects the corresponding block. -/
lemma luders_branch_ofOrthogonalResolution (P : CategoryTheory.OrthogonalResolution H ι)
    (i : ι) (A : Operator H) :
    (ofOrthogonalResolution P).luders.branch i A = (P.proj i).hom * A * (P.proj i).hom :=
  luders_branch_of_idempotent _ _
    ((isStarProjection_iff_hom _).mp (P.isStarProjection i)).isIdempotentElem.eq _

/-- An immediate repetition of a projective measurement gives the same outcome.
The unnormalized branch formula also covers impossible outcomes. -/
theorem luders_branch_repeat [DecidableEq ι] (P : CategoryTheory.OrthogonalResolution H ι)
    (i j : ι) (A : Operator H) :
    (ofOrthogonalResolution P).luders.branch j ((ofOrthogonalResolution P).luders.branch i A) =
      if i = j then (ofOrthogonalResolution P).luders.branch i A else 0 := by
  simp only [luders_branch_ofOrthogonalResolution]
  have h := congrArg Hom.hom (P.sandwich_sandwich i j (ofHom A))
  split_ifs at h ⊢ <;> exact h

/-- Forgetting the outcome of a projective measurement keeps the diagonal blocks. -/
theorem luders_toChannel_ofOrthogonalResolution (P : CategoryTheory.OrthogonalResolution H ι)
    (A : Operator H) : (ofOrthogonalResolution P).luders.toChannel.toSuperoperator A =
      (P.diagonalPart (ofHom A)).hom := by
  change (∑ i, (ofOrthogonalResolution P).luders.branch i) A = _
  simp only [LinearMap.sum_apply, luders_branch_ofOrthogonalResolution,
    CategoryTheory.OrthogonalResolution.diagonalPart, hom_sum]
  rfl

/-- The unread Lüders channel keeps an outer product exactly within a single outcome block. -/
theorem luders_toChannel_outer [DecidableEq ι] (P : CategoryTheory.OrthogonalResolution H ι)
    {i j : ι} {x y : H.state} (hx : (P.proj i).hom x = x) (hy : (P.proj j).hom y = y) :
    (ofOrthogonalResolution P).luders.toChannel.toSuperoperator (Operator.outer x y) =
      if i = j then Operator.outer x y else 0 := by
  have h := CQM.diagonalPart_outerHom P
    (u := ketArrow x) (v := ketArrow y) (i := i) (j := j)
    (by rw [ketArrow_comp, hx]) (by rw [ketArrow_comp, hy])
  have hxy : ofHom (Operator.outer x y) =
      CategoryTheory.MonoidalCategory.State.outerHom (ketArrow x) (ketArrow y) :=
    hom_ext (Operator.hom_outerHom_ketArrow x y).symm
  rw [luders_toChannel_ofOrthogonalResolution, hxy]
  simpa only [apply_ite, Operator.hom_outerHom_ketArrow, ← Operator.outer_eq_ket_comp_bra,
    hom_zero] using congrArg Hom.hom h

/-- Forgetting the outcome of a projective measurement defines an idempotent channel. -/
theorem luders_toChannel_idempotent (P : CategoryTheory.OrthogonalResolution H ι) :
    let Φ := (ofOrthogonalResolution P).luders.toChannel
    Φ.comp Φ = Φ := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  simp only [QuantumChannel.comp, LinearMap.comp_apply, luders_toChannel_ofOrthogonalResolution]
  exact congrArg Hom.hom (P.diagonalPart_idempotent (ofHom A))

/-- Basis measurement produces an unnormalized multiple of the observed basis projection. -/
lemma luders_ofBasis_branch (b : OrthonormalBasis ι ℂ H.state) (i : ι) (A : Operator H) :
    (ofBasis b).luders.branch i A = inner ℂ (b i) (A (b i)) • Operator.outer (b i) (b i) := by
  rw [← ofOrthogonalResolution_basisResolution, luders_branch_ofOrthogonalResolution,
    hom_basisResolution_proj]
  simpa only [Superoperator.conjugate_apply, ← Operator.outer_eq_ket_comp_bra,
    Operator.adjoint_outer, Module.End.mul_eq_comp, LinearMap.comp_assoc] using
    Superoperator.conjugate_ket_comp_bra_apply (b i) (b i) A

/-- Conditioning a basis measurement gives the observed pure basis state. -/
lemma conditional_luders_ofBasis (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H)
    (i : ι) (hp : 0 < (ofBasis b).luders.probability ρ i) :
    (ofBasis b).luders.conditional ρ i hp = Density.pure (UnitState.ofBasis b i) :=
  (ofBasis b).luders.conditional_eq_of_branch_eq_smul ρ i hp (luders_ofBasis_branch b i ρ.op)

end POVM

end

end Qudit
