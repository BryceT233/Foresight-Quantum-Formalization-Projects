/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Dual
public import FQFP.CQM.Qudit.Rigid

/-!
# Basis-dependent compact pairings of CP processes

The CP image of the existing Hilbert-space cup and cap satisfies both snake identities
and dagger compatibility. The basis is explicit: these are self-dual pairings, not a
new construction of the canonical conjugate Hilbert space.

## Main definitions and results

* `Qudit.CPQudit.exactPairingOfOrthonormalBasis`: the CP self-dual pairing of a chosen basis.
* `Qudit.CPQudit.dagger_basisCup`: the cap is the dagger of the cup.
* `Qudit.CPQudit.discard_dual`: discarding is compatible with the chosen self-dual pairing.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit.CPQudit

noncomputable section

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- Transport the chosen orthonormal self-dual pairing to CP semantics. -/
@[instance_reducible]
def exactPairingOfOrthonormalBasis (b : OrthonormalBasis ι ℂ H.state) :
    ExactPairing (⟨H⟩ : CPQudit) ⟨H⟩ where
  coevaluation' := pure.map (basisCoevaluation b)
  evaluation' := pure.map (basisEvaluation b)
  coevaluation_evaluation' := by
    have e := congrArg pure.map (Qudit.coevaluation_evaluation b)
    simp only [← id_tensorHom, ← tensorHom_id, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1 <;> rfl
  evaluation_coevaluation' := by
    have e := congrArg pure.map (Qudit.evaluation_coevaluation b)
    simp only [← id_tensorHom, ← tensorHom_id, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1 <;> rfl

/-- The CP cap is the dagger of its cup. -/
lemma dagger_basisCup (b : OrthonormalBasis ι ℂ H.state) :
    (pure.map (basisCoevaluation b))† = pure.map (basisEvaluation b) := by
  rw [dagger_pure, dagger_basisCoevaluation]

/-- The compact cap evaluates an operator tensored with the identity by its trace. -/
lemma cap_tensor_one (b : OrthonormalBasis ι ℂ H.state) (A : Operator H) :
    (pure.map (basisEvaluation b)).toSuperoperator (Operator.tensor A 1) = A.trace • 1 := by
  apply LinearMap.ext_ring
  change (basisEvaluation b).hom
    (Operator.tensor A 1 ((basisEvaluation b).hom.adjoint (1 : ℂ))) = A.trace * 1
  rw [← Qudit.hom_dagger, ← dagger_basisCoevaluation b, involutive_dagger, dagger_basisCoevaluation]
  change basisEvaluation b (Operator.tensor A 1 (basisCoevaluation b (1 : ℂ))) = _
  rw [basisCoevaluation_apply, one_smul, map_sum, map_sum, mul_one]
  simp only [Operator.tensor_apply, Module.End.one_apply, basisEvaluation_apply,
    basisForm_apply_basis]
  exact (LinearMap.trace_eq_sum_inner A b).symm

/-- Discarding respects the chosen dual: bending the adjoint of discarding through
the compact cap recovers discarding. This is the dual compatibility in (7.19). -/
lemma discard_dual (b : OrthonormalBasis ι ℂ H.state) :
    (ρ_ (⟨H⟩ : CPQudit)).inv ≫
      (𝟙 (⟨H⟩ : CPQudit) ⊗ₘ (discard ⟨H⟩)†) ≫ pure.map (basisEvaluation b) = discard ⟨H⟩ := by
  apply (cancel_epi (ρ_ (⟨H⟩ : CPQudit)).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply CPMap.ext
  apply Operator.tensor_ext
  intro A B
  change (pure.map (basisEvaluation b)).toSuperoperator
    (Superoperator.tensor LinearMap.id (discard ⟨H⟩)†.toSuperoperator (Operator.tensor A B)) =
    Superoperator.discard H
      (Superoperator.conjugate (ρ_ H).hom.hom (Operator.tensor A B))
  rw [Superoperator.tensor_apply, LinearMap.id_apply, dagger_discard_apply,
    Superoperator.conjugate_rightUnitor_tensor]
  have ht : Operator.tensor A (B.trace • (1 : Operator H)) =
      B.trace • Operator.tensor A 1 := by
    simp only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_smul]
  change Superoperator.conjugate (H := H ⊗ H) (K := of ℂ) (basisEvaluation b).hom
    (Operator.tensor (H := H) (K := H) A (B.trace • 1)) =
      Superoperator.discard H (B.trace • A)
  rw [ht, map_smul, map_smul, Superoperator.discard_apply]
  exact congrArg (B.trace • ·) (cap_tensor_one b A)

end

end Qudit.CPQudit
