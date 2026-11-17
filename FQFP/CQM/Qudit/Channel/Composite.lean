/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Basic

/-!
# Composite channel identities

Parallel channels commute with sequential composition. Discarding one output of a product
channel leaves precisely the channel on the retained input, including for entangled inputs.
Swapping the outputs exchanges the two partial traces.

## Main results

* `Qudit.QuantumChannel.tensor_comp`: parallel composition respects sequential composition.
* `Qudit.QuantumChannel.partialTraceRight_map_tensor`: the left output marginal depends on the left
  input.
* `Qudit.QuantumChannel.partialTraceLeft_map_tensor`: the corresponding right-marginal identity.
* `Qudit.QuantumChannel.partialTraceRight_comp_swap`: swapping exchanges the subsystem discarded.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K L M N P : Qudit}

/-- Sequential isometries induce sequential channels. -/
lemma ofIsometry_comp (f : H ⟶ K) (g : K ⟶ L) [IsIsometry f] [IsIsometry g] :
    ofIsometry (f ≫ g) = (ofIsometry g).comp (ofIsometry f) :=
  QuantumChannel.ext (Superoperator.conjugate_comp f.hom g.hom)

/-- Parallel isometries induce the product channel. -/
lemma ofIsometry_tensor (f : H ⟶ K) (g : L ⟶ M) [IsIsometry f] [IsIsometry g] :
    ofIsometry (f ⊗ₘ g) = (ofIsometry f).tensor (ofIsometry g) := by
  apply QuantumChannel.ext
  change Superoperator.conjugate (f ⊗ₘ g).hom = _
  rw [hom_tensorHom, Superoperator.conjugate_tensor]
  rfl

/-- The identity isometry induces the identity channel. -/
lemma ofIsometry_id (H : Qudit) : ofIsometry (𝟙 H) = id H :=
  QuantumChannel.ext (Superoperator.conjugate_id H)

/-- Parallel composition respects sequential composition. -/
lemma tensor_comp (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (Φ' : QuantumChannel K N) (Ψ' : QuantumChannel M P) :
    (Φ'.comp Φ).tensor (Ψ'.comp Ψ) = (Φ'.tensor Ψ').comp (Φ.tensor Ψ) :=
  QuantumChannel.ext (Superoperator.tensor_comp _ _ _ _)

/-- The product of identity channels is the identity channel. -/
lemma tensor_id_id (H K : Qudit) : (id H).tensor (id K) = id (H ⊗ K) :=
  QuantumChannel.ext (Superoperator.tensor_id_id H K)

/-- Discarding the second output commutes with a product of trace-preserving channels. -/
lemma partialTraceRight_comp_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) :
    (partialTraceRight K M).comp (Φ.tensor Ψ) = Φ.comp (partialTraceRight H L) := by
  apply QuantumChannel.ext
  apply Operator.tensor_ext
  intro A B
  change Operator.partialTraceRight
    (Superoperator.tensor Φ.toSuperoperator Ψ.toSuperoperator (Operator.tensor A B)) =
      Φ.toSuperoperator (Operator.partialTraceRight (Operator.tensor A B))
  rw [Superoperator.tensor_apply, Operator.partialTraceRight_tensor,
    Operator.partialTraceRight_tensor, Ψ.tracePreserving, map_smul]

/-- Discarding the first output commutes with a product of trace-preserving channels. -/
lemma partialTraceLeft_comp_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) :
    (partialTraceLeft K M).comp (Φ.tensor Ψ) = Ψ.comp (partialTraceLeft H L) := by
  apply QuantumChannel.ext
  apply Operator.tensor_ext
  intro A B
  change Operator.partialTraceLeft
    (Superoperator.tensor Φ.toSuperoperator Ψ.toSuperoperator (Operator.tensor A B)) =
      Ψ.toSuperoperator (Operator.partialTraceLeft (Operator.tensor A B))
  rw [Superoperator.tensor_apply, Operator.partialTraceLeft_tensor,
    Operator.partialTraceLeft_tensor, Φ.tracePreserving, map_smul]

/-- The left marginal of a product-channel output depends only on the left input marginal. -/
lemma partialTraceRight_map_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (ρ : Density (H ⊗ L)) :
    ((Φ.tensor Ψ).map ρ).partialTraceRight = Φ.map ρ.partialTraceRight := by
  have h := congrArg (fun Γ => Γ.map ρ) (partialTraceRight_comp_tensor Φ Ψ)
  simpa only [map_comp, map_partialTraceRight] using h

/-- The right marginal of a product-channel output depends only on the right input marginal. -/
lemma partialTraceLeft_map_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M)
    (ρ : Density (H ⊗ L)) :
    ((Φ.tensor Ψ).map ρ).partialTraceLeft = Ψ.map ρ.partialTraceLeft := by
  have h := congrArg (fun Γ => Γ.map ρ) (partialTraceLeft_comp_tensor Φ Ψ)
  simpa only [map_comp, map_partialTraceLeft] using h

/-- Reassociate `H ⊗ (K ⊗ L)` and discard `L`, equivalently discard it inside `K ⊗ L`. -/
lemma partialTraceRight_map_associator_inv (ρ : Density (H ⊗ (K ⊗ L))) :
    (ρ.map (α_ H K L).inv).partialTraceRight =
      ((id H).tensor (partialTraceRight K L)).map ρ := by
  let e := (TensorProduct.assocIsometry ℂ H.state K.state L.state).symm
  have h : (Operator.partialTraceRight : Superoperator ((H ⊗ K) ⊗ L) (H ⊗ K)) ∘ₗ
      Superoperator.relabel e = Superoperator.tensor (LinearMap.id : Superoperator H H)
        (Operator.partialTraceRight : Superoperator (K ⊗ L) K) := by
    apply Operator.tensor_ext
    intro A D
    induction D using Operator.tensor_induction_on with
    | htensor B C =>
      simp only [e, LinearMap.comp_apply, Superoperator.relabel_assoc_symm_tensor,
        Superoperator.tensor_apply, LinearMap.id_apply, Operator.partialTraceRight_tensor]
      exact (TensorProduct.map_smul_right _ _ _).symm
    | hadd B C hB hC =>
      simpa only [Operator.tensor, TensorProduct.map_add_right, map_add] using
        congrArg₂ (· + ·) hB hC
  apply Density.ext
  rw [Superoperator.relabel_eq_conjugate] at h
  exact DFunLike.congr_fun h ρ.op

/-- Swapping before discarding the right output retains the original right output. -/
lemma partialTraceRight_comp_swap (H K : Qudit) :
    (partialTraceRight K H).comp (ofIsometry (β_ H K).hom) = partialTraceLeft H K := by
  apply QuantumChannel.ext
  change (Operator.partialTraceRight : Superoperator (K ⊗ H) K) ∘ₗ
    Superoperator.conjugate (H := H ⊗ K) (K := K ⊗ H)
      (TensorProduct.commIsometry ℂ H.state K.state).toLinearMap = Operator.partialTraceLeft
  rw [← Superoperator.relabel_eq_conjugate (H := H ⊗ K) (K := K ⊗ H)]
  apply Operator.tensor_ext
  intro A B
  simp only [LinearMap.comp_apply, Superoperator.relabel_comm_tensor,
    Operator.partialTraceRight_tensor, Operator.partialTraceLeft_tensor]

/-- Swapping before discarding the left output retains the original left output. -/
lemma partialTraceLeft_comp_swap (H K : Qudit) :
    (partialTraceLeft K H).comp (ofIsometry (β_ H K).hom) = partialTraceRight H K := by
  apply QuantumChannel.ext
  change (Operator.partialTraceLeft : Superoperator (K ⊗ H) H) ∘ₗ
    Superoperator.conjugate (H := H ⊗ K) (K := K ⊗ H)
      (TensorProduct.commIsometry ℂ H.state K.state).toLinearMap = Operator.partialTraceRight
  rw [← Superoperator.relabel_eq_conjugate (H := H ⊗ K) (K := K ⊗ H)]
  apply Operator.tensor_ext
  intro A B
  simp only [LinearMap.comp_apply, Superoperator.relabel_comm_tensor,
    Operator.partialTraceRight_tensor, Operator.partialTraceLeft_tensor]

end

end Qudit.QuantumChannel
