/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for compatibility of tensor products with composition.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/MatrixMap.lean
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Category.Postprocessing
public import FQFP.CQM.Qudit.Channel.Process.Causal

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

namespace Qudit.CausalQudit

open SemiCartesianMonoidalCategory

/-- The first marginal in the deterministic process category is the right partial trace. -/
lemma fst_eq_partialTraceRight (X Y : CausalQudit) :
    fst X Y = QuantumChannel.partialTraceRight X.toQudit Y.toQudit :=
  QuantumChannel.ext (CPQudit.tensor_discard ⟨X.toQudit⟩ ⟨Y.toQudit⟩)

/-- The second marginal is the left partial trace. -/
lemma snd_eq_partialTraceLeft (X Y : CausalQudit) :
    snd X Y = QuantumChannel.partialTraceLeft X.toQudit Y.toQudit := by
  rw [← braiding_hom_fst, fst_eq_partialTraceRight]
  apply QuantumChannel.ext
  change (Operator.partialTraceRight : Superoperator (Y.toQudit ⊗ X.toQudit) Y.toQudit) ∘ₗ
    Superoperator.conjugate (H := X.toQudit ⊗ Y.toQudit) (K := Y.toQudit ⊗ X.toQudit)
      (TensorProduct.commIsometry ℂ X.toQudit.state Y.toQudit.state).toLinearMap =
        Operator.partialTraceLeft
  rw [← Superoperator.relabel_eq_conjugate (H := X.toQudit ⊗ Y.toQudit)
    (K := Y.toQudit ⊗ X.toQudit)]
  apply Operator.tensor_ext
  intro A B
  simp only [LinearMap.comp_apply, Superoperator.relabel_comm_tensor,
    Operator.partialTraceRight_tensor, Operator.partialTraceLeft_tensor]

end Qudit.CausalQudit

namespace Qudit.QuantumChannel

noncomputable section

open CausalQudit SemiCartesianMonoidalCategory

variable {H K L M N P : Qudit}

/-- The two categorical marginals of a joint channel are its partial traces. -/
lemma hasMarginals_iff {j : QuantumChannel H (K ⊗ L)} {f : QuantumChannel H K}
    {g : QuantumChannel H L} :
    CQM.HasMarginals j.asHom f.asHom g.asHom ↔
      (partialTraceRight K L).comp j = f ∧ (partialTraceLeft K L).comp j = g := by
  simp only [CQM.HasMarginals, fst_eq_partialTraceRight, snd_eq_partialTraceLeft]
  rfl

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
  (tensorHom_comp_tensorHom Φ.asHom Ψ.asHom Φ'.asHom Ψ'.asHom).symm

/-- The product of identity channels is the identity channel. -/
lemma tensor_id_id (H K : Qudit) : (id H).tensor (id K) = id (H ⊗ K) :=
  id_tensorHom_id (C := CausalQudit) ⟨H⟩ ⟨K⟩

/-- Discarding the second output commutes with a product of trace-preserving channels. -/
lemma partialTraceRight_comp_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) :
    (partialTraceRight K M).comp (Φ.tensor Ψ) = Φ.comp (partialTraceRight H L) := by
  simpa only [fst_eq_partialTraceRight] using!
    tensorHom_fst Φ.asHom Ψ.asHom

/-- Discarding the first output commutes with a product of trace-preserving channels. -/
lemma partialTraceLeft_comp_tensor (Φ : QuantumChannel H K) (Ψ : QuantumChannel L M) :
    (partialTraceLeft K M).comp (Φ.tensor Ψ) = Ψ.comp (partialTraceLeft H L) := by
  simpa only [snd_eq_partialTraceLeft] using!
    tensorHom_snd Φ.asHom Ψ.asHom

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

/-- Discarding the last two outputs after reassociation equals discarding them successively. -/
lemma partialTraceRight_comp_associator (H K L : Qudit) :
    (partialTraceRight H (K ⊗ L)).comp (ofIsometry (α_ H K L).hom) =
      (partialTraceRight H K).comp (partialTraceRight (H ⊗ K) L) := by
  simpa only [fst_eq_partialTraceRight] using!
    associator_hom_fst (C := CausalQudit) ⟨H⟩ ⟨K⟩ ⟨L⟩

/-- Discarding the first output after reassociation leaves the last output untouched. -/
lemma partialTraceLeft_comp_associator (H K L : Qudit) :
    (partialTraceLeft H (K ⊗ L)).comp (ofIsometry (α_ H K L).hom) =
      (partialTraceLeft H K).tensor (id L) := by
  simpa only [snd_eq_partialTraceLeft] using!
    associator_hom_snd (C := CausalQudit) ⟨H⟩ ⟨K⟩ ⟨L⟩

/-- Reassociate `H ⊗ (K ⊗ L)` and discard `L`, equivalently discard it inside `K ⊗ L`. -/
lemma partialTraceRight_map_associator_inv (ρ : Density (H ⊗ (K ⊗ L))) :
    (ρ.map (α_ H K L).inv).partialTraceRight =
      ((id H).tensor (partialTraceRight K L)).map ρ := by
  have h := associator_inv_fst (C := CausalQudit) ⟨H⟩ ⟨K⟩ ⟨L⟩
  rw [fst_eq_partialTraceRight, fst_eq_partialTraceRight] at h
  change (partialTraceRight (H ⊗ K) L).comp (ofIsometry (α_ H K L).hom†) = _ at h
  have he := congrArg (fun f : QuantumChannel _ _ => f.toSuperoperator ρ.op) h
  change Operator.partialTraceRight (Superoperator.conjugate (α_ H K L).hom†.hom ρ.op) = _ at he
  rw [IsUnitary.dagger_hom_eq_inv] at he
  exact Density.ext he

/-- Swapping before discarding the right output retains the original right output. -/
lemma partialTraceRight_comp_swap (H K : Qudit) :
    (partialTraceRight K H).comp (ofIsometry (β_ H K).hom) = partialTraceLeft H K := by
  simpa only [fst_eq_partialTraceRight, snd_eq_partialTraceLeft] using!
    braiding_hom_fst (C := CausalQudit) ⟨H⟩ ⟨K⟩

/-- Swapping before discarding the left output retains the original left output. -/
lemma partialTraceLeft_comp_swap (H K : Qudit) :
    (partialTraceLeft K H).comp (ofIsometry (β_ H K).hom) = partialTraceRight H K := by
  simpa only [fst_eq_partialTraceRight, snd_eq_partialTraceLeft] using!
    braiding_hom_snd (C := CausalQudit) ⟨H⟩ ⟨K⟩

end

end Qudit.QuantumChannel
