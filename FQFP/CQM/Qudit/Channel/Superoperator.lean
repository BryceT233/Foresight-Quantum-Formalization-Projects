/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite
public import Mathlib.LinearAlgebra.Contraction

/-!
# Linear maps between qudit operator spaces

Superoperators act on operators, separately from the pure processes of `Qudit`.
Their tensor product is transported through Mathlib's canonical `homTensorHomEquiv`.
No basis or positivity assumption is needed for these algebraic constructions.

## Main definitions and results

* `Qudit.Superoperator`: complex-linear maps between qudit operator spaces.
* `Qudit.Superoperator.tensor`: the canonical tensor product of superoperators.
* `Qudit.Superoperator.conjugate`: conjugation by a linear map and its adjoint.
* `Qudit.Superoperator.tensor_comp`: tensor products respect sequential composition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

/-- A complex-linear map between operator spaces. -/
abbrev Superoperator (H K : Qudit) := Operator H →ₗ[ℂ] Operator K

namespace Operator

/-- The canonical tensor equivalence for finite-dimensional operator spaces. -/
def tensorEquiv (H K : Qudit) :
    Operator H ⊗[ℂ] Operator K ≃ₗ[ℂ] Operator (H ⊗ K) :=
  homTensorHomEquiv ℂ H.state K.state H.state K.state

/-- The canonical equivalence sends a simple tensor to the product operator. -/
lemma tensorEquiv_tmul {H K : Qudit} (A : Operator H) (B : Operator K) :
    tensorEquiv H K (A ⊗ₜ B) = tensor A B := rfl

/-- Linear maps on composite operators are determined on product operators. -/
lemma tensor_ext {H K : Qudit} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {f g : Operator (H ⊗ K) →ₗ[ℂ] V}
    (h : ∀ A B, f (tensor A B) = g (tensor A B)) : f = g := by
  apply (LinearMap.cancel_right (tensorEquiv H K).surjective).mp
  exact TensorProduct.ext' h

/-- Every operator on a composite space is a finite sum of product operators. -/
lemma tensor_induction_on {H K : Qudit} (A : Operator (H ⊗ K))
    {p : Operator (H ⊗ K) → Prop} (htensor : ∀ B C, p (tensor B C))
    (hadd : ∀ B C, p B → p C → p (B + C)) : p A := by
  obtain ⟨x, rfl⟩ := (tensorEquiv H K).surjective A
  induction x using TensorProduct.inductionOn with
  | tmul B C => exact htensor B C
  | add x y hx hy => rw [map_add]; exact hadd _ _ hx hy

end Operator

namespace Superoperator

variable {H K L M N P : Qudit}

/-- Tensor two superoperators using the canonical operator tensor equivalences. -/
def tensor (Φ : Superoperator H K) (Ψ : Superoperator L M) :
    Superoperator (H ⊗ L) (K ⊗ M) :=
  (Operator.tensorEquiv K M).toLinearMap ∘ₗ TensorProduct.map Φ Ψ ∘ₗ
    (Operator.tensorEquiv H L).symm.toLinearMap

/-- A product superoperator acts separately on product operators. -/
lemma tensor_apply (Φ : Superoperator H K) (Ψ : Superoperator L M)
    (A : Operator H) (B : Operator L) :
    tensor Φ Ψ (Operator.tensor A B) = Operator.tensor (Φ A) (Ψ B) := by
  change Operator.tensorEquiv K M
    (TensorProduct.map Φ Ψ ((Operator.tensorEquiv H L).symm
      (Operator.tensorEquiv H L (A ⊗ₜ B)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, Operator.tensorEquiv_tmul]

/-- Applying a superoperator on the retained factor commutes with discarding the other factor. -/
lemma partialTraceRight_tensor_id (Φ : Superoperator H K) (R : Qudit) :
    (Operator.partialTraceRight : Superoperator (K ⊗ R) K) ∘ₗ
        tensor Φ (LinearMap.id : Superoperator R R) =
      Φ ∘ₗ (Operator.partialTraceRight : Superoperator (H ⊗ R) H) := by
  apply Operator.tensor_ext
  intro A B
  simp only [LinearMap.comp_apply, tensor_apply, LinearMap.id_apply,
    Operator.partialTraceRight_tensor, map_smul]

/-- Tensoring identity superoperators gives the identity. -/
lemma tensor_id_id (H K : Qudit) :
    tensor (LinearMap.id : Superoperator H H) (LinearMap.id : Superoperator K K) =
      LinearMap.id := by
  apply Operator.tensor_ext
  intro A B
  rw [tensor_apply]
  rfl

/-- Tensor products commute with composition of superoperators. -/
lemma tensor_comp (Φ : Superoperator H K) (Ψ : Superoperator L M)
    (Φ' : Superoperator K N) (Ψ' : Superoperator M P) :
    tensor (Φ' ∘ₗ Φ) (Ψ' ∘ₗ Ψ) = tensor Φ' Ψ' ∘ₗ tensor Φ Ψ := by
  apply Operator.tensor_ext
  intro A B
  simp only [tensor_apply, LinearMap.comp_apply]

/-- Tensoring distributes over a finite sum in its first argument. -/
lemma tensor_sum_left {ι : Type*} (s : Finset ι) (Φ : ι → Superoperator H K)
    (Ψ : Superoperator L M) : tensor (∑ i ∈ s, Φ i) Ψ = ∑ i ∈ s, tensor (Φ i) Ψ := by
  apply Operator.tensor_ext
  intro A B
  simp only [tensor_apply, LinearMap.sum_apply]
  simp only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_sum, LinearMap.sum_apply]

/-- The adjoint of tensor insertion contracts against the inserted vector. -/
lemma adjoint_tensorInsertion_apply {C : Qudit} (v : C.state) (x : H.state) (y : C.state) :
    ((TensorProduct.mk ℂ H.state C.state).flip v).adjoint (x ⊗ₜ y) = inner ℂ v y • x := by
  apply ext_inner_left ℂ
  intro z
  rw [LinearMap.adjoint_inner_right]
  simp [TensorProduct.inner_tmul, inner_smul_right, mul_comm]

/-- Conjugation by an arbitrary linear process, without a normalization requirement. -/
def conjugate (f : H.state →ₗ[ℂ] K.state) : Superoperator H K where
  toFun A := f ∘ₗ A ∘ₗ f.adjoint
  map_add' A B := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' c A := by simp [LinearMap.comp_smul, LinearMap.smul_comp]

/-- Conjugation acts by the process and its adjoint. -/
lemma conjugate_apply (f : H.state →ₗ[ℂ] K.state) (A : Operator H) :
    conjugate f A = f ∘ₗ A ∘ₗ f.adjoint := rfl

/-- Conjugation by the identity is the identity superoperator. -/
lemma conjugate_id (H : Qudit) :
    conjugate (LinearMap.id : H.state →ₗ[ℂ] H.state) = LinearMap.id := by
  ext A x
  simp [conjugate]

/-- Conjugations respect sequential composition of the underlying linear processes. -/
lemma conjugate_comp (f : H.state →ₗ[ℂ] K.state) (g : K.state →ₗ[ℂ] L.state) :
    conjugate (g ∘ₗ f) = conjugate g ∘ₗ conjugate f := by
  ext A x
  simp only [conjugate_apply, LinearMap.comp_apply, LinearMap.adjoint_comp]

/-- Product processes induce product conjugations. -/
lemma conjugate_tensor (f : H.state →ₗ[ℂ] K.state) (g : L.state →ₗ[ℂ] M.state) :
    conjugate (TensorProduct.map f g) = tensor (conjugate f) (conjugate g) := by
  apply Operator.tensor_ext
  intro A B
  rw [tensor_apply]
  change TensorProduct.map f g ∘ₗ TensorProduct.map A B ∘ₗ
    (TensorProduct.map f g).adjoint =
      TensorProduct.map (f ∘ₗ A ∘ₗ f.adjoint) (g ∘ₗ B ∘ₗ g.adjoint)
  rw [TensorProduct.adjoint_map, TensorProduct.map_comp, TensorProduct.map_comp]

/-- Isometric change of coordinates on operator spaces. -/
def relabel (e : H.state ≃ₗᵢ[ℂ] K.state) : Superoperator H K :=
  e.toLinearEquiv.conj.toLinearMap

/-- Isometric relabeling agrees with conjugation by the isometry. -/
lemma relabel_eq_conjugate (e : H.state ≃ₗᵢ[ℂ] K.state) :
    relabel e = conjugate e.toLinearMap := by
  ext A x
  simp [relabel, conjugate, LinearEquiv.conj_apply_apply,
    LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

/-- Isometric relabeling preserves operator positivity. -/
lemma isPositive_relabel (e : H.state ≃ₗᵢ[ℂ] K.state) {A : Operator H}
    (hA : A.IsPositive) : (relabel e A).IsPositive := by
  rw [relabel_eq_conjugate]
  exact hA.conj_adjoint e.toLinearMap

/-- Swapping the factors of an operator swaps its product components. -/
lemma relabel_comm_tensor (A : Operator H) (B : Operator K) :
    relabel (TensorProduct.commIsometry ℂ H.state K.state) (Operator.tensor A B) =
      Operator.tensor B A := by
  apply TensorProduct.ext'
  intro x y
  change (TensorProduct.comm ℂ H.state K.state)
    (TensorProduct.map A B (TensorProduct.comm ℂ K.state H.state (x ⊗ₜ y))) = _
  rw [TensorProduct.comm_tmul, TensorProduct.map_tmul, TensorProduct.comm_tmul]
  rfl

/-- Reassociation of operator products agrees with Hilbert-space reassociation. -/
lemma relabel_assoc_tensor (A : Operator H) (B : Operator K) (C : Operator L) :
    relabel (TensorProduct.assocIsometry ℂ H.state K.state L.state)
      (Operator.tensor (Operator.tensor A B) C) =
      Operator.tensor A (Operator.tensor B C) := by
  apply TensorProduct.ext'
  intro x yz
  induction yz using TensorProduct.inductionOn with
  | tmul y z =>
    change (TensorProduct.assoc ℂ H.state K.state L.state)
      (TensorProduct.map (TensorProduct.map A B) C
        ((TensorProduct.assoc ℂ H.state K.state L.state).symm (x ⊗ₜ (y ⊗ₜ z)))) = _
    rw [TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, TensorProduct.assoc_tmul]
    rfl
  | add u v hu hv => simp_all [TensorProduct.tmul_add]

/-- Discarding a composite right factor agrees with two successive partial traces. -/
lemma partialTraceRight_relabel_assoc (H K L : Qudit) :
    (Operator.partialTraceRight : Superoperator (H ⊗ (K ⊗ L)) H) ∘ₗ
        relabel (TensorProduct.assocIsometry ℂ H.state K.state L.state) =
      (Operator.partialTraceRight : Superoperator (H ⊗ K) H) ∘ₗ
        (Operator.partialTraceRight : Superoperator ((H ⊗ K) ⊗ L) (H ⊗ K)) := by
  apply Operator.tensor_ext
  intro A C
  induction A using Operator.tensor_induction_on with
  | htensor A B =>
    simp only [LinearMap.comp_apply, relabel_assoc_tensor,
      Operator.partialTraceRight_tensor, Operator.trace_tensor, map_smul,
      smul_smul, mul_comm]
  | hadd A B hA hB =>
    simpa only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_add,
      LinearMap.add_apply] using congrArg₂ (· + ·) hA hB

/-- Discarding the first factor after reassociation retains the other two factors. -/
lemma partialTraceLeft_relabel_assoc (H K L : Qudit) :
    (Operator.partialTraceLeft : Superoperator (H ⊗ (K ⊗ L)) (K ⊗ L)) ∘ₗ
        relabel (TensorProduct.assocIsometry ℂ H.state K.state L.state) =
      tensor (Operator.partialTraceLeft : Superoperator (H ⊗ K) K)
        (LinearMap.id : Superoperator L L) := by
  apply Operator.tensor_ext
  intro A C
  induction A using Operator.tensor_induction_on with
  | htensor A B =>
    simp only [LinearMap.comp_apply, relabel_assoc_tensor, tensor_apply,
      Operator.partialTraceLeft_tensor, LinearMap.id_apply]
    exact (TensorProduct.map_smul_left _ _ _).symm
  | hadd A B hA hB =>
    simpa only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_add,
      LinearMap.add_apply] using congrArg₂ (· + ·) hA hB

/-- Inverse reassociation of operator products. -/
lemma relabel_assoc_symm_tensor (A : Operator H) (B : Operator K) (C : Operator L) :
    relabel (TensorProduct.assocIsometry ℂ H.state K.state L.state).symm
      (Operator.tensor A (Operator.tensor B C)) =
      Operator.tensor (Operator.tensor A B) C := by
  apply TensorProduct.ext'
  intro xy z
  induction xy using TensorProduct.inductionOn with
  | tmul x y =>
    change (TensorProduct.assoc ℂ H.state K.state L.state).symm
      (TensorProduct.map A (TensorProduct.map B C)
        ((TensorProduct.assoc ℂ H.state K.state L.state) ((x ⊗ₜ y) ⊗ₜ z))) = _
    rw [TensorProduct.assoc_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, TensorProduct.assoc_symm_tmul]
    rfl
  | add u v hu hv => simp_all [TensorProduct.add_tmul]

/-- Tensoring identities on two ancillary factors agrees with reassociation. -/
lemma tensor_id_assoc (Φ : Superoperator H K) (L M : Qudit) :
    tensor (tensor Φ (LinearMap.id : Superoperator L L))
        (LinearMap.id : Superoperator M M) =
      relabel (TensorProduct.assocIsometry ℂ K.state L.state M.state).symm ∘ₗ
        tensor Φ (LinearMap.id : Superoperator (L ⊗ M) (L ⊗ M)) ∘ₗ
        relabel (TensorProduct.assocIsometry ℂ H.state L.state M.state) := by
  apply Operator.tensor_ext
  intro A C
  induction A using Operator.tensor_induction_on with
  | htensor A B =>
    simp only [tensor_apply, LinearMap.id_apply, LinearMap.comp_apply,
      relabel_assoc_tensor, relabel_assoc_symm_tensor]
  | hadd A B hA hB =>
    simpa only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_add,
      LinearMap.add_apply] using congrArg₂ (· + ·) hA hB

/-- Tensoring on the left is tensoring on the right conjugated by swaps. -/
lemma id_tensor_eq_comm (Φ : Superoperator H K) (L : Qudit) :
    tensor (LinearMap.id : Superoperator L L) Φ =
      relabel (TensorProduct.commIsometry ℂ K.state L.state) ∘ₗ
        tensor Φ (LinearMap.id : Superoperator L L) ∘ₗ
        relabel (TensorProduct.commIsometry ℂ L.state H.state) := by
  apply Operator.tensor_ext
  intro A B
  simp only [tensor_apply, LinearMap.id_apply, LinearMap.comp_apply, relabel_comm_tensor]

end Superoperator

end

end Qudit
