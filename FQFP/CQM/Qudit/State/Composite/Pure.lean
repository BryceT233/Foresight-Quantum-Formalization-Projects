/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/

/-
Physlib reference for pure bipartite states with a pure marginal.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Mixed/MState.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Pure

/-!
# Pure bipartite states and pure marginals

A bipartite unit vector is a product vector exactly when either reduced density operator
is pure. The tensor factors may have different dimensions. No Schmidt basis is chosen:
a pure marginal forces the vector into the range of its local rank-one projection.

## Main results

* `Qudit.UnitState.exists_eq_tensor_of_partialTraceRight_eq_pure`: factorization from a pure
  marginal.
* `Qudit.UnitState.isProduct_iff_isPure_partialTraceRight`: products are exactly pure left
  marginals.
* `Qudit.UnitState.isProduct_iff_isPure_partialTraceLeft`: the corresponding right-marginal
  criterion.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

variable {H K : Qudit}

namespace UnitState

/-- A specified pure left marginal determines the left factor of a bipartite unit vector. -/
lemma exists_eq_tensor_of_partialTraceRight_eq_pure (ψ : UnitState (H ⊗ K))
    (v : UnitState H) (h : (Density.pure ψ).partialTraceRight = Density.pure v) :
    ∃ w : UnitState K, ψ = v.tensor w := by
  let f : K.state →ₗ[ℂ] (H ⊗ K).state := TensorProduct.mk ℂ H.state K.state v.val
  have hf (x y : K.state) : inner ℂ (f x) (f y) = inner ℂ x y := by
    change inner ℂ (v.val ⊗ₜ[ℂ] x) (v.val ⊗ₜ[ℂ] y) = _
    rw [TensorProduct.inner_tmul, v.inner_self, one_mul]
  have hA : Operator.tensor (Density.pure v).op 1 = f ∘ₗ f.adjoint := by
    apply TensorProduct.ext'
    intro x y
    have hc : f.adjoint (x ⊗ₜ[ℂ] y) = inner ℂ v.val x • y := by
      apply ext_inner_left ℂ
      intro z
      rw [LinearMap.adjoint_inner_right]
      change inner ℂ (v.val ⊗ₜ[ℂ] z) (x ⊗ₜ[ℂ] y) = _
      rw [TensorProduct.inner_tmul, inner_smul_right, mul_comm]
    simp only [LinearMap.comp_apply, hc]
    exact TensorProduct.smul_tmul _ _ _
  have he : inner ℂ ψ.val (f (f.adjoint ψ.val)) = 1 := by
    have he := (Density.pure ψ).expectationComplex_partialTraceRight (Density.pure v).op
    rw [h, Density.expectationComplex_pure, Density.pure_apply, v.inner_self,
      one_smul, v.inner_self, Density.expectationComplex_pure, hA] at he
    exact he.symm
  have hnorm : inner ℂ (f (f.adjoint ψ.val)) (f (f.adjoint ψ.val)) = 1 := by
    rw [hf, ← LinearMap.adjoint_inner_right, LinearMap.adjoint_adjoint]
    exact he
  have hψ : ψ.val = f (f.adjoint ψ.val) := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_sub_left, inner_sub_right, inner_sub_right, ψ.inner_self, he, hnorm,
      ← inner_conj_symm (f (f.adjoint ψ.val)) ψ.val, he]
    simp
  have hw : state.Normalized (f.adjoint ψ.val) := by
    change inner ℂ (f.adjoint ψ.val) (f.adjoint ψ.val) = 1
    rw [← hf]
    exact hnorm
  exact ⟨⟨f.adjoint ψ.val, hw⟩, Subtype.ext hψ⟩

/-- A bipartite unit vector is a product exactly when its left marginal is pure. -/
lemma isProduct_iff_isPure_partialTraceRight (ψ : UnitState (H ⊗ K)) :
    ψ.IsProduct ↔ (Density.pure ψ).partialTraceRight.IsPure := by
  constructor
  · rintro ⟨v, w, rfl⟩
    rw [← Density.tensor_pure, Density.partialTraceRight_tensor]
    exact Density.isPure_pure v
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := exists_eq_tensor_of_partialTraceRight_eq_pure ψ v hv
    exact ⟨v, w, hw⟩

end UnitState

namespace Density

/-- Swapping a pure bipartite vector exchanges the retained subsystem of its marginal. -/
lemma partialTraceRight_pure_swap (ψ : UnitState (H ⊗ K)) :
    (pure ψ.swap).partialTraceRight = (pure ψ).partialTraceLeft := by
  apply Density.ext
  ext y
  apply ext_inner_left ℂ
  intro x
  let b := stdOrthonormalBasis ℂ H.state
  rw [op_partialTraceRight, op_partialTraceLeft,
    Operator.inner_partialTraceRight b, Operator.inner_partialTraceLeft b]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pure_apply, inner_smul_right]
  have hx : inner ℂ (x ⊗ₜ[ℂ] b i) ψ.swap.val = inner ℂ (b i ⊗ₜ[ℂ] x) ψ.val := by
    exact TensorProduct.inner_comm_comm (b i ⊗ₜ[ℂ] x) ψ.val
  have hy : inner ℂ ψ.swap.val (y ⊗ₜ[ℂ] b i) = inner ℂ ψ.val (b i ⊗ₜ[ℂ] y) := by
    exact TensorProduct.inner_comm_comm ψ.val (b i ⊗ₜ[ℂ] y)
  rw [hx, hy]

end Density

namespace UnitState

/-- A specified pure right marginal determines the right factor of a bipartite unit vector. -/
lemma exists_eq_tensor_of_partialTraceLeft_eq_pure (ψ : UnitState (H ⊗ K))
    (w : UnitState K) (h : (Density.pure ψ).partialTraceLeft = Density.pure w) :
    ∃ v : UnitState H, ψ = v.tensor w := by
  have hs : (Density.pure ψ.swap).partialTraceRight = Density.pure w := by
    rw [Density.partialTraceRight_pure_swap, h]
  obtain ⟨v, hv⟩ := exists_eq_tensor_of_partialTraceRight_eq_pure ψ.swap w hs
  exact ⟨v, by simpa only [swap_swap, swap_tensor] using congrArg UnitState.swap hv⟩

/-- A bipartite unit vector is a product exactly when its right marginal is pure. -/
lemma isProduct_iff_isPure_partialTraceLeft (ψ : UnitState (H ⊗ K)) :
    ψ.IsProduct ↔ (Density.pure ψ).partialTraceLeft.IsPure := by
  rw [← isProduct_swap_iff, isProduct_iff_isPure_partialTraceRight,
    Density.partialTraceRight_pure_swap]

end UnitState

end

end Qudit
