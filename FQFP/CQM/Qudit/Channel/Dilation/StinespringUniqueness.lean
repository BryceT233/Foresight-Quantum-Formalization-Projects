/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.InnerProductSpace.Gram
public import FQFP.CQM.Qudit.Channel.Dilation.Complementary

/-!
# Uniqueness of finite-dimensional Stinespring dilations

A common channel fixes the Gram matrix of the environment vectors obtained by contracting
each isometry against output vectors. When the environment dimensions are ordered, an
isometry between the environments therefore intertwines the original dilations.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit.QuantumChannel.Dilation

noncomputable section

variable {H K E F : Qudit} {Φ : QuantumChannel H K}

private def slice (d : Φ.Dilation E) (p : H.state × K.state) : E.state :=
  (TensorProduct.mk ℂ K.state E.state p.2).adjoint (d.toHom.hom p.1)

private lemma inner_slice (d : Φ.Dilation E) (p q : H.state × K.state) :
    inner ℂ (d.slice p) (d.slice q) =
      inner ℂ q.2 (Φ.toSuperoperator (Operator.outer q.1 p.1) p.2) := by
  let b := stdOrthonormalBasis ℂ E.state
  rw [d.channel_eq, LinearMap.comp_apply, Superoperator.conjugate_outer,
    Operator.inner_partialTraceRight b, ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [slice, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right,
    TensorProduct.mk_apply, Operator.outer_apply, inner_smul_right]

/-- An environment isometry intertwines any two dilations of the same channel when the
first environment has dimension at most that of the second. -/
theorem exists_isometry (d : Φ.Dilation E) (d' : Φ.Dilation F)
    (hdim : Module.finrank ℂ E.state ≤ Module.finrank ℂ F.state) :
    ∃ (J : E ⟶ F) (_ : IsIsometry J), d.toHom ≫ (𝟙 K ⊗ₘ J) = d'.toHom := by
  classical
  let f := Finsupp.linearCombination ℂ d.slice
  let g := Finsupp.linearCombination ℂ d'.slice
  have hgram (p q : H.state × K.state) :
      inner ℂ (d.slice p) (d.slice q) = inner ℂ (d'.slice p) (d'.slice q) := by
    rw [inner_slice, inner_slice]
  obtain ⟨V, hV⟩ := f.exists_linearIsometry_comp_eq g (by
    intro x y
    simp only [f, g, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hgram]) hdim
  have hs (p : H.state × K.state) : V (d.slice p) = d'.slice p := by
    simpa only [f, g, LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearIsometry.coe_toLinearMap] using LinearMap.congr_fun hV (Finsupp.single p 1)
  refine ⟨ofLinearIsometry V, inferInstance, hom_ext ?_⟩
  apply LinearMap.ext
  intro x
  let b := stdOrthonormalBasis ℂ K.state
  let c := stdOrthonormalBasis ℂ F.state
  apply InnerProductSpace.ext_inner_left_basis (b.tensorProduct c).toBasis
  rintro ⟨i, j⟩
  rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply, hom_comp,
    LinearMap.comp_apply, hom_tensorHom, hom_id, hom_ofLinearIsometry,
    ← LinearMap.adjoint_inner_left, TensorProduct.adjoint_map, TensorProduct.map_tmul,
    LinearMap.adjoint_id, LinearMap.id_apply]
  have he : inner ℂ (c j) (V.toLinearMap (d.slice (x, b i))) =
      inner ℂ (c j) (d'.slice (x, b i)) := congrArg (inner ℂ (c j)) (hs (x, b i))
  rw [← LinearMap.adjoint_inner_left] at he
  simpa only [slice, LinearMap.adjoint_inner_right, TensorProduct.mk_apply] using he

/-- Intertwining the Stinespring isometries intertwines their complementary channels on
all input operators. -/
lemma complementary_eq_comp_of_intertwines (d : Φ.Dilation E) (d' : Φ.Dilation F)
    (J : E ⟶ F) [IsIsometry J] (hJ : d.toHom ≫ (𝟙 K ⊗ₘ J) = d'.toHom) :
    d'.complementary = (ofIsometry J).comp d.complementary := by
  unfold complementary
  have he : ofIsometry (d.toHom ≫ (𝟙 K ⊗ₘ J)) = ofIsometry d'.toHom :=
    QuantumChannel.ext (congrArg (fun f : H ⟶ K ⊗ F => Superoperator.conjugate f.hom) hJ)
  rw [← he, ofIsometry_comp, ofIsometry_tensor, ofIsometry_id, ← comp_assoc,
    partialTraceLeft_comp_tensor, comp_assoc]

end

end Qudit.QuantumChannel.Dilation
