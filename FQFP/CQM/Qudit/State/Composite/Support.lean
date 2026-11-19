/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for support inclusion under products and partial trace.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/Relative.lean
QuantumInfo/Entropy/DPI.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Support

/-!
# Supports of bipartite density operators

A vector in a marginal kernel annihilates every tensor with that vector.
Consequently every bipartite state is supported on the tensor product of its marginals.

## Main results

* `Qudit.Density.absolutelyContinuous_tensor_marginals`: support on the product of the marginals.
* `Qudit.Density.AbsolutelyContinuous.partialTraceRight`: discarding preserves support inclusion.
* `Qudit.Density.absolutelyContinuous_tensor_iff`: tensor support inclusion is componentwise.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- A left marginal kernel vector annihilates every tensor containing that vector. -/
lemma apply_tmul_eq_zero_of_partialTraceRight (ρ : Density (H ⊗ K))
    (x : H.state) (y : K.state) (hx : ρ.partialTraceRight.op x = 0) :
    ρ.op (x ⊗ₜ[ℂ] y) = 0 := by
  let b := stdOrthonormalBasis ℂ K.state
  have hs := congrArg Complex.re (Operator.inner_partialTraceRight b ρ.op x x)
  change (inner ℂ x (ρ.partialTraceRight.op x)).re = _ at hs
  rw [hx, inner_zero_right, Complex.zero_re, Complex.re_sum] at hs
  have hn (i) : 0 ≤ (inner ℂ (x ⊗ₜ[ℂ] b i) (ρ.op (x ⊗ₜ[ℂ] b i))).re :=
    ρ.positive.re_inner_nonneg_right _
  have hz (i) : ρ.op (x ⊗ₜ[ℂ] b i) = 0 := by
    apply (ρ.op.apply_eq_zero_iff_re_inner_eq_zero ρ.positive _).mpr
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs.symm i (Finset.mem_univ i)
  calc
    _ = ρ.op (x ⊗ₜ[ℂ] (∑ i, b.repr y i • b i)) := by rw [b.sum_repr]
    _ = 0 := by simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
      map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero]

/-- A right marginal kernel vector annihilates every tensor containing that vector. -/
lemma apply_tmul_eq_zero_of_partialTraceLeft (ρ : Density (H ⊗ K))
    (x : H.state) (y : K.state) (hy : ρ.partialTraceLeft.op y = 0) :
    ρ.op (x ⊗ₜ[ℂ] y) = 0 := by
  let b := stdOrthonormalBasis ℂ H.state
  have hs := congrArg Complex.re (Operator.inner_partialTraceLeft b ρ.op y y)
  change (inner ℂ y (ρ.partialTraceLeft.op y)).re = _ at hs
  rw [hy, inner_zero_right, Complex.zero_re, Complex.re_sum] at hs
  have hn (i) : 0 ≤ (inner ℂ (b i ⊗ₜ[ℂ] y) (ρ.op (b i ⊗ₜ[ℂ] y))).re :=
    ρ.positive.re_inner_nonneg_right _
  have hz (i) : ρ.op (b i ⊗ₜ[ℂ] y) = 0 := by
    apply (ρ.op.apply_eq_zero_iff_re_inner_eq_zero ρ.positive _).mpr
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs.symm i (Finset.mem_univ i)
  calc
    _ = ρ.op ((∑ i, b.repr x i • b i) ⊗ₜ[ℂ] y) := by rw [b.sum_repr]
    _ = 0 := by simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
      map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero]

/-- Every bipartite state is supported on the tensor product of its marginals. -/
lemma absolutelyContinuous_tensor_marginals (ρ : Density (H ⊗ K)) :
    ρ.AbsolutelyContinuous (ρ.partialTraceRight.tensor ρ.partialTraceLeft) := by
  rw [absolutelyContinuous_iff_of_right_eigenbasis ρ _
    (ρ.partialTraceRight.eigenbasis.tensorProduct ρ.partialTraceLeft.eigenbasis)
    (fun i => ρ.partialTraceRight.eigenvalue i.1 * ρ.partialTraceLeft.eigenvalue i.2)
    (ρ.partialTraceRight.tensor_apply_eigenbasis ρ.partialTraceLeft)]
  rintro ⟨i, j⟩ hij
  rw [OrthonormalBasis.tensorProduct_apply]
  rcases mul_eq_zero.mp hij with hi | hj
  · apply ρ.apply_tmul_eq_zero_of_partialTraceRight
    rw [ρ.partialTraceRight.apply_eigenbasis, hi, Complex.ofReal_zero, zero_smul]
  · apply ρ.apply_tmul_eq_zero_of_partialTraceLeft
    rw [ρ.partialTraceLeft.apply_eigenbasis, hj, Complex.ofReal_zero, zero_smul]

/-- Discarding the right system preserves absolute continuity. -/
lemma AbsolutelyContinuous.partialTraceRight {ρ σ : Density (H ⊗ K)}
    (h : ρ.AbsolutelyContinuous σ) :
    ρ.partialTraceRight.AbsolutelyContinuous σ.partialTraceRight := by
  intro x hx
  apply (ρ.partialTraceRight.op.apply_eq_zero_iff_re_inner_eq_zero
    ρ.partialTraceRight.positive x).mpr
  change (inner ℂ x (Operator.partialTraceRight ρ.op x)).re = 0
  rw [Operator.inner_partialTraceRight (stdOrthonormalBasis ℂ K.state)]
  have hz (y : K.state) : ρ.op (x ⊗ₜ[ℂ] y) = 0 :=
    h (σ.apply_tmul_eq_zero_of_partialTraceRight x y hx)
  simp only [hz, inner_zero_right, Finset.sum_const_zero, Complex.zero_re]

/-- Discarding the left system preserves absolute continuity. -/
lemma AbsolutelyContinuous.partialTraceLeft {ρ σ : Density (H ⊗ K)}
    (h : ρ.AbsolutelyContinuous σ) :
    ρ.partialTraceLeft.AbsolutelyContinuous σ.partialTraceLeft := by
  intro y hy
  apply (ρ.partialTraceLeft.op.apply_eq_zero_iff_re_inner_eq_zero
    ρ.partialTraceLeft.positive y).mpr
  change (inner ℂ y (Operator.partialTraceLeft ρ.op y)).re = 0
  rw [Operator.inner_partialTraceLeft (stdOrthonormalBasis ℂ H.state)]
  have hz (x : H.state) : ρ.op (x ⊗ₜ[ℂ] y) = 0 :=
    h (σ.apply_tmul_eq_zero_of_partialTraceLeft x y hy)
  simp only [hz, inner_zero_right, Finset.sum_const_zero, Complex.zero_re]

/-- Tensoring two absolutely continuous pairs preserves absolute continuity. -/
lemma AbsolutelyContinuous.tensor {ρ σ : Density H} {τ ω : Density K}
    (hρ : ρ.AbsolutelyContinuous σ) (hτ : τ.AbsolutelyContinuous ω) :
    (ρ.tensor τ).AbsolutelyContinuous (σ.tensor ω) := by
  rw [absolutelyContinuous_iff_of_right_eigenbasis (ρ.tensor τ) (σ.tensor ω)
    (σ.eigenbasis.tensorProduct ω.eigenbasis)
    (fun i => σ.eigenvalue i.1 * ω.eigenvalue i.2) (σ.tensor_apply_eigenbasis ω)]
  rintro ⟨i, j⟩ hij
  rw [OrthonormalBasis.tensorProduct_apply σ.eigenbasis ω.eigenbasis i j,
    op_tensor, Operator.tensor_apply]
  rcases mul_eq_zero.mp hij with hi | hj
  · have hz : ρ.op (σ.eigenbasis i) = 0 := hρ (by
      change σ.op (σ.eigenbasis i) = 0
      rw [σ.apply_eigenbasis, hi, Complex.ofReal_zero, zero_smul])
    rw [hz, TensorProduct.zero_tmul]
  · have hz : τ.op (ω.eigenbasis j) = 0 := hτ (by
      change ω.op (ω.eigenbasis j) = 0
      rw [ω.apply_eigenbasis, hj, Complex.ofReal_zero, zero_smul])
    rw [hz, TensorProduct.tmul_zero]

/-- Tensor support inclusion holds exactly when it holds in both factors. -/
lemma absolutelyContinuous_tensor_iff (ρ σ : Density H) (τ ω : Density K) :
    (ρ.tensor τ).AbsolutelyContinuous (σ.tensor ω) ↔
      ρ.AbsolutelyContinuous σ ∧ τ.AbsolutelyContinuous ω := by
  constructor
  · intro h
    exact ⟨by simpa only [partialTraceRight_tensor] using h.partialTraceRight,
      by simpa only [partialTraceLeft_tensor] using h.partialTraceLeft⟩
  · rintro ⟨hρ, hτ⟩
    exact hρ.tensor hτ

end

end Qudit.Density
