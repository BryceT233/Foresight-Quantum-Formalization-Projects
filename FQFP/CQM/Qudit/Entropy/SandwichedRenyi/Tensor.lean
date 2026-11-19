/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for tensor additivity of the sandwiched divergence.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/Relative.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.DataProcessing

/-!
# Sandwiched Rényi relative entropy of tensor products

The spectrum of the product sandwich consists of the pairwise products of the local
sandwich eigenvalues, with multiplicities. The trace functional therefore factors.
At order above one this gives additivity of the divergence, including infinite values.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped BigOperators TensorProduct

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- Real spectral powers factor over tensor products of density operators. -/
lemma spectralMap_rpow_tensor (σ : Density H) (ω : Density K) (t : ℝ) :
    (σ.tensor ω).spectralMap (fun x => x ^ t) =
      Operator.tensor (σ.spectralMap (fun x => x ^ t)) (ω.spectralMap (fun x => x ^ t)) := by
  apply (σ.eigenbasis.tensorProduct ω.eigenbasis).toBasis.ext
  rintro ⟨i, j⟩
  simp only [OrthonormalBasis.coe_toBasis]
  rw [(σ.tensor ω).spectralMap_apply_of_eigenvector _ (σ.tensor_apply_eigenbasis ω (i, j))]
  rw [OrthonormalBasis.tensorProduct_apply, Operator.tensor_apply,
    σ.spectralMap_apply_eigenbasis, ω.spectralMap_apply_eigenbasis]
  simp only [Real.mul_rpow (σ.eigenvalue_nonneg i) (ω.eigenvalue_nonneg j),
    Complex.ofReal_mul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]

/-- Independent sources and references give a tensor product of the two sandwiches. -/
lemma renyiSandwich_tensor (ρ σ : Density H) (τ ω : Density K) (s : ℝ) :
    (ρ.tensor τ).renyiSandwich (σ.tensor ω) s =
      Operator.tensor (ρ.renyiSandwich σ s) (τ.renyiSandwich ω s) := by
  simp only [renyiSandwich, adjoint_spectralMap]
  rw [spectralMap_rpow_tensor, op_tensor]
  simp only [Operator.tensor, TensorProduct.map_comp]

/-- The sandwiched trace functional is multiplicative for every real exponent. -/
theorem sandwichedTraceFunctional_tensor (ρ σ : Density H) (τ ω : Density K) (α : ℝ) :
    (ρ.tensor τ).sandwichedTraceFunctional (σ.tensor ω) α =
      ρ.sandwichedTraceFunctional σ α * τ.sandwichedTraceFunctional ω α := by
  let A := ρ.renyiSandwich_positive σ (1 - α⁻¹)
  let B := τ.renyiSandwich_positive ω (1 - α⁻¹)
  let b := A.isSymmetric.eigenvectorBasis rfl
  let c := B.isSymmetric.eigenvectorBasis rfl
  let x := A.isSymmetric.eigenvalues rfl
  let y := B.isSymmetric.eigenvalues rfl
  rw [sandwichedTraceFunctional_eq_sum_of_eigenbasis _ _ α (b.tensorProduct c)
    (fun i => x i.1 * y i.2)]
  · have hpow (i j) : (x i * y j) ^ α = x i ^ α * y j ^ α :=
      Real.mul_rpow (A.nonneg_eigenvalues rfl i) (B.nonneg_eigenvalues rfl j)
    simp only [Fintype.sum_prod_type, hpow, ← Finset.mul_sum, ← Finset.sum_mul]
    rfl
  · rintro ⟨i, j⟩
    have hi : ρ.renyiSandwich σ (1 - α⁻¹) (b i) = (x i : ℂ) • b i :=
      A.isSymmetric.apply_eigenvectorBasis rfl i
    have hj : τ.renyiSandwich ω (1 - α⁻¹) (c j) = (y j : ℂ) • c j :=
      B.isSymmetric.apply_eigenvectorBasis rfl j
    rw [renyiSandwich_tensor, OrthonormalBasis.tensorProduct_apply, Operator.tensor_apply, hi, hj,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Complex.ofReal_mul]

/-- Sandwiched Rényi relative entropy of order above one is additive on independent pairs. -/
theorem sandwichedRenyiRelativeEntropy_tensor (ρ σ : Density H) (τ ω : Density K)
    (α : Set.Ioi (1 : ℝ)) :
    (ρ.tensor τ).sandwichedRenyiRelativeEntropy (σ.tensor ω) α =
      ρ.sandwichedRenyiRelativeEntropy σ α + τ.sandwichedRenyiRelativeEntropy ω α := by
  classical
  simp only [sandwichedRenyiRelativeEntropy, absolutelyContinuous_tensor_iff]
  by_cases hρ : ρ.AbsolutelyContinuous σ <;> by_cases hτ : τ.AbsolutelyContinuous ω <;>
    simp only [hρ, hτ, and_self, and_true, and_false, reduceIte, top_add, add_top]
  have hx := ρ.one_le_sandwichedTraceFunctional σ α.property hρ
  have hy := τ.one_le_sandwichedTraceFunctional ω α.property hτ
  rw [sandwichedTraceFunctional_tensor, Real.log_mul (zero_lt_one.trans_le hx).ne'
    (zero_lt_one.trans_le hy).ne', add_div]
  exact ENNReal.ofReal_add (div_nonneg (Real.log_nonneg hx) (sub_nonneg.mpr α.property.le))
    (div_nonneg (Real.log_nonneg hy) (sub_nonneg.mpr α.property.le))

/-- Appending a common ancillary state preserves the divergence. -/
theorem sandwichedRenyiRelativeEntropy_tensor_right (ρ σ : Density H) (τ : Density K)
    (α : Set.Ioi (1 : ℝ)) :
    (ρ.tensor τ).sandwichedRenyiRelativeEntropy (σ.tensor τ) α =
      ρ.sandwichedRenyiRelativeEntropy σ α := by
  rw [sandwichedRenyiRelativeEntropy_tensor, sandwichedRenyiRelativeEntropy_self, add_zero]

/-- Prepending a common ancillary state preserves the divergence. -/
theorem sandwichedRenyiRelativeEntropy_tensor_left (ρ σ : Density K) (τ : Density H)
    (α : Set.Ioi (1 : ℝ)) :
    (τ.tensor ρ).sandwichedRenyiRelativeEntropy (τ.tensor σ) α =
      ρ.sandwichedRenyiRelativeEntropy σ α := by
  rw [sandwichedRenyiRelativeEntropy_tensor, sandwichedRenyiRelativeEntropy_self, zero_add]

end

end Qudit.Density
