/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the proposed maximally entangled input criterion.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/CPTP.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.ChoiState
public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.Basic

/-!
# From a separable Choi state to a measurement and preparations

The weighted reference factors give the POVM after transposition in the input basis.
The output factors are the prepared states.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct ComplexOrder

namespace Qudit.QuantumChannel

noncomputable section

variable {H K : Qudit} {Φ : QuantumChannel H K} {ι α : Type*} [Fintype ι] [Fintype α]

/-- For a product decomposition of the unnormalized Choi operator, the input effects are
the basis transposes of the positive reference operators. The prepared states and outcome
labels are exactly those of the given decomposition. -/
theorem exists_measurePrepare_of_choi_eq_sum_tensor [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H.state) (σ : α → Density K) (R : α → Operator H)
    (hR : ∀ a, (R a).IsPositive)
    (hChoi : Superoperator.choi b Φ.toSuperoperator = ∑ a, Operator.tensor (σ a).op (R a)) :
    ∃ M : POVM H α, (∀ a, LinearMap.toMatrixOrthonormal b (M.op a) =
      (LinearMap.toMatrixOrthonormal b (R a)).transpose) ∧ Φ = M.measurePrepare σ := by
  let e := LinearMap.toMatrixOrthonormal b
  have hsum : ∑ a, R a = 1 := by
    have h := (Superoperator.isTracePreserving_iff_partialTraceLeft_choi b _).mp Φ.tracePreserving
    simpa only [hChoi, map_sum, Operator.partialTraceLeft_tensor, Density.trace_one, one_smul]
      using h
  let M : POVM H α :=
    { op := fun a => e.symm (e (R a)).transpose
      positive := fun a => (Operator.posSemidef_toMatrix_iff b _).mp (by
        change (e (e.symm _)).PosSemidef
        rw [e.apply_symm_apply, Matrix.posSemidef_transpose_iff]
        exact (Operator.posSemidef_toMatrix_iff b _).mpr (hR a))
      sum_op := by
        apply e.injective
        simp only [← Matrix.transpose_sum, ← map_sum, hsum,
          map_one, Matrix.transpose_one] }
  have hM (a : α) : e (M.op a) = (e (R a)).transpose := e.apply_symm_apply _
  refine ⟨M, hM, QuantumChannel.ext (Operator.basis_outer_ext b ?_)⟩
  intro i j
  have hcoeff (a : α) : inner ℂ (b j) (M.op a (b i)) = inner ℂ (b i) (R a (b j)) := by
    simpa only [e, Matrix.transpose_apply, LinearMap.toMatrixOrthonormal_apply_apply]
      using congrArg (fun A : Matrix ι ι ℂ => A j i) (hM a)
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [← Superoperator.inner_choi b Φ.toSuperoperator x y i j, hChoi, M.measurePrepare_apply]
  simp only [LinearMap.sum_apply, inner_sum, Operator.tensor_apply, TensorProduct.inner_tmul,
    Operator.trace_mul_outer, hcoeff, LinearMap.smul_apply, inner_smul_right]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- A separable normalized Choi state in any one input basis gives a finite POVM
and a prepared density for each outcome. -/
theorem exists_measurePrepare_of_isSeparable_choiState (b : OrthonormalBasis ι ℂ H.state)
    (hH : 0 < Module.finrank ℂ H.state) (hsep : (Φ.choiState b hH).IsSeparable) :
    ∃ (α : Type) (_ : Fintype α) (M : POVM H α) (σ : α → Density K), Φ = M.measurePrepare σ := by
  classical
  obtain ⟨α, _, w, hw, hs, σ, ρ, he⟩ := (Density.isSeparable_iff_exists_mixture _).mp hsep
  let n : ℂ := Module.finrank ℂ H.state
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast hH.ne'
  let R (a : α) := (n * (w a : ℂ)) • (ρ a).op
  have hR (a : α) : (R a).IsPositive :=
    (ρ a).positive.smul_of_nonneg (mul_nonneg (by dsimp [n]; positivity) (by exact_mod_cast hw a))
  have hChoi : Superoperator.choi b Φ.toSuperoperator = ∑ a, Operator.tensor (σ a).op (R a) := by
    calc
      _ = n • (Φ.choiState b hH).op := by
        change _ = n • (n⁻¹ • _)
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = _ := by
        rw [← he, Density.op_mixture, Finset.smul_sum]
        simp only [R, Density.op_tensor, smul_smul, Operator.tensor, TensorProduct.map_smul_right]
  obtain ⟨M, _, hM⟩ := exists_measurePrepare_of_choi_eq_sum_tensor b σ R hR hChoi
  exact ⟨α, inferInstance, M, σ, hM⟩

end

end Qudit.QuantumChannel
