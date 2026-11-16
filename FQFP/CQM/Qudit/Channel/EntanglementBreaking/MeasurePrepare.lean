/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.EntanglementBreaking.Antidegradable

/-!
# The measure-and-prepare characterization of entanglement-breaking channels

In output-first Choi coordinates, a product decomposition gives a measurement by
transposing each weighted reference operator in the input basis. The output factors
are the prepared states. An empty outcome set represents every channel with zero input.
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

/-- Exactly the channels with zero-dimensional input have an empty-outcome representation.
The empty preparation family exists even when the output has no density states. -/
theorem exists_empty_measurePrepare_iff (Φ : QuantumChannel H K) :
    (∃ M : POVM H (Fin 0), Φ = M.measurePrepare (fun i => i.elim0)) ↔
      Module.finrank ℂ H.state = 0 := by
  constructor
  · rintro ⟨M, _⟩
    by_contra hn
    simpa using M.sum_probability (Density.maximallyMixed H hn)
  · intro hH
    have : Subsingleton H.state := Module.finrank_zero_iff.mp hH
    let M : POVM H (Fin 0) := ⟨Fin.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
    exact ⟨M, QuantumChannel.ext (Subsingleton.elim _ _)⟩

/-- A channel breaks entanglement exactly when it has a finite measure-and-prepare
representation. Empty outcome sets are allowed, so no dimension assumptions are needed. -/
theorem isEntanglementBreaking_iff_exists_measurePrepare (Φ : QuantumChannel H K) :
    Φ.IsEntanglementBreaking ↔
      ∃ (α : Type) (_ : Fintype α) (M : POVM H α) (σ : α → Density K), Φ = M.measurePrepare σ := by
  constructor
  · intro hΦ
    by_cases hH : 0 < Module.finrank ℂ H.state
    · let b := stdOrthonormalBasis ℂ H.state
      exact exists_measurePrepare_of_isSeparable_choiState b hH (hΦ.isSeparable_choiState b hH)
    · obtain ⟨M, he⟩ := (exists_empty_measurePrepare_iff Φ).mpr (by lia)
      exact ⟨Fin 0, inferInstance, M, _, he⟩
  · rintro ⟨α, _, M, σ, rfl⟩
    exact M.isEntanglementBreaking_measurePrepare σ

/-- On a positive-dimensional input, testing the normalized Choi state in a single
orthonormal basis characterizes entanglement breaking. -/
theorem isEntanglementBreaking_iff_isSeparable_choiState (Φ : QuantumChannel H K)
    (b : OrthonormalBasis ι ℂ H.state) (hH : 0 < Module.finrank ℂ H.state) :
    Φ.IsEntanglementBreaking ↔ (Φ.choiState b hH).IsSeparable :=
  ⟨fun h => h.isSeparable_choiState b hH, fun h =>
    (isEntanglementBreaking_iff_exists_measurePrepare Φ).mpr
      (exists_measurePrepare_of_isSeparable_choiState b hH h)⟩

end

end Qudit.QuantumChannel
