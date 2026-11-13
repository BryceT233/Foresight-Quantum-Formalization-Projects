/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Channel.Dilation
import FQFP.CQM.Qudit.Classical
import FQFP.CQM.Qudit.Measurement.Luders

/-!
# Choi, Kraus completeness, and finite dilation clients

Rectangular complex coordinates, Choi normalization, basis-independent positivity,
classical copying as a coherent measurement dilation, and zero-dimensional boundaries.
-/

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct ComplexOrder

noncomputable section

-- Necessity for an arbitrary channel, with no supplied Kraus data.
example {H K : Qudit} (Φ : QuantumChannel H K) :
    ∃ f : Fin (Module.finrank ℂ K.state * Module.finrank ℂ H.state) →
        H.state →ₗ[ℂ] K.state,
      Φ.toSuperoperator = Superoperator.kraus f ∧ ∑ i, (f i).adjoint ∘ₗ f i = 1 :=
  Φ.exists_kraus_finrank

-- A qutrit-to-qubit channel has a six-dimensional environment available.
example (Φ : QuantumChannel (std 3) Qubit) :
    ∃ V : std 3 ⟶ Qubit ⊗ std 6,
      IsIsometry V ∧ Φ.toSuperoperator =
        (Operator.partialTraceRight : Superoperator (Qubit ⊗ std 6) Qubit) ∘ₗ
          Superoperator.conjugate V.hom := by
  have hd : Module.finrank ℂ Qubit.state * Module.finrank ℂ (std 3).state = 6 := by
    rw [finrank_std 2, finrank_std 3]
  rw [← hd]
  exact Φ.exists_dilation_finrank

-- Dilation acts correctly on every mixed input, not only on basis states.
example {H K : Qudit} (Φ : QuantumChannel H K) :
    ∃ (n : ℕ) (V : H ⟶ K ⊗ std n) (_hV : IsIsometry V),
      ∀ ρ : Density H, Φ.map ρ = (ρ.map V).partialTraceRight := Φ.exists_dilation_map

-- Choi positivity is unchanged by an entirely different indexed orthonormal basis.
example {H K : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ H.state)
    (Φ : Superoperator H K) :
    (Superoperator.choi b Φ).IsPositive ↔ (Superoperator.choi c Φ).IsPositive :=
  Superoperator.choi_positive_iff b c Φ

-- The unnormalized identity Choi operator has trace d, not 1.
example (n : ℕ) :
    (Superoperator.choi (ZBasis n) (QuantumChannel.id (std n)).toSuperoperator).trace = n := by
  have hm := (Superoperator.isTracePreserving_iff_partialTraceLeft_choi (ZBasis n)
    (QuantumChannel.id (std n)).toSuperoperator).mp (QuantumChannel.id (std n)).tracePreserving
  calc
    _ = (Operator.partialTraceLeft
        (Superoperator.choi (ZBasis n) (QuantumChannel.id (std n)).toSuperoperator)).trace :=
      (LinearMap.trace_partialTraceLeft _).symm
    _ = n := by rw [hm]; simp [Operator.trace, LinearMap.trace_one]

private def rectangularProcess : (std 2).state →ₗ[ℂ] (std 3).state :=
  (bra (ZBasis 2 0)).smulRight (ZBasis 3 0) +
    (bra (ZBasis 2 1)).smulRight (Complex.I • ZBasis 3 2)

-- This off-diagonal complex entry checks both factor order and conjugation convention.
example :
    LinearMap.toMatrixOrthonormal ((ZBasis 3).tensorProduct (ZBasis 2))
      (Superoperator.choi (ZBasis 2) (Superoperator.conjugate rectangularProcess))
        (0, 0) (2, 1) = -Complex.I := by
  rw [Superoperator.toMatrix_choi, Superoperator.conjugate_outer,
    LinearMap.toMatrixOrthonormal_apply_apply]
  simp [rectangularProcess, bra_apply, Operator.outer_apply, inner_smul_left, inner_smul_right]

-- Classical copying is precisely the coherent dilation of the basis projectors.
private lemma dilation_basisCopy {H : Qudit} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    Superoperator.krausDilation b (fun i => Operator.outer (b i) (b i)) = (basisCopy b).hom := by
  classical
  apply b.toBasis.ext
  intro j
  rw [Superoperator.krausDilation_apply]
  change (∑ i, (inner ℂ (b i) (b j) • b i) ⊗ₜ[ℂ] b i) = basisCopy b (b j)
  simp [b.inner_eq_ite, ite_smul, TensorProduct.ite_tmul]

-- Forgetting the environment recovers the previously implemented unread Lüders measurement.
example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    (Operator.partialTraceRight : Superoperator (H ⊗ H) H) ∘ₗ
      Superoperator.conjugate (basisCopy b).hom = (POVM.ofBasis b).luders.toChannel.toSuperoperator := by
  rw [← dilation_basisCopy b, Superoperator.partialTraceRight_conjugate_krausDilation]
  apply LinearMap.ext
  intro A
  change Superoperator.kraus (fun i => Operator.outer (b i) (b i)) A =
    (∑ i, (POVM.ofBasis b).luders.branch i) A
  rw [Superoperator.kraus_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [POVM.luders_ofBasis_branch]
  ext x
  simp [Operator.outer_apply, LinearMap.comp_apply, smul_smul, mul_comm]

-- An empty Kraus family is a legitimate channel from a zero-dimensional input.
private def emptyInputChannel : QuantumChannel (std 0) Qubit :=
  QuantumChannel.ofKraus (fun i : Fin 0 => Fin.elim0 i) (Subsingleton.elim _ _)

example :
    ∃ V : std 0 ⟶ Qubit ⊗ std 0,
      IsIsometry V ∧ emptyInputChannel.toSuperoperator =
        (Operator.partialTraceRight : Superoperator (Qubit ⊗ std 0) Qubit) ∘ₗ
          Superoperator.conjugate V.hom := by
  have hd : Module.finrank ℂ Qubit.state * Module.finrank ℂ (std 0).state = 0 := by
    rw [finrank_std 0, Nat.mul_zero]
  have h := emptyInputChannel.exists_dilation_finrank
  rw [hd] at h
  exact h

example : Superoperator.choi (ZBasis 0) emptyInputChannel.toSuperoperator = 0 := by
  simp [Superoperator.choi_apply]

-- A nonzero input cannot acquire a fictitious channel to a zero-dimensional output.
example (Φ : QuantumChannel Qubit (std 0)) : False :=
  isEmptyElim (Φ.map (Density.pure (UnitState.ofBasis (ZBasis 2) 0)))

-- A non-CP map is rejected by Choi positivity: the qubit reduction map has a negative direction.
private def reduction : Superoperator Qubit Qubit :=
  (LinearMap.trace ℂ Qubit.state).smulRight (1 : Operator Qubit) - LinearMap.id

example : ¬ reduction.IsCompletelyPositive := by
  intro h
  let v := ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 0 + ZBasis 2 1 ⊗ₜ[ℂ] ZBasis 2 1
  have hv := (h.choi_positive (ZBasis 2)).re_inner_nonneg_right v
  simp only [v, map_add, inner_add_left, inner_add_right,
    Superoperator.inner_choi (ZBasis 2) reduction] at hv
  norm_num [reduction, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.id_apply, Operator.trace_outer, Operator.outer_apply, inner_sub_right,
    inner_smul_right] at hv
