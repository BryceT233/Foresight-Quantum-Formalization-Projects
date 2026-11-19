/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for the two ancilla branches of a heralded gate.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Gate/HeraldedBlock.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Examples.RepeatUntilSuccess

/-!
# Two-qubit heralded blocks

A block is specified by its action on a reset ancilla and arbitrary data. The orthogonal
ancilla sectors determine the two Born weights and imply that they sum to one.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit
open scoped TensorProduct

namespace QuantumProgram

open RepeatUntilSuccess (Memory outputMap selectAncilla measurement reset)

/-- Outcome zero applies the target and outcome one preserves the input data. -/
structure HeraldedBlock (W : UnitaryProgram Memory) (V : Qubit ⟶ Qubit) (α β : ℂ) : Prop where
  /-- Coherent action before measuring the ancilla. -/
  decomp (x : Qubit.state) : W.denoteHom.hom ((RepeatUntilSuccess.insert 0).hom x) =
    α • (ZBasis 2 0 ⊗ₜ[ℂ] V.hom x) + β • (ZBasis 2 1 ⊗ₜ[ℂ] x)

namespace HeraldedBlock

variable {W : UnitaryProgram Memory} {V : Qubit ⟶ Qubit} {α β : ℂ}

/-- The two branch probabilities sum to one by unitarity of the block and target. -/
theorem prob_add [IsUnitary V] (h : HeraldedBlock W V α β) : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1 := by
  have he := congrArg (fun y => ‖y‖ ^ 2) (h.decomp (ZBasis 2 0))
  simp only [pow_two] at he ⊢
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (𝕜 := ℂ) (by
    simp [inner_smul_left, inner_smul_right,
      TensorProduct.inner_tmul ℂ (ZBasis 2 0) (ZBasis 2 1)
        (V.hom (ZBasis 2 0)) (ZBasis 2 0)])] at he
  simpa [norm_smul, TensorProduct.norm_tmul (𝕜 := ℂ) (ZBasis 2 0) (V.hom (ZBasis 2 0)),
    TensorProduct.norm_tmul (𝕜 := ℂ) (ZBasis 2 1) (ZBasis 2 0)] using he.symm

/-- The Born weight of a retry as a probability in the unit interval. -/
noncomputable def retryProb [IsUnitary V] (h : HeraldedBlock W V α β) : Set.Icc (0 : ℝ) 1 :=
  ⟨‖β‖ ^ 2, sq_nonneg _, by linarith only [h.prob_add, sq_nonneg ‖α‖]⟩

/-- The measured branch on any input operator, including inputs correlated with the ancilla. -/
theorem branch_after_reset (h : HeraldedBlock W V α β) (i : Fin 2) (A : Operator Memory) :
    measurement.branch i (W.toChannel.toSuperoperator (reset.toSuperoperator A)) =
      ((if i = 0 then ‖α‖ ^ 2 else ‖β‖ ^ 2 : ℝ) : ℂ) •
        Superoperator.conjugate (outputMap V i).hom (Operator.partialTraceLeft A) := by
  let c := if i = 0 then α else β
  have hs : selectAncilla i ∘ₗ W.denoteHom.hom ∘ₗ (RepeatUntilSuccess.insert 0).hom =
      c • (outputMap V i).hom := by
    ext x : 1
    simp only [LinearMap.comp_apply, h.decomp, map_smul, map_add, RepeatUntilSuccess.select_basis]
    fin_cases i <;> simp [c, outputMap] <;> rfl
  rw [RepeatUntilSuccess.branch_after_reset_of_select _ _ _ _ hs, ← Complex.ofReal_pow]
  fin_cases i <;> rfl

end HeraldedBlock

end QuantumProgram
