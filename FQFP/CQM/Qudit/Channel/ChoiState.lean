/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Choi

/-!
# Positive Choi operators and normalized Choi states

Every positive operator on output tensor input is the Choi operator of a completely
positive map. For a channel, its trace is the input dimension. Dividing by that dimension
gives a density operator whenever the input has positive dimension.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped ComplexOrder

namespace Qudit

noncomputable section

variable {H K L : Qudit} {ι : Type*} [Fintype ι]

namespace Superoperator

/-- Postprocessing a map acts only on the output factor of its Choi operator. -/
lemma choi_comp (b : OrthonormalBasis ι ℂ H.state) (Φ : Superoperator H K)
    (Ψ : Superoperator K L) :
    choi b (Ψ ∘ₗ Φ) = tensor Ψ (LinearMap.id : Superoperator H H) (choi b Φ) := by
  simp only [choi_apply, map_sum, tensor_apply, LinearMap.comp_apply, LinearMap.id_apply]

/-- Every positive Choi operator represents a completely positive map. -/
lemma exists_of_choi_positive (b : OrthonormalBasis ι ℂ H.state)
    (A : Operator (K ⊗ H)) (hA : A.IsPositive) :
    ∃ Φ : Superoperator H K, Φ.IsCompletelyPositive ∧ choi b Φ = A := by
  obtain ⟨v, hv⟩ := Operator.exists_sum_outer_of_isPositive A hA
  refine ⟨kraus (fun i => unvectorize b (v i)), isCompletelyPositive_kraus _, ?_⟩
  simp only [kraus, map_sum, choi_conjugate, vectorize_unvectorize, ← hv]

end Superoperator

namespace QuantumChannel

/-- The unnormalized Choi operator of a channel has trace equal to the input dimension. -/
lemma trace_choi (b : OrthonormalBasis ι ℂ H.state) (Φ : QuantumChannel H K) :
    (Superoperator.choi b Φ.toSuperoperator).trace = Module.finrank ℂ H.state := by
  have h := (Superoperator.isTracePreserving_iff_partialTraceLeft_choi b _).mp Φ.tracePreserving
  calc
    _ = (Operator.partialTraceLeft (Superoperator.choi b Φ.toSuperoperator)).trace :=
      (LinearMap.trace_partialTraceLeft _).symm
    _ = _ := by rw [h, Operator.trace, LinearMap.trace_one]

/-- The Choi density operator, with the reference on the right. -/
def choiState (b : OrthonormalBasis ι ℂ H.state) (Φ : QuantumChannel H K)
    (hH : 0 < Module.finrank ℂ H.state) : Density (K ⊗ H) where
  op := (Module.finrank ℂ H.state : ℂ)⁻¹ • Superoperator.choi b Φ.toSuperoperator
  positive := (Φ.completelyPositive.choi_positive b).smul_of_nonneg (by positivity)
  trace_one := by
    change LinearMap.trace ℂ (K ⊗ H).state (_ • _) = 1
    rw [map_smul]
    change _ * (Superoperator.choi b Φ.toSuperoperator).trace = 1
    rw [trace_choi, inv_mul_cancel₀ (by exact_mod_cast hH.ne')]

end QuantumChannel

end

end Qudit
