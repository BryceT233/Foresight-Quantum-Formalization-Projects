/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Degradation.Basic

/-!
# Recovering an isometrically embedded system

Compression by the adjoint recovers the input on the image of an isometry. On its orthogonal
complement one may apply any channel going back to the input space. This completes compression
to a trace-preserving channel on all operators, including coherences between the two subspaces.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.QuantumChannel

noncomputable section

variable {H K : Qudit}

/-- An isometric channel admits a CPTP left inverse whenever a channel in the reverse
direction exists. The latter condition also covers zero-dimensional systems exactly. -/
theorem exists_leftInverse_ofIsometry (J : H ⟶ K) [IsIsometry J] (Γ : QuantumChannel K H) :
    ∃ D : QuantumChannel K H, D.comp (ofIsometry J) = id H := by
  let P : Operator K := J.hom ∘ₗ J.hom.adjoint
  let Q : Operator K := 1 - P
  have hP : P * P = P := by
    change (J.hom ∘ₗ J.hom.adjoint) ∘ₗ (J.hom ∘ₗ J.hom.adjoint) = _
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc J.hom.adjoint,
      hom_adjoint_comp_of_isIsometry, LinearMap.id_comp]
  have hQadj : Q.adjoint = Q := by
    simp [Q, P, LinearMap.adjoint_comp]
  have hQ : Q * Q = Q := by simp [Q, mul_sub, sub_mul, hP]
  have hQJ : Q ∘ₗ J.hom = 0 := by
    dsimp only [Q, P]
    rw [LinearMap.sub_comp, LinearMap.comp_assoc, hom_adjoint_comp_of_isIsometry,
      LinearMap.comp_id, Module.End.one_eq_id, LinearMap.id_comp, sub_self]
  let S : Superoperator K H := Superoperator.conjugate J.hom.adjoint +
    Γ.toSuperoperator ∘ₗ Superoperator.conjugate Q
  have hcp : S.IsCompletelyPositive := by
    let b := stdOrthonormalBasis ℂ K.state
    apply (Superoperator.isCompletelyPositive_iff_choi_positive b S).mpr
    rw [show S = _ + _ from rfl, map_add]
    exact ((Superoperator.isCompletelyPositive_conjugate J.hom.adjoint).choi_positive b).add
      ((Γ.completelyPositive.comp (Superoperator.isCompletelyPositive_conjugate Q)).choi_positive b)
  have htp : S.IsTracePreserving := by
    intro A
    change (LinearMap.trace ℂ H.state) (_ + _) = _
    rw [map_add]
    change (Superoperator.conjugate J.hom.adjoint A).trace +
      (Γ.toSuperoperator (Superoperator.conjugate Q A)).trace = _
    rw [Γ.tracePreserving, Superoperator.trace_conjugate, Superoperator.trace_conjugate,
      LinearMap.adjoint_adjoint, hQadj, show Q ∘ₗ Q = Q from hQ]
    change Operator.trace (P * A) + Operator.trace (Q * A) = _
    rw [← map_add, ← add_mul, show P + Q = 1 by simp [Q], one_mul]
  refine ⟨⟨S, hcp, htp⟩, QuantumChannel.ext ?_⟩
  change S ∘ₗ Superoperator.conjugate J.hom = LinearMap.id
  dsimp only [S]
  rw [LinearMap.add_comp, LinearMap.comp_assoc, ← Superoperator.conjugate_comp,
    ← Superoperator.conjugate_comp, hom_adjoint_comp_of_isIsometry, hQJ,
    Superoperator.conjugate_id]
  have hz : Superoperator.conjugate (0 : H.state →ₗ[ℂ] K.state) = 0 := by
    ext A x
    simp [Superoperator.conjugate_apply]
  rw [hz, LinearMap.comp_zero, add_zero]

end

end Qudit.QuantumChannel
