/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Category
public import FQFP.CQM.Qudit.Channel.Dilation.Basic

/-!
# Discarding and purification of finite-dimensional CP processes

Discarding is the complex trace, encoded as an operator on the tensor unit. Causality
is exactly trace preservation. Every CP process admits a pure dilation, without any
normalization assumption. The environment is on the right throughout this API.

## Main definitions and results

* `Qudit.CPQudit.discard`: discarding as a completely positive process.
* `Qudit.CPQudit.IsCausal`: preservation of discarding.
* `Qudit.CPQudit.isCausal_iff`: causality is trace preservation.
* `Qudit.CPQudit.exists_pure_comp_discard`: every CP process has a pure dilation.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit

noncomputable section

namespace Operator

/-- The trace pairing separates operators, including on the zero-dimensional space. -/
lemma ext_trace {H : Qudit} {A B : Operator H}
    (h : ∀ C, (A * C).trace = (B * C).trace) : A = B := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simpa only [trace_mul_outer] using h (outer x y)

/-- An operator on the scalar system is multiplication by its value at one. -/
lemma scalar_eq (A : Operator (of ℂ)) : A = A (1 : ℂ) • (1 : Operator (of ℂ)) := by
  apply LinearMap.ext_ring
  simp

/-- The trace of a scalar operator is its value at one. -/
lemma trace_scalar (A : Operator (of ℂ)) : A.trace = A (1 : ℂ) := by
  conv_lhs => rw [scalar_eq A]
  simp [trace]

end Operator

namespace Superoperator

/-- Discard a system by taking its trace, as an operator on the tensor unit. -/
def discard (H : Qudit) : Superoperator H (𝟙_ Qudit) :=
  (LinearMap.toSpanSingleton ℂ (Operator (𝟙_ Qudit)) 1) ∘ₗ LinearMap.trace ℂ H.state

/-- Discarding returns the trace times the scalar identity. -/
lemma discard_apply (H : Qudit) (A : Operator H) : discard H A = A.trace • 1 := rfl

/-- Discarding is a Kraus sum of the bras of any orthonormal basis. -/
lemma discard_eq_kraus {H : Qudit} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) : discard H = kraus (fun i => bra (b i)) := by
  apply LinearMap.ext
  intro A
  apply LinearMap.ext_ring
  rw [discard_apply, kraus_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, one_apply_eq_self, smul_eq_mul, mul_one,
    LinearMap.comp_apply, bra, LinearMap.adjoint_innerₛₗ_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  exact LinearMap.trace_eq_sum_inner A b

/-- Discarding is completely positive. -/
lemma isCompletelyPositive_discard (H : Qudit) : (discard H).IsCompletelyPositive := by
  rw [discard_eq_kraus (stdOrthonormalBasis ℂ H.state)]
  exact isCompletelyPositive_kraus _

/-- Discarding preserves the trace. -/
lemma isTracePreserving_discard (H : Qudit) : (discard H).IsTracePreserving := by
  intro A
  rw [Operator.trace_scalar, discard_apply]
  simp

/-- Discarding after conjugation is the trace pairing with the adjoint square. -/
lemma discard_conjugate_apply {H K : Qudit} (f : H.state →ₗ[ℂ] K.state)
    (A : Operator H) :
    discard K (conjugate f A) = Operator.trace ((f.adjoint ∘ₗ f) * A) • 1 := by
  rw [discard_apply, conjugate_apply, Operator.trace, LinearMap.trace_comp_comm',
    LinearMap.comp_assoc]
  rw [← Module.End.mul_eq_comp, LinearMap.trace_mul_comm]

/-- The right unit constraint contracts a scalar operator by its trace. -/
lemma conjugate_rightUnitor_tensor {H : Qudit} (A : Operator H)
    (B : Operator (of ℂ)) :
    conjugate (ρ_ H).hom.hom (Operator.tensor A B) = B.trace • A := by
  change conjugate (H := H ⊗ of ℂ) (K := H) (TensorProduct.ridIsometry ℂ H.state).toLinearMap _ = _
  rw [← relabel_eq_conjugate, Operator.trace_scalar]
  ext x
  change (TensorProduct.rid ℂ H.state)
    (TensorProduct.map A B ((TensorProduct.rid ℂ H.state).symm x)) = B (1 : ℂ) • A x
  simp

end Superoperator

namespace CPQudit

/-- The physical discarding process. It is not the deletion map of a chosen basis. -/
def discard (H : CPQudit) : H ⟶ 𝟙_ CPQudit :=
  ⟨Superoperator.discard H.toQudit, Superoperator.isCompletelyPositive_discard H.toQudit⟩

/-- Discarding on the scalar system is the identity. -/
lemma discard_unit : discard (𝟙_ CPQudit) = 𝟙 _ := by
  apply hom_ext
  apply LinearMap.ext
  intro A
  change A.trace • 1 = A
  rw [Operator.trace_scalar, ← Operator.scalar_eq]

/-- Discarding respects tensor products, with the scalar unit constraint explicit. -/
lemma discard_tensor (H K : CPQudit) :
    discard (H ⊗ K) = (discard H ⊗ₘ discard K) ≫ (ρ_ (𝟙_ CPQudit)).hom := by
  apply hom_ext
  apply Operator.tensor_ext
  intro A B
  change Superoperator.discard (H.toQudit ⊗ K.toQudit) (Operator.tensor A B) =
    Superoperator.conjugate (ρ_ (𝟙_ Qudit)).hom.hom
      (Superoperator.tensor (Superoperator.discard H.toQudit)
        (Superoperator.discard K.toQudit) (Operator.tensor A B))
  rw [Superoperator.tensor_apply, Superoperator.conjugate_rightUnitor_tensor,
    Superoperator.isTracePreserving_discard, Superoperator.discard_apply,
    Superoperator.discard_apply, Operator.trace_tensor, smul_smul, mul_comm]

/-- The right partial trace is exactly tensoring with discarding and removing the unit. -/
lemma tensor_discard (H K : CPQudit) :
    ((𝟙 H ⊗ₘ discard K) ≫ (ρ_ H).hom).toSuperoperator =
      (Operator.partialTraceRight : Superoperator (H.toQudit ⊗ K.toQudit) H.toQudit) := by
  apply Operator.tensor_ext
  intro A B
  change Superoperator.conjugate (ρ_ H.toQudit).hom.hom
    (Superoperator.tensor LinearMap.id (Superoperator.discard K.toQudit)
      (Operator.tensor A B)) = Operator.partialTraceRight (Operator.tensor A B)
  rw [Superoperator.tensor_apply, Superoperator.conjugate_rightUnitor_tensor,
    Superoperator.isTracePreserving_discard, Operator.partialTraceRight_tensor]
  rfl

/-- A process is causal when discarding its output equals discarding its input. -/
def IsCausal {H K : CPQudit} (f : H ⟶ K) : Prop := f ≫ discard K = discard H

/-- Causality is precisely preservation of the trace on all operators. -/
lemma isCausal_iff {H K : CPQudit} (f : H ⟶ K) :
    IsCausal f ↔ f.toSuperoperator.IsTracePreserving := by
  constructor
  · intro h A
    have e := congrArg (fun f => f.toSuperoperator A (1 : ℂ)) h
    change (f.toSuperoperator A).trace * 1 = A.trace * 1 at e
    simpa using e
  · intro h
    apply hom_ext
    apply LinearMap.ext
    intro A
    apply LinearMap.ext
    intro x
    change (f.toSuperoperator A).trace * x = A.trace * x
    rw [h A]

/-- The environment's separation axiom: equal discarded pure processes are exactly
equal adjoint squares. The two output spaces need not have the same dimension. -/
lemma pure_comp_discard_iff {H K L : Qudit} (f : H ⟶ K) (g : H ⟶ L) :
    pure.map f ≫ discard ⟨K⟩ = pure.map g ≫ discard ⟨L⟩ ↔ f ≫ f† = g ≫ g† := by
  dsimp only [pure]
  constructor
  · intro h
    apply Qudit.hom_ext
    apply Operator.ext_trace
    intro A
    have e := congrArg (fun f => f.toSuperoperator A (1 : ℂ)) h
    change Superoperator.discard K (Superoperator.conjugate f.hom A) (1 : ℂ) =
      Superoperator.discard L (Superoperator.conjugate g.hom A) (1 : ℂ) at e
    simp only [Superoperator.discard_conjugate_apply, LinearMap.smul_apply,
      one_apply_eq_self, smul_eq_mul, mul_one] at e
    exact e
  · intro h
    apply hom_ext
    apply LinearMap.ext
    intro A
    change Superoperator.discard K (Superoperator.conjugate f.hom A) =
      Superoperator.discard L (Superoperator.conjugate g.hom A)
    simp only [Superoperator.discard_conjugate_apply]
    rw [show f.hom.adjoint ∘ₗ f.hom = g.hom.adjoint ∘ₗ g.hom from congrArg Hom.hom h]

/-- Every CP process is a pure process followed by a finite environmental partial trace.
No trace normalization or positive-dimension assumption is imposed. -/
lemma exists_purification {H K : CPQudit} (f : H ⟶ K) :
    ∃ (n : ℕ) (V : H.toQudit ⟶ K.toQudit ⊗ std n),
      f.toSuperoperator = (Operator.partialTraceRight :
        Superoperator (K.toQudit ⊗ std n) K.toQudit) ∘ₗ Superoperator.conjugate V.hom := by
  obtain ⟨n, a, ha⟩ := f.completelyPositive.exists_kraus
  exact ⟨n, ofHom (Superoperator.krausDilation (ZBasis n) a),
    ha.trans (Superoperator.partialTraceRight_conjugate_krausDilation (ZBasis n) a).symm⟩

/-- Purification expressed entirely as composition in the CP process category. -/
lemma exists_pure_comp_discard {H K : CPQudit} (f : H ⟶ K) :
    ∃ (n : ℕ) (V : H.toQudit ⟶ K.toQudit ⊗ std n),
      f = pure.map V ≫ (𝟙 K ⊗ₘ discard ⟨std n⟩) ≫ (ρ_ K).hom := by
  obtain ⟨n, V, hV⟩ := exists_purification f
  refine ⟨n, V, hom_ext ?_⟩
  exact hV.trans (congrArg (fun S => S ∘ₗ Superoperator.conjugate V.hom)
    (tensor_discard K ⟨std n⟩).symm)

end CPQudit

end

end Qudit
