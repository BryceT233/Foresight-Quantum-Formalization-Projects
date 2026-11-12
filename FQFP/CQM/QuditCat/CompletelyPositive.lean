/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.QuditCat.Superoperator

/-!
# Completely positive and trace-preserving superoperators

Complete positivity means positivity after tensoring with the identity on every
finite-dimensional auxiliary qudit. This is the defining amplification condition,
not an assumed Kraus characterization. Trace preservation is required on all operators.
Finite Kraus sums satisfy CP; the usual sum of adjoint squares suffices for TP.

The conventions follow Watrous, *The Theory of Quantum Information*, Section 2.2,
in particular Definition 2.13 and Theorems 2.22 and 2.26 (sufficiency directions).
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped ComplexOrder

namespace QuditCat.Superoperator

noncomputable section

variable {H K L M : QuditCat}

/-- Positivity of a superoperator: positive operators have positive images. -/
def IsPositive (Φ : Superoperator H K) : Prop :=
  ∀ A, A.IsPositive → (Φ A).IsPositive

/-- Complete positivity on every finite-dimensional auxiliary quantum system. -/
def IsCompletelyPositive (Φ : Superoperator H K) : Prop :=
  ∀ (R : QuditCat), (tensor Φ (LinearMap.id : Superoperator R R)).IsPositive

/-- Preservation of the complex trace on all operators, not only density inputs. -/
def IsTracePreserving (Φ : Superoperator H K) : Prop :=
  ∀ A, (Φ A).trace = A.trace

/-- Complete positivity implies positivity without an auxiliary system. -/
lemma IsCompletelyPositive.isPositive {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) : Φ.IsPositive := by
  intro A hA
  let ρ := Density.pure (UnitState.ofBasis (ZBasis 1) 0)
  have h := (hΦ (std 1) (Operator.tensor A ρ.op)
    (hA.tensorProduct ρ.positive)).partialTraceRight
  rw [tensor_apply, LinearMap.id_apply] at h
  change (Operator.partialTraceRight (Operator.tensor (Φ A) ρ.op)).IsPositive at h
  simpa only [Operator.partialTraceRight_tensor, ρ.trace_one, one_smul] using h

/-- Identity maps are completely positive. -/
lemma isCompletelyPositive_id (H : QuditCat) :
    IsCompletelyPositive (LinearMap.id : Superoperator H H) := by
  intro R A hA
  rw [tensor_id_id]
  exact hA

/-- Composition preserves complete positivity. -/
lemma IsCompletelyPositive.comp {Φ : Superoperator H K} {Ψ : Superoperator K L}
    (hΨ : Ψ.IsCompletelyPositive) (hΦ : Φ.IsCompletelyPositive) :
    IsCompletelyPositive (Ψ ∘ₗ Φ) := by
  intro R A hA
  have heq := tensor_comp Φ (LinearMap.id : Superoperator R R) Ψ LinearMap.id
  rw [LinearMap.id_comp] at heq
  rw [heq, LinearMap.comp_apply]
  exact hΨ R _ (hΦ R A hA)

/-- Arbitrary linear processes induce completely positive conjugations. -/
lemma isCompletelyPositive_conjugate (f : H.state →ₗ[ℂ] K.state) :
    (conjugate f).IsCompletelyPositive := by
  intro R A hA
  rw [← conjugate_id R, ← conjugate_tensor]
  exact hA.conj_adjoint _

/-- An isometric relabeling is completely positive. -/
lemma isCompletelyPositive_relabel (e : H.state ≃ₗᵢ[ℂ] K.state) :
    (relabel e).IsCompletelyPositive := by
  rw [relabel_eq_conjugate]
  exact isCompletelyPositive_conjugate _

/-- Appending an identity factor preserves complete positivity. -/
lemma IsCompletelyPositive.tensor_id {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) (L : QuditCat) :
    (tensor Φ (LinearMap.id : Superoperator L L)).IsCompletelyPositive := by
  intro R A hA
  rw [tensor_id_assoc, LinearMap.comp_apply, LinearMap.comp_apply]
  exact isPositive_relabel _ (hΦ (L ⊗ R) _ (isPositive_relabel _ hA))

/-- Prepending an identity factor preserves complete positivity. -/
lemma IsCompletelyPositive.id_tensor {Φ : Superoperator H K}
    (hΦ : Φ.IsCompletelyPositive) (L : QuditCat) :
    (tensor (LinearMap.id : Superoperator L L) Φ).IsCompletelyPositive := by
  rw [id_tensor_eq_comm]
  exact (isCompletelyPositive_relabel _).comp
    ((hΦ.tensor_id L).comp (isCompletelyPositive_relabel _))

/-- Tensor products of arbitrary completely positive maps are completely positive. -/
lemma IsCompletelyPositive.tensor {Φ : Superoperator H K} {Ψ : Superoperator L M}
    (hΦ : Φ.IsCompletelyPositive) (hΨ : Ψ.IsCompletelyPositive) :
    (tensor Φ Ψ).IsCompletelyPositive := by
  have heq := tensor_comp Φ (LinearMap.id : Superoperator L L)
    (LinearMap.id : Superoperator K K) Ψ
  rw [LinearMap.id_comp, LinearMap.comp_id] at heq
  rw [heq]
  exact (hΨ.id_tensor K).comp (hΦ.tensor_id L)

/-- Finite sums preserve complete positivity without imposing trace normalization. -/
lemma IsCompletelyPositive.sum {ι : Type*} (s : Finset ι)
    (Φ : ι → Superoperator H K) (hΦ : ∀ i ∈ s, (Φ i).IsCompletelyPositive) :
    (∑ i ∈ s, Φ i).IsCompletelyPositive := by
  intro R A hA
  rw [tensor_sum_left, LinearMap.sum_apply]
  exact LinearMap.isPositive_sum _ fun i hi => hΦ i hi R A hA

/-- The finite Kraus superoperator associated with a family of linear processes. -/
def kraus {ι : Type*} [Fintype ι] (f : ι → H.state →ₗ[ℂ] K.state) :
    Superoperator H K := ∑ i, conjugate (f i)

/-- A Kraus map acts by a sum of unnormalized conjugations. -/
lemma kraus_apply {ι : Type*} [Fintype ι] (f : ι → H.state →ₗ[ℂ] K.state)
    (A : Operator H) : kraus f A = ∑ i, f i ∘ₗ A ∘ₗ (f i).adjoint :=
  LinearMap.sum_apply _ _ _

/-- Every finite Kraus family defines a completely positive map. -/
lemma isCompletelyPositive_kraus {ι : Type*} [Fintype ι]
    (f : ι → H.state →ₗ[ℂ] K.state) : (kraus f).IsCompletelyPositive :=
  IsCompletelyPositive.sum _ _ fun i _ => isCompletelyPositive_conjugate (f i)

/-- The identity map preserves trace. -/
lemma isTracePreserving_id (H : QuditCat) :
    IsTracePreserving (LinearMap.id : Superoperator H H) := fun _ => rfl

/-- Composition preserves trace preservation. -/
lemma IsTracePreserving.comp {Φ : Superoperator H K} {Ψ : Superoperator K L}
    (hΨ : Ψ.IsTracePreserving) (hΦ : Φ.IsTracePreserving) :
    IsTracePreserving (Ψ ∘ₗ Φ) := fun A => (hΨ (Φ A)).trans (hΦ A)

/-- Product superoperators preserve trace when both factors do. -/
lemma IsTracePreserving.tensor {Φ : Superoperator H K} {Ψ : Superoperator L M}
    (hΦ : Φ.IsTracePreserving) (hΨ : Ψ.IsTracePreserving) :
    (tensor Φ Ψ).IsTracePreserving := by
  have heq : LinearMap.trace ℂ (K ⊗ M).state ∘ₗ Superoperator.tensor Φ Ψ =
      LinearMap.trace ℂ (H ⊗ L).state := by
    apply Operator.tensor_ext
    intro A B
    change Operator.trace (Superoperator.tensor Φ Ψ (Operator.tensor A B)) =
      Operator.trace (Operator.tensor A B)
    rw [tensor_apply, Operator.trace_tensor, Operator.trace_tensor, hΦ, hΨ]
  exact fun A => congrArg (fun f => f A) heq

/-- The trace of a Kraus map is paired with the sum of its adjoint squares. -/
lemma trace_kraus {ι : Type*} [Fintype ι] (f : ι → H.state →ₗ[ℂ] K.state)
    (A : Operator H) :
    (kraus f A).trace = Operator.trace ((∑ i, (f i).adjoint ∘ₗ f i) * A) := by
  rw [kraus_apply, Operator.trace, map_sum]
  simp only [Finset.sum_mul, Operator.trace, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  exact LinearMap.trace_mul_comm ℂ A _

/-- The usual Kraus completeness identity suffices for trace preservation. -/
lemma isTracePreserving_kraus {ι : Type*} [Fintype ι]
    (f : ι → H.state →ₗ[ℂ] K.state) (hf : ∑ i, (f i).adjoint ∘ₗ f i = 1) :
    (kraus f).IsTracePreserving := by
  intro A
  rw [trace_kraus, hf, one_mul]

/-- A finite Kraus map is trace preserving exactly when its adjoint squares sum to one. -/
lemma isTracePreserving_kraus_iff {ι : Type*} [Fintype ι]
    (f : ι → H.state →ₗ[ℂ] K.state) :
    (kraus f).IsTracePreserving ↔ ∑ i, (f i).adjoint ∘ₗ f i = 1 := by
  refine ⟨fun h => ?_, isTracePreserving_kraus f⟩
  ext x
  apply ext_inner_left ℂ
  intro y
  have hxy := h (Operator.outer x y)
  rw [trace_kraus, Operator.trace_mul_outer, Operator.trace_outer] at hxy
  exact hxy

/-- An isometric process induces a trace-preserving conjugation. -/
lemma isTracePreserving_conjugate (f : H.state →ₗ[ℂ] K.state)
    (hf : f.adjoint ∘ₗ f = LinearMap.id) : (conjugate f).IsTracePreserving := by
  intro A
  change LinearMap.trace ℂ K.state (f ∘ₗ A ∘ₗ f.adjoint) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, hf, LinearMap.comp_id]

/-- Right partial trace is a finite Kraus sum of basis contractions. -/
lemma partialTraceRight_eq_kraus {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K.state) :
    (Operator.partialTraceRight : Superoperator (H ⊗ K) H) =
      kraus (fun i => ((TensorProduct.mk ℂ H.state K.state).flip (b i)).adjoint) := by
  ext A x
  simp [Operator.partialTraceRight, LinearMap.partialTraceRight_eq b,
    LinearMap.partialTraceRightWith, kraus_apply]

/-- Discarding the right subsystem is completely positive. -/
lemma isCompletelyPositive_partialTraceRight (H K : QuditCat) :
    IsCompletelyPositive (Operator.partialTraceRight : Superoperator (H ⊗ K) H) := by
  rw [partialTraceRight_eq_kraus (stdOrthonormalBasis ℂ K.state)]
  exact isCompletelyPositive_kraus _

/-- Discarding the left subsystem is completely positive. -/
lemma isCompletelyPositive_partialTraceLeft (H K : QuditCat) :
    IsCompletelyPositive (Operator.partialTraceLeft : Superoperator (H ⊗ K) K) := by
  change IsCompletelyPositive
    ((Operator.partialTraceRight : Superoperator (K ⊗ H) K) ∘ₗ
      relabel (H := H ⊗ K) (K := K ⊗ H) (TensorProduct.commIsometry ℂ H.state K.state))
  exact (isCompletelyPositive_partialTraceRight K H).comp
    (isCompletelyPositive_relabel (H := H ⊗ K) (K := K ⊗ H)
      (TensorProduct.commIsometry ℂ H.state K.state))

end

end QuditCat.Superoperator
