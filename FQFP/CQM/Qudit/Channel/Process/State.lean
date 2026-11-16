/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Causal
public import FQFP.CQM.Qudit.Channel.Process.Dual
public import FQFP.CategoryTheory.Monoidal.State

/-!
# Positive operators and categorical preparations

Positive operators are states of `CPQudit`; density operators are states of `CausalQudit`.
The preparation associated to `A` sends a scalar operator `B` to `Tr(B) • A`.
These equivalences preserve sequential action and parallel preparation, including in
dimension zero. They do not identify non-product mixed states with entangled states.

## Main definitions and results

* `Qudit.CPQudit.stateEquiv`: positive operators correspond to categorical CP preparations.
* `Qudit.Density.toState`: a normalized state in the causal channel category.
* `Qudit.Density.causalCPStateEquiv`: densities correspond to causal CP preparations.
* `Qudit.Density.toCPState_comp`: sequential composition agrees with channel evolution.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped ComplexOrder BigOperators

namespace Qudit

noncomputable section

namespace Superoperator

variable {H : Qudit}

/-- A map out of the scalar operator space is determined by its value at one. -/
lemma ext_unit {Φ Ψ : Superoperator (𝟙_ Qudit) H} (h : Φ 1 = Ψ 1) : Φ = Ψ := by
  apply LinearMap.ext
  intro B
  rw [Operator.scalar_eq B, map_smul, map_smul, h]

/-- Preparation of an operator, without positivity or normalization assumptions. -/
def prepare (A : Operator H) : Superoperator (𝟙_ Qudit) H :=
  (LinearMap.toSpanSingleton ℂ (Operator H) A) ∘ₗ LinearMap.trace ℂ ℂ

/-- Preparation scales its output by the input scalar. -/
lemma prepare_apply (A : Operator H) (B : Operator (𝟙_ Qudit)) :
    prepare A B = B.trace • A := rfl

/-- The prepared operator is the value at one. -/
@[simp]
lemma prepare_one (A : Operator H) : prepare A 1 = A := by
  rw [prepare_apply, Operator.trace_scalar]
  exact one_smul ℂ A

/-- Every linear map out of the scalar system is a preparation. -/
lemma prepare_apply_one (Φ : Superoperator (𝟙_ Qudit) H) : prepare (Φ 1) = Φ :=
  ext_unit (prepare_one _)

/-- A pure ket prepares its outer square. -/
lemma conjugate_ket (v : H.state) : conjugate (ket v) = prepare (Operator.outer v v) := by
  apply ext_unit
  rw [prepare_one, conjugate_apply]
  simp only [ket, LinearMap.adjoint_toSpanSingleton]
  rfl

/-- Positivity of an operator is sufficient for completely positive preparation. -/
lemma isCompletelyPositive_prepare {A : Operator H} (hA : A.IsPositive) :
    (prepare A).IsCompletelyPositive := by
  obtain ⟨v, hv⟩ := Operator.exists_sum_outer_of_isPositive A hA
  have h : prepare A = kraus (fun i => ket (v i)) := by
    apply ext_unit
    simp only [prepare_one, kraus, LinearMap.sum_apply, conjugate_ket]
    simpa only [prepare_one] using hv
  rw [h]
  exact isCompletelyPositive_kraus _

/-- Unitary conjugation preserves the identity operator. -/
lemma conjugate_unitary_one {K : Qudit} (f : H ⟶ K) [IsUnitary f] :
    conjugate f.hom 1 = 1 := by
  change f.hom ∘ₗ LinearMap.id ∘ₗ f.hom.adjoint = LinearMap.id
  rw [LinearMap.id_comp, ← hom_dagger, ← hom_comp, IsUnitary.dagger_comp_eq_id]
  rfl

/-- Parallel preparation agrees with the operator tensor after inserting the unit. -/
lemma tensor_prepare {K : Qudit} (A : Operator H) (B : Operator K) :
    tensor (prepare A) (prepare B) ∘ₗ conjugate (λ_ (𝟙_ Qudit)).inv.hom =
      prepare (Operator.tensor A B) := by
  apply ext_unit
  rw [LinearMap.comp_apply, ← IsUnitary.dagger_hom_eq_inv, conjugate_unitary_one]
  have h : (1 : Operator ((𝟙_ Qudit) ⊗ (𝟙_ Qudit))) = Operator.tensor 1 1 :=
    TensorProduct.map_one.symm
  rw [h, tensor_apply, prepare_one, prepare_one, prepare_one]

end Superoperator

namespace CPQudit

/-- The CP state associated to an unnormalized positive operator. -/
def ofPositive {H : Qudit} (A : Operator H) (hA : A.IsPositive) :
    𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit) :=
  ⟨Superoperator.prepare A, Superoperator.isCompletelyPositive_prepare hA⟩

/-- The underlying action of a positive preparation. -/
lemma ofPositive_apply {H : Qudit} (A : Operator H) (hA : A.IsPositive)
    (B : Operator (𝟙_ Qudit)) : (ofPositive A hA).toSuperoperator B = B.trace • A := rfl

/-- A CP state is determined by the positive operator it prepares. -/
@[ext]
lemma state_ext {H : CPQudit} {f g : 𝟙_ CPQudit ⟶ H}
    (h : f.toSuperoperator 1 = g.toSuperoperator 1) : f = g :=
  hom_ext (Superoperator.ext_unit h)

/-- Positive operators are exactly the states of the CP process category. -/
def stateEquiv (H : Qudit) :
    {A : Operator H // A.IsPositive} ≃ (𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit)) where
  toFun A := ofPositive A.1 A.2
  invFun f := ⟨f.toSuperoperator 1, f.completelyPositive.isPositive 1 LinearMap.isPositive_one⟩
  left_inv A := Subtype.ext (Superoperator.prepare_one A.1)
  right_inv _ := state_ext (Superoperator.prepare_one _)

/-- Pure preparations agree with the pure-process functor. -/
lemma ofPositive_outer {H : Qudit} (v : H.state) :
    ofPositive (Operator.outer v v) (Operator.isPositive_outer v) = pure.map (ketArrow v) :=
  hom_ext (Superoperator.conjugate_ket v).symm

end CPQudit

namespace Density

variable {H K : Qudit}

/-- A density operator as a deterministic preparation. -/
def toState (ρ : Density H) : 𝟙_ CausalQudit ⟶ (⟨H⟩ : CausalQudit) where
  toSuperoperator := Superoperator.prepare ρ.op
  completelyPositive := Superoperator.isCompletelyPositive_prepare ρ.positive
  tracePreserving B := by
    rw [Superoperator.prepare_apply, Operator.trace, map_smul]
    change B.trace * ρ.op.trace = B.trace
    rw [ρ.trace_one, mul_one]

/-- A density operator as a CP preparation, forgetting trace preservation. -/
def toCPState (ρ : Density H) : 𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit) :=
  CausalQudit.inclusion.map ρ.toState

/-- Inclusion of deterministic preparations gives their CP interpretation. -/
@[simp]
lemma inclusion_toState (ρ : Density H) :
    CausalQudit.inclusion.map ρ.toState = ρ.toCPState := rfl

/-- The deterministic preparation returns the input trace times the density operator. -/
lemma toState_apply (ρ : Density H) (B : Operator (𝟙_ Qudit)) :
    ρ.toState.toSuperoperator B = B.trace • ρ.op := rfl

/-- The CP preparation returns the input trace times the density operator. -/
lemma toCPState_apply (ρ : Density H) (B : Operator (𝟙_ Qudit)) :
    ρ.toCPState.toSuperoperator B = B.trace • ρ.op := rfl

/-- Evaluation of a deterministic preparation at one. -/
@[simp]
lemma toState_one (ρ : Density H) : ρ.toState.toSuperoperator 1 = ρ.op :=
  Superoperator.prepare_one _

/-- Evaluation of a CP preparation at one. -/
@[simp]
lemma toCPState_one (ρ : Density H) : ρ.toCPState.toSuperoperator 1 = ρ.op :=
  Superoperator.prepare_one _

/-- Density operators are exactly the deterministic states, with no dimension assumption. -/
def causalStateEquiv (H : Qudit) :
    Density H ≃ (𝟙_ CausalQudit ⟶ (⟨H⟩ : CausalQudit)) where
  toFun := toState
  invFun f := ⟨f.toSuperoperator 1,
    f.completelyPositive.isPositive 1 LinearMap.isPositive_one,
    (f.tracePreserving 1).trans (by rw [Operator.trace_scalar]; rfl)⟩
  left_inv ρ := Density.ext (toState_one ρ)
  right_inv f := QuantumChannel.ext (Superoperator.ext_unit (toState_one _))

/-- Density operators are exactly the causal states inside the CP category. -/
def causalCPStateEquiv (H : Qudit) :
    Density H ≃ {f : 𝟙_ CPQudit ⟶ (⟨H⟩ : CPQudit) // CPQudit.IsCausal f} :=
  (causalStateEquiv H).trans (CausalQudit.homEquiv (𝟙_ CausalQudit) ⟨H⟩)

/-- Density preparations satisfy the categorical normalization equation. -/
lemma isCausal_toCPState (ρ : Density H) : CPQudit.IsCausal ρ.toCPState :=
  CausalQudit.isCausal_inclusion ρ.toState

/-- Deterministic state preparation is injective. -/
lemma toState_injective : Function.Injective (toState (H := H)) :=
  (causalStateEquiv H).injective

/-- Pure density preparation is the CP image of its ket. -/
lemma toCPState_pure (v : UnitState H) :
    (pure v).toCPState = CPQudit.pure.map (ketArrow v.val) :=
  CPQudit.ofPositive_outer v.val

/-- Sequential preparation and evolution agrees with the existing channel action. -/
@[simp]
lemma toState_comp (ρ : Density H) (Φ : QuantumChannel H K) :
    ρ.toState ≫ Φ = (Φ.map ρ).toState := by
  apply QuantumChannel.ext
  apply Superoperator.ext_unit
  change Φ.toSuperoperator (ρ.toState.toSuperoperator 1) =
    (Φ.map ρ).toState.toSuperoperator 1
  rw [toState_one, toState_one]
  rfl

/-- The same sequential compatibility after forgetting causality. -/
@[simp]
lemma toCPState_comp (ρ : Density H) (Φ : QuantumChannel H K) :
    ρ.toCPState ≫ Φ.toCPMap = (Φ.map ρ).toCPState := by
  apply CPQudit.state_ext
  change Φ.toSuperoperator (ρ.toCPState.toSuperoperator 1) =
    (Φ.map ρ).toCPState.toSuperoperator 1
  rw [toCPState_one, toCPState_one]
  rfl

/-- Independent deterministic preparations give the existing tensor density. -/
lemma toState_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).toState =
      (λ_ (𝟙_ CausalQudit)).inv ≫ (ρ.toState ⊗ₘ σ.toState) := by
  apply QuantumChannel.ext
  change Superoperator.prepare (Operator.tensor ρ.op σ.op) =
    Superoperator.tensor (Superoperator.prepare ρ.op) (Superoperator.prepare σ.op) ∘ₗ
      Superoperator.conjugate (λ_ (𝟙_ Qudit)).hom†.hom
  rw [IsUnitary.dagger_hom_eq_inv]
  exact (Superoperator.tensor_prepare ρ.op σ.op).symm

/-- Independent CP preparations give the existing tensor density. -/
lemma toCPState_tensor (ρ : Density H) (σ : Density K) :
    (ρ.tensor σ).toCPState =
      (λ_ (𝟙_ CPQudit)).inv ≫ (ρ.toCPState ⊗ₘ σ.toCPState) :=
  CPQudit.hom_ext (Superoperator.tensor_prepare ρ.op σ.op).symm

end Density

end

end Qudit
