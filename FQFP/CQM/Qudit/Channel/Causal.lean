/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Environment
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-!
# The causal category of quantum channels

The arrows are exactly the existing `QuantumChannel` structures. The faithful inclusion
in `CPQudit` identifies them with causal CP processes. This category is symmetric
monoidal, but has no dagger instance: the adjoint of a TP map is unital, not generally TP.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit

/-- A quantum system in the category of deterministic (CPTP) processes. -/
structure CausalQudit where
  /-- The underlying Hilbert space. -/
  toQudit : Qudit

namespace CausalQudit

noncomputable section

instance : Category CausalQudit where
  Hom H K := QuantumChannel H.toQudit K.toQudit
  id H := QuantumChannel.id H.toQudit
  comp f g := g.comp f
  id_comp f := f.comp_id
  comp_id f := f.id_comp
  assoc f g h := (QuantumChannel.comp_assoc h g f).symm

/-- Include a channel as a general CP process. -/
def inclusion : CausalQudit ⥤ CPQudit where
  obj H := ⟨H.toQudit⟩
  map f := ⟨f.toSuperoperator, f.completelyPositive⟩

instance : inclusion.Faithful where
  map_injective h := QuantumChannel.ext (congrArg CPMap.toSuperoperator h)

/-- Every included channel is causal. -/
lemma isCausal_inclusion {H K : CausalQudit} (f : H ⟶ K) :
    CPQudit.IsCausal (inclusion.map f) :=
  (CPQudit.isCausal_iff _).mpr f.tracePreserving

/-- Channels are precisely the causal arrows of the CP category. -/
def homEquiv (H K : CausalQudit) :
    (H ⟶ K) ≃ {f : inclusion.obj H ⟶ inclusion.obj K // CPQudit.IsCausal f} where
  toFun f := ⟨inclusion.map f, isCausal_inclusion f⟩
  invFun f := ⟨f.1.toSuperoperator, f.1.completelyPositive, (CPQudit.isCausal_iff _).mp f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A unitary pure process gives an invertible deterministic process. -/
def unitaryIso {H K : Qudit} (f : H ⟶ K) [IsUnitary f] :
    (⟨H⟩ : CausalQudit) ≅ ⟨K⟩ where
  hom := QuantumChannel.ofIsometry f
  inv := QuantumChannel.ofIsometry f†
  hom_inv_id := by
    apply QuantumChannel.ext
    change Superoperator.conjugate f†.hom ∘ₗ Superoperator.conjugate f.hom = LinearMap.id
    rw [← Superoperator.conjugate_comp, ← Qudit.hom_comp, IsIsometry.comp_dagger_eq_id]
    exact Superoperator.conjugate_id H
  inv_hom_id := by
    apply QuantumChannel.ext
    change Superoperator.conjugate f.hom ∘ₗ Superoperator.conjugate f†.hom = LinearMap.id
    rw [← Superoperator.conjugate_comp, ← Qudit.hom_comp, IsUnitary.dagger_comp_eq_id]
    exact Superoperator.conjugate_id K

instance : MonoidalCategoryStruct CausalQudit where
  tensorObj H K := ⟨H.toQudit ⊗ K.toQudit⟩
  tensorUnit := ⟨𝟙_ Qudit⟩
  tensorHom f g := f.tensor g
  whiskerLeft H _ _ f := (QuantumChannel.id H.toQudit).tensor f
  whiskerRight f H := f.tensor (QuantumChannel.id H.toQudit)
  associator H K L := unitaryIso (α_ H.toQudit K.toQudit L.toQudit).hom
  leftUnitor H := unitaryIso (λ_ H.toQudit).hom
  rightUnitor H := unitaryIso (ρ_ H.toQudit).hom

instance : MonoidalCategory CausalQudit := Monoidal.induced inclusion
  { μIso := fun _ _ => Iso.refl _
    εIso := Iso.refl _
    whiskerLeft_eq := by intros; dsimp +instances [inclusion]; simp; rfl
    whiskerRight_eq := by intros; dsimp +instances [inclusion]; simp; rfl
    tensorHom_eq := by intros; dsimp +instances [inclusion]; simp; rfl
    associator_eq := by
      intros
      dsimp [inclusion]
      simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight, Category.id_comp,
        Iso.inv_hom_id, Category.comp_id, Category.assoc]
      apply CPMap.ext
      simp only [← tensorHom_id, CPQudit.hom_comp, CPQudit.hom_id,
        CPQudit.hom_tensor, Superoperator.tensor_id_id, LinearMap.comp_id]
      rfl
    leftUnitor_eq := by
      intros
      dsimp [inclusion]
      simp only [tensorHom_id, Category.assoc]
      apply CPMap.ext
      simp only [← tensorHom_id, CPQudit.hom_comp, CPQudit.hom_id,
        CPQudit.hom_tensor, Superoperator.tensor_id_id, LinearMap.comp_id]
      rfl
    rightUnitor_eq := by
      intros
      dsimp [inclusion]
      simp only [id_tensorHom, Category.assoc]
      apply CPMap.ext
      simp only [← id_tensorHom, CPQudit.hom_comp, CPQudit.hom_id,
        CPQudit.hom_tensor, Superoperator.tensor_id_id, LinearMap.comp_id]
      rfl }

instance : inclusion.Monoidal := Functor.CoreMonoidal.toMonoidal
  { εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by intros; dsimp +instances [inclusion]; simp; rfl
    μIso_hom_natural_right := by intros; dsimp +instances [inclusion]; simp; rfl
    associativity := by intros; dsimp +instances [inclusion]; simp; rfl
    left_unitality := by intros; dsimp +instances [inclusion]; simp; rfl
    right_unitality := by intros; dsimp +instances [inclusion]; simp; rfl }

instance : BraidedCategory CausalQudit :=
  BraidedCategory.ofFaithful inclusion
    (fun H K => unitaryIso (β_ H.toQudit K.toQudit).hom) (by
      intros
      dsimp [Functor.LaxMonoidal.μ, Functor.CoreMonoidal.toMonoidal,
        Functor.CoreMonoidal.toLaxMonoidal, inclusion]
      simp
      rfl)

instance : inclusion.Braided where
  braided H K := by
    dsimp [Functor.LaxMonoidal.μ, Functor.CoreMonoidal.toMonoidal,
      Functor.CoreMonoidal.toLaxMonoidal, inclusion, BraidedCategory.ofFaithful]
    simp
    rfl

instance : SymmetricCategory CausalQudit := SymmetricCategory.ofFaithful inclusion

/-- Discarding, now regarded as a deterministic process. -/
def discard (H : CausalQudit) : H ⟶ 𝟙_ CausalQudit :=
  ⟨Superoperator.discard H.toQudit, Superoperator.isCompletelyPositive_discard H.toQudit,
    Superoperator.isTracePreserving_discard H.toQudit⟩

/-- There is a unique deterministic effect: discarding. -/
lemma eq_discard {H : CausalQudit} (f : H ⟶ 𝟙_ CausalQudit) : f = discard H := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  change f.toSuperoperator A = A.trace • 1
  calc
    f.toSuperoperator A = (f.toSuperoperator A).trace • 1 := by
      rw [Operator.trace_scalar, ← Operator.scalar_eq]
    _ = _ := by rw [f.tracePreserving]

end

end CausalQudit

end Qudit
