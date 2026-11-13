/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Choi

/-!
# The category of completely positive quantum processes

Objects retain the underlying Hilbert space; arrows are completely positive maps on
its full operator algebra. Trace preservation is not part of this category. The pure
process functor sends `f` to conjugation by `f`, and therefore forgets global phase.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit

namespace Superoperator

/-- Tensoring distributes over a finite sum in its second argument. -/
lemma tensor_sum_right {H K L M : Qudit} {ι : Type*} (s : Finset ι)
    (Φ : Superoperator H K) (Ψ : ι → Superoperator L M) :
    tensor Φ (∑ i ∈ s, Ψ i) = ∑ i ∈ s, tensor Φ (Ψ i) := by
  apply Operator.tensor_ext
  intro A B
  simp only [tensor_apply, LinearMap.sum_apply]
  simp only [Operator.tensor, ← TensorProduct.mapBilinear_apply, map_sum]

end Superoperator

/-- A completely positive process, with no normalization constraint. -/
@[ext]
structure CPMap (H K : Qudit) where
  /-- Action on all operators. -/
  toSuperoperator : Superoperator H K
  /-- Positivity after every finite-dimensional amplification. -/
  completelyPositive : toSuperoperator.IsCompletelyPositive

/-- Forget trace preservation while retaining the underlying CP process. -/
def QuantumChannel.toCPMap {H K : Qudit} (f : QuantumChannel H K) : CPMap H K :=
  ⟨f.toSuperoperator, f.completelyPositive⟩

/-- A Hilbert space regarded as a full matrix algebra in the CP process category. -/
structure CPQudit where
  /-- The underlying pure quantum system. -/
  toQudit : Qudit

namespace CPQudit

noncomputable section

instance : Category CPQudit where
  Hom H K := CPMap H.toQudit K.toQudit
  id H := ⟨LinearMap.id, Superoperator.isCompletelyPositive_id H.toQudit⟩
  comp f g := ⟨g.toSuperoperator ∘ₗ f.toSuperoperator,
    g.completelyPositive.comp f.completelyPositive⟩
  id_comp _ := CPMap.ext (LinearMap.comp_id _)
  comp_id _ := CPMap.ext (LinearMap.id_comp _)
  assoc _ _ _ := CPMap.ext (LinearMap.comp_assoc _ _ _)

/-- Extensionality on the underlying superoperator. -/
@[ext]
lemma hom_ext {H K : CPQudit} {f g : H ⟶ K}
    (h : f.toSuperoperator = g.toSuperoperator) : f = g := CPMap.ext h

/-- The identity process acts identically on operators. -/
@[simp]
lemma hom_id (H : CPQudit) : (𝟙 H : H ⟶ H).toSuperoperator = LinearMap.id := rfl

/-- Categorical composition applies the first process before the second. -/
@[simp]
lemma hom_comp {H K L : CPQudit} (f : H ⟶ K) (g : K ⟶ L) :
    (f ≫ g).toSuperoperator = g.toSuperoperator ∘ₗ f.toSuperoperator := rfl

/-- Pure processes act by conjugation. This functor is not asserted to be faithful. -/
def pure : Qudit ⥤ CPQudit where
  obj H := ⟨H⟩
  map f := ⟨Superoperator.conjugate f.hom, Superoperator.isCompletelyPositive_conjugate _⟩
  map_id H := hom_ext (Superoperator.conjugate_id H)
  map_comp f g := hom_ext (Superoperator.conjugate_comp f.hom g.hom)

/-- Independent parallel composition of CP processes. -/
def tensor {H K L M : CPQudit} (f : H ⟶ K) (g : L ⟶ M) :
    CPMap (H.toQudit ⊗ L.toQudit) (K.toQudit ⊗ M.toQudit) :=
  ⟨Superoperator.tensor f.toSuperoperator g.toSuperoperator,
    f.completelyPositive.tensor g.completelyPositive⟩

instance : MonoidalCategoryStruct CPQudit where
  tensorObj H K := ⟨H.toQudit ⊗ K.toQudit⟩
  tensorUnit := ⟨𝟙_ Qudit⟩
  tensorHom f g := tensor f g
  whiskerLeft H _ _ f := tensor (𝟙 H) f
  whiskerRight f H := tensor f (𝟙 H)
  associator H K L := pure.mapIso (α_ H.toQudit K.toQudit L.toQudit)
  leftUnitor H := pure.mapIso (λ_ H.toQudit)
  rightUnitor H := pure.mapIso (ρ_ H.toQudit)

/-- The tensor of processes acts by the existing superoperator tensor. -/
@[simp]
lemma hom_tensor {H K L M : CPQudit} (f : H ⟶ K) (g : L ⟶ M) :
    (f ⊗ₘ g).toSuperoperator = Superoperator.tensor f.toSuperoperator g.toSuperoperator := rfl

/-- The pure functor preserves tensor products on the nose. -/
@[simp]
lemma pure_tensor {H K L M : Qudit} (f : H ⟶ K) (g : L ⟶ M) :
    pure.map (f ⊗ₘ g) = pure.map f ⊗ₘ pure.map g := by
  apply hom_ext
  exact (congrArg Superoperator.conjugate (Qudit.hom_tensorHom f g)).trans
    (Superoperator.conjugate_tensor f.hom g.hom)

/-- Reassociation is the CP image of pure reassociation. -/
@[simp]
lemma hom_associator (H K L : CPQudit) :
    (α_ H K L).hom.toSuperoperator =
      Superoperator.conjugate (α_ H.toQudit K.toQudit L.toQudit).hom.hom := rfl

/-- The left unit constraint is the CP image of the pure constraint. -/
@[simp]
lemma hom_leftUnitor (H : CPQudit) :
    (λ_ H).hom.toSuperoperator = Superoperator.conjugate (λ_ H.toQudit).hom.hom := rfl

/-- The right unit constraint is the CP image of the pure constraint. -/
@[simp]
lemma hom_rightUnitor (H : CPQudit) :
    (ρ_ H).hom.toSuperoperator = Superoperator.conjugate (ρ_ H.toQudit).hom.hom := rfl

/-- Naturality of reassociation for arbitrary CP processes. -/
lemma assoc_natural {H K L H' K' L' : CPQudit}
    (f : H ⟶ H') (g : K ⟶ K') (h : L ⟶ L') :
    ((f ⊗ₘ g) ⊗ₘ h) ≫ (α_ H' K' L').hom =
      (α_ H K L).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
  apply hom_ext
  obtain ⟨n, a, ha⟩ := f.completelyPositive.exists_kraus
  obtain ⟨m, b, hb⟩ := g.completelyPositive.exists_kraus
  obtain ⟨k, c, hc⟩ := h.completelyPositive.exists_kraus
  apply LinearMap.ext
  intro A
  simp only [hom_comp, hom_tensor, ha, hb, hc, Superoperator.kraus,
    Superoperator.tensor_sum_left, Superoperator.tensor_sum_right,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have e := congrArg (fun f => (pure.map f).toSuperoperator A)
    (associator_naturality (ofHom (a l) : H.toQudit ⟶ H'.toQudit)
      (ofHom (b j) : K.toQudit ⟶ K'.toQudit) (ofHom (c i) : L.toQudit ⟶ L'.toQudit))
  simp only [pure.map_comp, pure_tensor] at e
  dsimp only [pure, tensor] at e
  convert e using 1 <;> rfl

/-- Naturality of the left unit for arbitrary CP processes. -/
lemma left_natural {H K : CPQudit} (f : H ⟶ K) :
    (𝟙 (𝟙_ CPQudit) ⊗ₘ f) ≫ (λ_ K).hom = (λ_ H).hom ≫ f := by
  apply hom_ext
  obtain ⟨n, a, ha⟩ := f.completelyPositive.exists_kraus
  apply LinearMap.ext
  intro A
  simp only [hom_comp, hom_tensor, ha, Superoperator.kraus,
    Superoperator.tensor_sum_right, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have e := congrArg (fun f => (pure.map f).toSuperoperator A)
    (leftUnitor_naturality (ofHom (a i) : H.toQudit ⟶ K.toQudit))
  simp only [← id_tensorHom, pure.map_comp, pure_tensor, pure.map_id] at e
  dsimp only [pure, tensor] at e
  convert e using 1 <;> rfl

/-- Naturality of the right unit for arbitrary CP processes. -/
lemma right_natural {H K : CPQudit} (f : H ⟶ K) :
    (f ⊗ₘ 𝟙 (𝟙_ CPQudit)) ≫ (ρ_ K).hom = (ρ_ H).hom ≫ f := by
  apply hom_ext
  obtain ⟨n, a, ha⟩ := f.completelyPositive.exists_kraus
  apply LinearMap.ext
  intro A
  simp only [hom_comp, hom_tensor, ha, Superoperator.kraus,
    Superoperator.tensor_sum_left, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have e := congrArg (fun f => (pure.map f).toSuperoperator A)
    (rightUnitor_naturality (ofHom (a i) : H.toQudit ⟶ K.toQudit))
  simp only [← tensorHom_id, pure.map_comp, pure_tensor, pure.map_id] at e
  dsimp only [pure, tensor] at e
  convert e using 1 <;> rfl

instance : MonoidalCategory CPQudit := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun H K => hom_ext (Superoperator.tensor_id_id H.toQudit K.toQudit))
  (id_tensorHom := fun _ {_ _} _ => rfl)
  (tensorHom_id := fun _ _ => rfl)
  (tensorHom_comp_tensorHom := fun f g f' g' =>
    hom_ext (Superoperator.tensor_comp _ _ _ _).symm)
  (associator_naturality := assoc_natural)
  (leftUnitor_naturality := left_natural)
  (rightUnitor_naturality := right_natural)
  (pentagon := fun W X Y Z => by
    have e := congrArg pure.map (pentagon W.toQudit X.toQudit Y.toQudit Z.toQudit)
    simp only [← tensorHom_id, ← id_tensorHom, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1 <;> rfl)
  (triangle := fun X Y => by
    have e := congrArg pure.map (triangle X.toQudit Y.toQudit)
    simp only [← tensorHom_id, ← id_tensorHom, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1; rfl)

/-- Swapping systems is natural for arbitrary CP processes. -/
lemma swap_natural {H K L M : CPQudit} (f : H ⟶ K) (g : L ⟶ M) :
    (f ⊗ₘ g) ≫ pure.map (β_ K.toQudit M.toQudit).hom =
      pure.map (β_ H.toQudit L.toQudit).hom ≫ (g ⊗ₘ f) := by
  apply hom_ext
  apply Operator.tensor_ext
  intro A B
  change Superoperator.conjugate (TensorProduct.commIsometry ℂ K.toQudit.state
      M.toQudit.state).toLinearMap (Superoperator.tensor f.toSuperoperator
        g.toSuperoperator (Operator.tensor A B)) =
    Superoperator.tensor g.toSuperoperator f.toSuperoperator
      (Superoperator.conjugate (TensorProduct.commIsometry ℂ H.toQudit.state
        L.toQudit.state).toLinearMap (Operator.tensor A B))
  rw [← Superoperator.relabel_eq_conjugate, ← Superoperator.relabel_eq_conjugate,
    Superoperator.tensor_apply, Superoperator.relabel_comm_tensor,
    Superoperator.relabel_comm_tensor, Superoperator.tensor_apply]

instance : BraidedCategory CPQudit where
  braiding H K := pure.mapIso (β_ H.toQudit K.toQudit)
  braiding_naturality_left f H := swap_natural f (𝟙 H)
  braiding_naturality_right H _ _ f := swap_natural (𝟙 H) f
  hexagon_forward H K L := by
    have e := congrArg pure.map (BraidedCategory.hexagon_forward H.toQudit K.toQudit L.toQudit)
    simp only [← tensorHom_id, ← id_tensorHom, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1 <;> rfl
  hexagon_reverse H K L := by
    have e := congrArg pure.map (BraidedCategory.hexagon_reverse H.toQudit K.toQudit L.toQudit)
    simp only [← tensorHom_id, ← id_tensorHom, pure.map_comp, pure_tensor, pure.map_id] at e
    convert e using 1 <;> rfl

instance : SymmetricCategory CPQudit where
  symmetry H K := by
    have e := congrArg pure.map (SymmetricCategory.symmetry H.toQudit K.toQudit)
    simp only [pure.map_comp, pure.map_id] at e
    exact e

instance : pure.Monoidal := Functor.CoreMonoidal.toMonoidal
  { εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := fun f Y => by
      dsimp only [pure]
      dsimp only [Iso.refl_hom]
      rw [Category.comp_id, Category.id_comp]
      apply hom_ext
      change Superoperator.tensor (Superoperator.conjugate f.hom) LinearMap.id =
        Superoperator.conjugate (TensorProduct.map f.hom (LinearMap.id : Y.state →ₗ[ℂ] Y.state))
      rw [Superoperator.conjugate_tensor, Superoperator.conjugate_id]
    μIso_hom_natural_right := fun X f => by
      dsimp only [pure]
      dsimp only [Iso.refl_hom]
      rw [Category.comp_id, Category.id_comp]
      apply hom_ext
      change Superoperator.tensor LinearMap.id (Superoperator.conjugate f.hom) =
        Superoperator.conjugate (TensorProduct.map (LinearMap.id : X.state →ₗ[ℂ] X.state) f.hom)
      rw [Superoperator.conjugate_tensor, Superoperator.conjugate_id]
    associativity := fun _ _ _ => by
      dsimp only [pure]
      dsimp only [Iso.refl_hom]
      rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.id_comp,
        Category.comp_id, Category.comp_id]
      rfl
    left_unitality := fun _ => by
      dsimp only [pure]
      dsimp only [Iso.refl_hom]
      rw [id_whiskerRight, Category.id_comp, Category.id_comp]
      rfl
    right_unitality := fun _ => by
      dsimp only [pure]
      dsimp only [Iso.refl_hom]
      rw [whiskerLeft_id, Category.id_comp, Category.id_comp]
      rfl }
end

end CPQudit

end Qudit
