/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Frobenius and classical structures

These are structures on an explicit object, not canonical instances on every object.
The monoid and comonoid data reuse Mathlib's `MonObj` and `ComonObj`.
The two Frobenius equations include the extended law of Lemma 5.4 of
*Categorical Quantum Mechanics: An Introduction* (2019). A classical structure is
special and commutative, as in Definition 5.10. No choice of basis occurs in the definition.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory DaggerCategory MonoidalDaggerCategory

variable {C : Type u} [Category.{v} C]

section Monoidal

variable [MonoidalCategory C]

/-- A monoid and comonoid satisfying both Frobenius equations. -/
structure FrobeniusObj (X : C) extends MonObj X, ComonObj X where
  /-- The left Frobenius equation. -/
  frobenius_left : (comul ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ mul) = mul ≫ comul
  /-- The right Frobenius equation. -/
  frobenius_right : (X ◁ comul) ≫ (α_ X X X).inv ≫ (mul ▷ X) = mul ≫ comul

/-- The original Frobenius law (equation (5.1)): the two mixed composites agree. -/
lemma FrobeniusObj.frobenius {X : C} (A : FrobeniusObj X) :
    (A.comul ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ A.mul) =
      (X ◁ A.comul) ≫ (α_ X X X).inv ≫ (A.mul ▷ X) :=
  A.frobenius_left.trans A.frobenius_right.symm

/-- Speciality: splitting and then merging is the identity. -/
def FrobeniusObj.IsSpecial {X : C} (A : FrobeniusObj X) : Prop :=
  A.comul ≫ A.mul = 𝟙 X

/-- The cup induced by the unit and comultiplication. -/
def FrobeniusObj.cup {X : C} (A : FrobeniusObj X) : 𝟙_ C ⟶ X ⊗ X :=
  A.one ≫ A.comul

/-- The cap induced by multiplication and the counit. -/
def FrobeniusObj.cap {X : C} (A : FrobeniusObj X) : X ⊗ X ⟶ 𝟙_ C :=
  A.mul ≫ A.counit

end Monoidal

variable [MonoidalDaggerCategory C]

/-- Taking daggers turns a comonoid into a monoid. The choice remains explicit. -/
@[instance_reducible]
def ComonObj.dagger {X : C} (A : ComonObj X) : MonObj X where
  one := A.counit†
  mul := A.comul†
  one_mul := by
    simpa only [dagger_comp, dagger_whiskerRight, IsUnitary.dagger_inv_eq_hom]
      using congrArg (fun f => f†) A.counit_comul
  mul_one := by
    simpa only [dagger_comp, dagger_whiskerLeft, IsUnitary.dagger_inv_eq_hom]
      using congrArg (fun f => f†) A.comul_counit
  mul_assoc := by
    have h := congrArg (fun f => f†) A.comul_assoc
    simpa only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight,
      IsUnitary.dagger_hom_eq_inv, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      using congrArg (fun f => (α_ X X X).hom ≫ f) h.symm

/-- A Frobenius structure whose comonoid maps are the daggers of its monoid maps. -/
structure DaggerFrobeniusObj (X : C) extends FrobeniusObj X where
  /-- Multiplication and comultiplication are adjoint. -/
  dagger_mul : mul† = comul
  /-- Unit and counit are adjoint. -/
  dagger_one : one† = counit

namespace DaggerFrobeniusObj

variable {X : C} (A : DaggerFrobeniusObj X)

/-- The cap is the dagger of the induced cup. -/
@[simp]
lemma dagger_cup : A.cup† = A.cap := by
  have h : A.comul† = A.mul := by rw [← A.dagger_mul, involutive_dagger]
  simp [FrobeniusObj.cup, FrobeniusObj.cap, h, A.dagger_one]

/-- The elementary two-input, two-output spider is self-adjoint. -/
instance isSelfAdjoint_mul_comul : DaggerCategory.IsSelfAdjoint (A.mul ≫ A.comul) := by
  rw [← A.dagger_mul]
  infer_instance

lemma dagger_mul_comul : (A.mul ≫ A.comul)† = A.mul ≫ A.comul :=
  IsSelfAdjoint.dagger_eq _

end DaggerFrobeniusObj

variable [BraidedCategory C]

/-- A special commutative dagger Frobenius structure (Definition 5.10).
Both commutativity equations are explicit, so no unitary-braiding hypothesis is hidden. -/
structure ClassicalStructure (X : C) extends DaggerFrobeniusObj X where
  /-- Splitting followed by merging is the identity. -/
  special : comul ≫ mul = 𝟙 X
  /-- The monoid is commutative. -/
  mul_comm : (β_ X X).hom ≫ mul = mul
  /-- The comonoid is commutative. -/
  comul_comm : comul ≫ (β_ X X).hom = comul

namespace ClassicalStructure

variable {X : C} (A : ClassicalStructure X)

/-- Speciality in the unbundled predicate. -/
lemma isSpecial : A.toFrobeniusObj.IsSpecial := A.special

/-- Two elementary spiders joined by two wires fuse to one spider. -/
lemma mul_comul_idempotent : (A.mul ≫ A.comul) ≫ (A.mul ≫ A.comul) =
    A.mul ≫ A.comul := by
  simp only [Category.assoc, ← Category.assoc A.comul A.mul A.comul, A.special,
    Category.id_comp]

/-- The merge-then-split spider is an orthogonal projection. -/
lemma isProj_mul_comul : IsProj (A.mul ≫ A.comul) :=
  ⟨A.mul_comul_idempotent, A.toDaggerFrobeniusObj.dagger_mul_comul⟩

/-- Copying is an isometry in every classical structure. -/
lemma isIsometry_comul : IsIsometry A.comul := by
  refine ⟨?_⟩
  have h : A.comul† = A.mul := by rw [← A.dagger_mul, involutive_dagger]
  rw [h]
  exact A.special

end ClassicalStructure

end CategoryTheory
