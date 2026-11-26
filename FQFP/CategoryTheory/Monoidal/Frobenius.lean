/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

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

/-- A Frobenius structure makes its object self-dual (Theorem 5.15).
This pairing depends on the supplied structure. -/
@[instance_reducible]
def FrobeniusObj.exactPairing {X : C} (A : FrobeniusObj X) : ExactPairing X X where
  coevaluation' := A.cup
  evaluation' := A.cap
  coevaluation_evaluation' := by
    simp only [FrobeniusObj.cup, FrobeniusObj.cap, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc]
    rw [← Category.assoc (α_ X X X).inv, ← Category.assoc (X ◁ A.comul),
      A.frobenius_right, Category.assoc, A.counit_comul, ← Category.assoc, A.mul_one]
  evaluation_coevaluation' := by
    simp only [FrobeniusObj.cup, FrobeniusObj.cap, whiskerLeft_comp, comp_whiskerRight,
      Category.assoc]
    rw [← Category.assoc (α_ X X X).hom, ← Category.assoc (A.comul ▷ X),
      A.frobenius_left, Category.assoc, A.comul_counit, ← Category.assoc, A.one_mul]

end Monoidal

variable [MonoidalDaggerCategory C]

/-- For adjoint copying and merging, the two Frobenius equations are daggers of each other. -/
lemma frobenius_right_of_dagger_left {X : C} (d : X ⟶ X ⊗ X)
    (h : (d ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ d†) = d† ≫ d) :
    (X ◁ d) ≫ (α_ X X X).inv ≫ (d† ▷ X) = d† ≫ d := by
  simpa only [dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, involutive_dagger,
    IsUnitary.dagger_hom_eq_inv, Category.assoc] using congrArg dagger h

/-- With a unitary braiding, the dagger of cocommutative copying is commutative merging. -/
lemma braiding_comp_dagger_of_cocomm [BraidedCategory C] {X : C} [IsUnitary (β_ X X).hom]
    (d : X ⟶ X ⊗ X) (h : d ≫ (β_ X X).hom = d) : (β_ X X).hom ≫ d† = d† := by
  have hd := congrArg dagger h
  rw [dagger_comp, IsUnitary.dagger_hom_eq_inv] at hd
  exact ((β_ X X).inv_comp_eq.mp hd).symm
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
theorem isSelfAdjoint_mul_comul : IsSelfAdjoint (End.of (A.mul ≫ A.comul)) := by
  rw [← A.dagger_mul]
  exact (End.IsPositive.comp_dagger A.mul).isSelfAdjoint

lemma dagger_mul_comul : (A.mul ≫ A.comul)† = A.mul ≫ A.comul :=
  A.isSelfAdjoint_mul_comul.dagger_asHom

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
lemma isStarProjection_mul_comul : IsStarProjection (End.of (A.mul ≫ A.comul)) :=
  ⟨End.ext A.mul_comul_idempotent, A.toDaggerFrobeniusObj.isSelfAdjoint_mul_comul⟩

/-- Copying is an isometry in every classical structure. -/
lemma isIsometry_comul : IsIsometry A.comul := by
  refine ⟨?_⟩
  have h : A.comul† = A.mul := by rw [← A.dagger_mul, involutive_dagger]
  rw [h]
  exact A.special

end ClassicalStructure

end CategoryTheory
