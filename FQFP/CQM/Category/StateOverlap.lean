/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.Copying
public import FQFP.CategoryTheory.Monoidal.Dagger.Basic
public import FQFP.CategoryTheory.Monoidal.Measurement
public import Mathlib.Algebra.Group.Idempotent

/-!
# State overlaps, probabilities and copying

In a monoidal dagger category an isometry preserves state overlaps and a tensor
product multiplies them. For two states copied by the same isometry this forces
the overlap to be idempotent. Taking the two states equal gives the scalar
calculation in Lemma 5.35 of *Categorical Quantum Mechanics*.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory MonoidalDaggerCategory

namespace CQM

variable {C : Type*} [Category* C] {X Y : C}

section

variable [MonoidalCategory C] [DaggerCategory C]

/-- The scalar obtained by preparing `b` and applying the effect adjoint to `a`. -/
def overlap (a b : State X) : Scalar C := .of (b ≫ a†)

/-- The Born scalar for a state tested against another state's dagger (§2.4.1). -/
lemma probability_dagger (a b : State X) :
    probability a b† = overlap a b * overlap b a := by
  apply End.ext
  simp [overlap, End.mul_asHom]

/-- Applying the same isometry to both preparations preserves their overlap. -/
lemma overlap_comp_isometry (a b : State X) (f : X ⟶ Y) [IsIsometry f] :
    overlap (a ≫ f) (b ≫ f) = overlap a b := by
  apply End.ext
  simp [overlap]

end

variable [MonoidalDaggerCategory C]

/-- The overlap of independent preparations is the product of their overlaps. -/
lemma overlap_tensor (a b : State X) (c d : State Y) :
    overlap (a.tensor c) (b.tensor d) = overlap a b * overlap c d := by
  apply End.ext
  simp only [overlap, State.tensor, End.mul_asHom, dagger_comp,
    dagger_tensor, IsUnitary.dagger_inv_eq_hom, Category.assoc, tensorHom_comp_tensorHom_assoc]
  simp [tensorHom_def', unitors_equal, unitors_inv_equal]

/-- The overlap of any two states copied by the same isometry is idempotent. -/
theorem isIdempotentElem_overlap_of_isCopyable {d : X ⟶ X ⊗ X} [IsIsometry d]
    {a b : State X} (ha : a.IsCopyable d) (hb : b.IsCopyable d) :
    IsIdempotentElem (overlap a b) := by
  change overlap a b * overlap a b = overlap a b
  rw [← overlap_tensor, ← (show a ≫ d = _ from ha), ← (show b ≫ d = _ from hb),
    overlap_comp_isometry]

end CQM
