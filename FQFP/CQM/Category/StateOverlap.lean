/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
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

/-- A branch that tests against `v` and prepares `u` returns the matrix coefficient of
the input times the outer square of `u`. This is the single-outcome form of the
measurement followed by preparation in §0.3.5, with arbitrary preparations. -/
lemma conjugate_by_outerHom (u : State Y) (v : State X) (A : X ⟶ X) :
    (u.outerHom v)† ≫ A ≫ u.outerHom v = overlap v (v ≫ A) • u.outerHom u := by
  rw [State.dagger_outerHom, State.outerHom, State.outerHom, State.outerHom, ← comp_scalar_smul,
    ← scalar_asHom_comp]
  simp only [overlap, Category.assoc]

/-- The Born scalar for a state tested against another state's dagger (§2.4.1). -/
lemma probability_dagger (a b : State X) :
    probability a b† = overlap a b * overlap b a := by
  apply End.ext
  simp [overlap, End.mul_asHom]

/-- Reading back the dagger preparation of a disjoint effect gives the Kronecker
delta of the labels, as in equation (0.41). -/
lemma probability_of_disjoint [Semiadditive C] {ι : Type*} [DecidableEq ι]
    {e : ι → Effect X} (h : Effect.Disjoint e) (i j : ι) :
    probability (e i)† (e j) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst j
    apply End.ext
    simp only [involutive_dagger, ← Category.assoc, h.1, Category.id_comp, End.one_asHom]
  · apply End.ext
    change (e i)† ≫ e j ≫ (e j)† ≫ (e i)†† = 0
    simp only [← Category.assoc, h.2 (Ne.symm hij), Limits.zero_comp]

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
