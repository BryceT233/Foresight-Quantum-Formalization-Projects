/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Dagger.OrthogonalResolution
public import FQFP.CQM.Category.StateOverlap

/-!
# Finite projective measurements

An orthogonal resolution models a projection-valued measure (Definition 0.61).
Disjoint amplitude effects resolving the identity give rank-one measurements in
finite-dimensional Hilbert spaces (the forward construction in Lemma 0.62).
-/

@[expose] public section

open CategoryTheory DaggerCategory MonoidalCategory Limits

namespace CQM

variable {C : Type*} [Category* C] [MonoidalCategory C] [DaggerCategory C] [Semiadditive C]
  {X : C} {ι : Type*} [Fintype ι]

/-- Form the projection for each outcome by measuring its amplitude and preparing
the corresponding dagger state. -/
def projectiveMeasurementOfEffects (x : ι → Effect X) (hd : Effect.Disjoint x)
    (hs : ∑ i, x i ≫ (x i)† = 𝟙 X) : OrthogonalResolution X ι where
  op i := .of (x i ≫ (x i)†)
  isStarProjection i := by
    let := hd.isIsometry_dagger x i
    simpa only [involutive_dagger] using End.isStarProjection_dagger_comp (x i)†
  orthogonal := by
    intro i j hij
    rw [Category.assoc, ← Category.assoc ((x i)†), hd.2 hij.symm, zero_comp, comp_zero]
  sum_proj := hs

/-- The Born weight of a projected state is the expectation of its projection
(Definition 0.63). -/
theorem overlap_comp_proj (P : OrthogonalResolution X ι) (a : State X) (i : ι) :
    overlap (a ≫ P.proj i) (a ≫ P.proj i) = .of (a ≫ P.proj i ≫ a†) := by
  apply End.ext
  have hi := P.isStarProjection i
  simp only [overlap, dagger_comp, hi.isSelfAdjoint.dagger_asHom, Category.assoc]
  rw [← Category.assoc (P.proj i), hi.isIdempotentElem.asHom_comp_self]

/-- The Born weights of a projective measurement sum to the squared norm of its input.
For an isometric state the right-hand side is the identity scalar (equation 0.37). -/
theorem sum_overlap_comp_proj (P : OrthogonalResolution X ι) (a : State X) :
    ∑ i, overlap (a ≫ P.proj i) (a ≫ P.proj i) = overlap a a := by
  simp only [overlap_comp_proj]
  apply End.ext
  rw [Semiadditive.end_sum_asHom]
  change ∑ i, (a ≫ P.proj i ≫ a†) = a ≫ a†
  rw [← Semiadditive.comp_sum, ← Semiadditive.sum_comp, P.sum_proj, Category.id_comp]

/-- An unread projective measurement preserves coherence between states in the
same outcome subspace and removes coherence between different outcomes.
This extends the basis decoherence formula (0.42) to arbitrary projection ranks. -/
theorem diagonalPart_outerHom [DecidableEq ι] (P : OrthogonalResolution X ι)
    {u v : State X} {i j : ι} (hu : u ≫ P.proj i = u) (hv : v ≫ P.proj j = v) :
    P.diagonalPart (u.outerHom v) = if i = j then u.outerHom v else 0 := by
  have h := State.dagger_comp_outerHom_comp u v (P.proj j) (P.proj i)
  rw [(P.isStarProjection j).isSelfAdjoint.dagger_asHom, hu, hv] at h
  simpa only [h, eq_comm] using P.diagonalPart_block j i (u.outerHom v)

end CQM
