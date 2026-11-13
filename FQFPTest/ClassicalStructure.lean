/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.Classical
import FQFP.CategoryTheory.Category.RelCat.Classical

/-!
# Classical structure clients

Exercise arbitrary bases, Mathlib monoid/comonoid interfaces, the measurement bridge,
spider fusion, empty objects, and the distinction between basis copying and nonlinear cloning.
-/

open CategoryTheory MonoidalCategory DaggerCategory Qudit
open scoped TensorProduct

noncomputable section

-- The construction works for a basis of any finite index type on an arbitrary qudit.
example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    ClassicalStructure H := classicalStructureOfOrthonormalBasis b

-- Exercise the dagger-to-adjoint simp normal form in a real basis calculation.
example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    (basisCopy b)† (b i ⊗ₜ[ℂ] b i) = b i := by simp

-- Reusing the actual Mathlib interfaces needs only local choices of structure.
example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    let := (classicalStructureOfOrthonormalBasis b).toMonObj
    (MonObj.mul ▷ H) ≫ MonObj.mul =
      (α_ H H H).hom ≫ (H ◁ MonObj.mul) ≫ MonObj.mul := by
  let := (classicalStructureOfOrthonormalBasis b).toMonObj
  exact MonObj.mul_assoc H

example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    let := (classicalStructureOfOrthonormalBasis b).toComonObj
    ComonObj.comul ≫ (ComonObj.counit ▷ H) = (λ_ H).inv := by
  let := (classicalStructureOfOrthonormalBasis b).toComonObj
  exact ComonObj.counit_comul H

-- The same structure recovers the previously implemented qutrit measurement projector.
example (i : Fin 3) :
    (classicalStructureOfOrthonormalBasis (ZBasis 3)).comul ≫
      (std 3 ◁ braArrow (ZBasis 3 i)) ≫ (ρ_ (std 3)).hom =
        ofHom ((POVM.computational 3).op i) :=
  classicalStructure_measurement (ZBasis 3) i

-- The cup really is the cup of the existing exact pairing, with its original normalization.
example {H : Qudit} {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) :
    (classicalStructureOfOrthonormalBasis b).cup =
      (exactPairingOfOrthonormalBasis b).coevaluation' := classicalStructure_cup b

-- Empty bases do not require a normalized state or a nonempty index type.
example : ClassicalStructure (std 0) := classicalStructureOfOrthonormalBasis (ZBasis 0)

example : (classicalStructureOfOrthonormalBasis (ZBasis 0)).cup = 0 := by
  rw [classicalStructure_cup]
  apply hom_ext
  apply LinearMap.ext
  intro c
  simp

-- The two-input spider is a genuine equality-label filter.
example :
    ((classicalStructureOfOrthonormalBasis (ZBasis 3)).mul ≫
      (classicalStructureOfOrthonormalBasis (ZBasis 3)).comul)
        (ZBasis 3 0 ⊗ₜ[ℂ] ZBasis 3 1) = 0 := by
  rw [classicalStructure_mul_comul_basis, ite_eq_right (by decide)]

example :
    let A := classicalStructureOfOrthonormalBasis (ZBasis 3)
    (A.mul ≫ A.comul) ≫ (A.mul ≫ A.comul) = A.mul ≫ A.comul :=
  classicalStructure_repeat_filter (ZBasis 3)

-- Copying is linear: a superposition gives a correlated sum, not a tensor square.
example : basisCopy (ZBasis 2) (ZBasis 2 0 + ZBasis 2 1) ≠
    (ZBasis 2 0 + ZBasis 2 1) ⊗ₜ[ℂ] (ZBasis 2 0 + ZBasis 2 1) := by
  intro h
  have h' := congrArg (inner ℂ (ZBasis 2 0 ⊗ₜ[ℂ] ZBasis 2 1)) h
  simp [map_add, basisCopy_basis, inner_add_right, TensorProduct.inner_tmul,
    (ZBasis 2).inner_eq_ite] at h'

-- Relational copying works on infinite and empty types too.
example : ClassicalStructure (C := RelCat) ℕ := RelCat.discreteClassicalStructure _

example : ClassicalStructure (C := RelCat) Empty := RelCat.discreteClassicalStructure _

example (X : RelCat) : (RelCat.discreteClassicalStructure X).cup = η_ X X :=
  RelCat.discreteClassicalStructure_cup X

-- Merging succeeds only when both labels agree.
example (x y z : ℕ) :
    ((x, y), z) ∈ (RelCat.discreteClassicalStructure (ℕ : RelCat)).mul.rel ↔
      z = x ∧ z = y := Iff.rfl

-- The abstract fusion theorem is shared by both models.
example (X : RelCat) :
    let A := RelCat.discreteClassicalStructure X
    (A.mul ≫ A.comul) ≫ (A.mul ≫ A.comul) = A.mul ≫ A.comul :=
  (RelCat.discreteClassicalStructure X).mul_comul_idempotent
