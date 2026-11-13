/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CategoryTheory.Monoidal.Frobenius
public import FQFP.CQM.Qudit.Rigid
public import FQFP.CQM.Qudit.Measurement.POVM

/-!
# Classical structures from orthonormal bases

The construction direction of Theorem 5.36 of the 2019 CQM notes: copy and delete
an arbitrary finite orthonormal basis. Multiplication and unit are their daggers.
The basis remains explicit, including in dimension zero; no classification or
bijection of indexed bases is asserted.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

variable {H : Qudit} {ι : Type*} [Fintype ι]

/-- Copy the chosen orthonormal basis, extending linearly to all vectors. -/
def basisCopy (b : OrthonormalBasis ι ℂ H.state) : H ⟶ H ⊗ H :=
  ofHom (b.toBasis.constr ℂ fun i => b i ⊗ₜ[ℂ] b i)

/-- Delete each chosen basis vector by sending it to `1`. -/
def basisDelete (b : OrthonormalBasis ι ℂ H.state) : H ⟶ 𝟙_ Qudit :=
  ofHom (b.toBasis.constr ℂ fun _ => (1 : ℂ))

/-- Copying acts diagonally on basis vectors. -/
@[simp]
lemma basisCopy_basis (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    basisCopy b (b i) = b i ⊗ₜ[ℂ] b i := b.toBasis.constr_basis ℂ _ i

/-- Deleting a basis vector gives the unit scalar. -/
@[simp]
lemma basisDelete_basis (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    basisDelete b (b i) = (1 : ℂ) := b.toBasis.constr_basis ℂ _ i

open Classical in
/-- The adjoint of copying merges equal labels and annihilates distinct labels. -/
@[simp]
lemma adjoint_basisCopy_basis (b : OrthonormalBasis ι ℂ H.state) (i j : ι) :
    (basisCopy b).hom.adjoint (b i ⊗ₜ[ℂ] b j) = if i = j then b i else 0 := by
  classical
  apply InnerProductSpace.ext_inner_left_basis b.toBasis
  intro k
  change inner ℂ (b k) ((basisCopy b).hom.adjoint (b i ⊗ₜ[ℂ] b j)) = _
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (basisCopy b (b k)) (b i ⊗ₜ[ℂ] b j) = _
  rw [basisCopy_basis, TensorProduct.inner_tmul]
  by_cases hj : i = j
  · subst j; simp [b.inner_eq_ite]
  · by_cases hi : k = i <;> simp [b.inner_eq_ite, hi, hj]

open Classical in
/-- The categorical dagger version of `adjoint_basisCopy_basis`. The adjoint version is
registered for `simp`, since `hom_dagger` exposes the underlying linear map first. -/
lemma dagger_basisCopy_basis (b : OrthonormalBasis ι ℂ H.state) (i j : ι) :
    (basisCopy b)† (b i ⊗ₜ[ℂ] b j) = if i = j then b i else 0 :=
  adjoint_basisCopy_basis b i j

/-- The adjoint of deleting creates the sum of the basis vectors. -/
lemma dagger_basisDelete_apply (b : OrthonormalBasis ι ℂ H.state) (c : ℂ) :
    (basisDelete b)† c = c • ∑ i, b i := by
  apply InnerProductSpace.ext_inner_left_basis b.toBasis
  intro i
  change inner ℂ (b i) ((basisDelete b).hom.adjoint c) = _
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (basisDelete b (b i)) c = _
  classical
  simp [inner_smul_right, inner_sum, b.inner_eq_ite]

/-- Copying and deleting form a comonoid. -/
@[instance_reducible]
def basisComonObj (b : OrthonormalBasis ι ℂ H.state) : ComonObj H where
  counit := basisDelete b
  comul := basisCopy b
  counit_comul := by
    apply hom_ext
    apply b.toBasis.ext
    intro i
    change (basisDelete b ▷ H) (basisCopy b (b i)) = (λ_ H).inv (b i)
    simp [leftUnitor_inv_apply]
  comul_counit := by
    apply hom_ext
    apply b.toBasis.ext
    intro i
    change (H ◁ basisDelete b) (basisCopy b (b i)) = (ρ_ H).inv (b i)
    simp [rightUnitor_inv_apply]
  comul_assoc := by
    apply hom_ext
    apply b.toBasis.ext
    intro i
    change (H ◁ basisCopy b) (basisCopy b (b i)) =
      (α_ H H H).hom ((basisCopy b ▷ H) (basisCopy b (b i)))
    simp

/-- The left Frobenius equation for basis copying. -/
lemma basisCopy_frobenius_left (b : OrthonormalBasis ι ℂ H.state) :
    (basisCopy b ▷ H) ≫ (α_ H H H).hom ≫ (H ◁ (basisCopy b)†) =
      (basisCopy b)† ≫ basisCopy b := by
  apply hom_ext
  apply (b.toBasis.tensorProduct b.toBasis).ext
  rintro ⟨i, j⟩
  rw [Module.Basis.tensorProduct_apply]
  change (H ◁ (basisCopy b)†) ((α_ H H H).hom
    ((basisCopy b ▷ H) (b i ⊗ₜ[ℂ] b j))) =
      basisCopy b ((basisCopy b)† (b i ⊗ₜ[ℂ] b j))
  rw [whiskerRight_apply, basisCopy_basis, associator_hom_apply]
  change b i ⊗ₜ[ℂ] ((basisCopy b)† (b i ⊗ₜ[ℂ] b j)) = _
  by_cases h : i = j
  · subst j
    rw [dagger_basisCopy_basis, ite_eq_left rfl, basisCopy_basis]
  · rw [dagger_basisCopy_basis, ite_eq_right h, TensorProduct.tmul_zero, map_zero]

/-- The right Frobenius equation for basis copying. -/
lemma basisCopy_frobenius_right (b : OrthonormalBasis ι ℂ H.state) :
    (H ◁ basisCopy b) ≫ (α_ H H H).inv ≫ ((basisCopy b)† ▷ H) =
      (basisCopy b)† ≫ basisCopy b := by
  apply hom_ext
  apply (b.toBasis.tensorProduct b.toBasis).ext
  rintro ⟨i, j⟩
  rw [Module.Basis.tensorProduct_apply]
  change ((basisCopy b)† ▷ H) ((α_ H H H).inv
    ((H ◁ basisCopy b) (b i ⊗ₜ[ℂ] b j))) =
      basisCopy b ((basisCopy b)† (b i ⊗ₜ[ℂ] b j))
  rw [whiskerLeft_apply, basisCopy_basis, associator_inv_apply]
  change ((basisCopy b)† (b i ⊗ₜ[ℂ] b j)) ⊗ₜ[ℂ] b j = _
  by_cases h : i = j
  · subst j
    rw [dagger_basisCopy_basis, ite_eq_left rfl, basisCopy_basis]
  · rw [dagger_basisCopy_basis, ite_eq_right h, TensorProduct.zero_tmul, map_zero]

/-- Copying followed by its adjoint is the identity, including for the empty basis. -/
lemma basisCopy_special (b : OrthonormalBasis ι ℂ H.state) :
    basisCopy b ≫ (basisCopy b)† = 𝟙 H := by
  apply hom_ext
  apply b.toBasis.ext
  intro i
  change (basisCopy b)† (basisCopy b (b i)) = b i
  rw [basisCopy_basis, dagger_basisCopy_basis, ite_eq_left rfl]

/-- Copying is cocommutative. -/
lemma basisCopy_comm (b : OrthonormalBasis ι ℂ H.state) :
    basisCopy b ≫ (β_ H H).hom = basisCopy b := by
  apply hom_ext
  apply b.toBasis.ext
  intro i
  change (TensorProduct.comm ℂ H.state H.state) (basisCopy b (b i)) = basisCopy b (b i)
  simp

/-- Merging is commutative. -/
lemma dagger_basisCopy_comm (b : OrthonormalBasis ι ℂ H.state) :
    (β_ H H).hom ≫ (basisCopy b)† = (basisCopy b)† := by
  apply hom_ext
  apply (b.toBasis.tensorProduct b.toBasis).ext
  rintro ⟨i, j⟩
  rw [Module.Basis.tensorProduct_apply]
  change (basisCopy b)† (b j ⊗ₜ[ℂ] b i) = (basisCopy b)† (b i ⊗ₜ[ℂ] b j)
  by_cases h : i = j
  · subst j; rfl
  · rw [dagger_basisCopy_basis, dagger_basisCopy_basis, ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The classical structure associated with a finite orthonormal basis.
This is the construction direction of Theorem 5.36, with all structure laws proved. -/
def classicalStructureOfOrthonormalBasis (b : OrthonormalBasis ι ℂ H.state) :
    ClassicalStructure H where
  toMonObj := (basisComonObj b).dagger
  toComonObj := basisComonObj b
  frobenius_left := basisCopy_frobenius_left b
  frobenius_right := basisCopy_frobenius_right b
  dagger_mul := involutive_dagger _
  dagger_one := involutive_dagger _
  special := basisCopy_special b
  mul_comm := dagger_basisCopy_comm b
  comul_comm := basisCopy_comm b

/-- The induced cup is exactly the existing basis-dependent self-dual cup. -/
lemma classicalStructure_cup (b : OrthonormalBasis ι ℂ H.state) :
    (classicalStructureOfOrthonormalBasis b).cup = basisCoevaluation b := by
  apply hom_ext
  apply LinearMap.ext
  intro c
  change basisCopy b ((basisDelete b)† c) = _
  rw [dagger_basisDelete_apply, map_smul, map_sum]
  simp [basisCopy_basis]

/-- The induced cap is exactly the existing basis evaluation. -/
lemma classicalStructure_cap (b : OrthonormalBasis ι ℂ H.state) :
    (classicalStructureOfOrthonormalBasis b).cap = basisEvaluation b := by
  rw [← (classicalStructureOfOrthonormalBasis b).toDaggerFrobeniusObj.dagger_cup,
    classicalStructure_cup, dagger_basisCoevaluation]

/-- Reading one leg of copying yields the existing basis measurement projector. -/
lemma classicalStructure_measurement (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    (classicalStructureOfOrthonormalBasis b).comul ≫
      (H ◁ braArrow (b i)) ≫ (ρ_ H).hom = ofHom ((POVM.ofBasis b).op i) := by
  apply hom_ext
  apply b.toBasis.ext
  intro j
  change (ρ_ H).hom ((H ◁ braArrow (b i)) (basisCopy b (b j))) =
    (POVM.ofBasis b).op i (b j)
  rw [basisCopy_basis, whiskerLeft_apply, rightUnitor_hom_apply]
  change (inner ℂ (b i) (b j)) • b j = (inner ℂ (b i) (b j)) • b i
  by_cases h : i = j
  · subst j; rfl
  · rw [b.inner_eq_zero h, zero_smul, zero_smul]

open Classical in
/-- The classical two-input spider retains equal basis labels and rejects unequal labels. -/
lemma classicalStructure_mul_comul_basis (b : OrthonormalBasis ι ℂ H.state) (i j : ι) :
    ((classicalStructureOfOrthonormalBasis b).mul ≫
      (classicalStructureOfOrthonormalBasis b).comul) (b i ⊗ₜ[ℂ] b j) =
        if i = j then b i ⊗ₜ[ℂ] b i else 0 := by
  change basisCopy b ((basisCopy b)† (b i ⊗ₜ[ℂ] b j)) = _
  rw [dagger_basisCopy_basis]
  split_ifs <;> simp only [basisCopy_basis, map_zero]

/-- Repeating the equal-label filter has no further effect: a concrete spider-fusion client. -/
lemma classicalStructure_repeat_filter (b : OrthonormalBasis ι ℂ H.state) :
    let A := classicalStructureOfOrthonormalBasis b
    (A.mul ≫ A.comul) ≫ (A.mul ≫ A.comul) = A.mul ≫ A.comul :=
  (classicalStructureOfOrthonormalBasis b).mul_comul_idempotent

end

end Qudit
