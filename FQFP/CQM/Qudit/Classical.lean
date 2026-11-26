/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Rigid
public import FQFP.CQM.Qudit.Measurement.POVM

/-!
# Measurement from a basis classical structure

Reading one output of basis copying gives the corresponding measurement projector.
The merge-then-split spider filters equal labels, and repeating the filter is idempotent.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit

noncomputable section

variable {H : Qudit} {ι : Type*} [Fintype ι]

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
