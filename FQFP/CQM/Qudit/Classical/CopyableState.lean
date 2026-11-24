/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Classical
import Mathlib.Algebra.GroupWithZero.Idempotent

/-!
# Copyable vectors of a classical structure

Lemma 5.35 of *Categorical Quantum Mechanics* gives unit norm for a nonzero
copyable vector. For the classical structure constructed from an orthonormal
basis, we recover the basis as its nonzero copyable vectors (§5.4.2).
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit

variable {H : Qudit}

/-- Copyability of a ket can be checked on the underlying vector. -/
theorem isCopyable_ketArrow_iff (v : H.state) (d : H ⟶ H ⊗ H) :
    State.IsCopyable (ketArrow v) d ↔ d v = v ⊗ₜ[ℂ] v := by
  have eval : ((ketArrow v) ≫ d).hom 1 = d v := by
    change d ((1 : ℂ) • v) = d v
    rw [one_smul]
  have prod : (State.tensor (ketArrow v) (ketArrow v)).hom (1 : ℂ) = v ⊗ₜ[ℂ] v := by
    change ((1 : ℂ) • v) ⊗ₜ[ℂ] ((1 : ℂ) • v) = _
    rw [one_smul]
  rw [← eval, ← prod]
  exact ⟨fun h => congrArg (fun f : 𝟙_ Qudit ⟶ H ⊗ H => f.hom (1 : ℂ)) h,
    fun h => hom_ext (LinearMap.ext_ring h)⟩

/-- Two vectors copied by the same isometry have inner product zero or one. -/
theorem inner_eq_zero_or_one_of_isCopyable {d : H ⟶ H ⊗ H} [IsIsometry d]
    {v w : H.state} (hv : State.IsCopyable (ketArrow v) d)
    (hw : State.IsCopyable (ketArrow w) d) : inner ℂ v w = 0 ∨ inner ℂ v w = 1 := by
  simpa only [scalarRingEquiv_overlap] using
    ((CQM.isIdempotentElem_overlap_of_isCopyable hv hw).map scalarRingEquiv).eq_zero_or_one

/-- Every nonzero vector copied by an isometry has unit norm (Lemma 5.35). -/
theorem norm_eq_one_of_isCopyable {d : H ⟶ H ⊗ H} [IsIsometry d] {v : H.state}
    (hv : State.IsCopyable (ketArrow v) d) (hne : v ≠ 0) : ‖v‖ = 1 := by
  have h := (inner_eq_zero_or_one_of_isCopyable hv hv).resolve_left (inner_self_ne_zero.mpr hne)
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), h, RCLike.one_re, Real.sqrt_one]

/-- Distinct kets copied by one isometry are orthogonal. -/
theorem eq_or_inner_eq_zero_of_isCopyable {d : H ⟶ H ⊗ H} [IsIsometry d]
    {v w : H.state} (hv : State.IsCopyable (ketArrow v) d)
    (hw : State.IsCopyable (ketArrow w) d) : v = w ∨ inner ℂ v w = 0 := by
  rcases inner_eq_zero_or_one_of_isCopyable hv hw with h | h
  · exact Or.inr h
  have hv' : v ≠ 0 := by rintro rfl; simp at h
  have hw' : w ≠ 0 := by rintro rfl; simp at h
  have hdist := norm_sub_sq (𝕜 := ℂ) v w
  rw [norm_eq_one_of_isCopyable hv hv', norm_eq_one_of_isCopyable hw hw', h] at hdist
  norm_num at hdist
  exact Or.inl (sub_eq_zero.mp hdist)

/-- The copying map of an orthonormal basis copies precisely zero and the basis vectors. -/
theorem isCopyable_basisCopy_iff {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state)
    (v : H.state) : State.IsCopyable (ketArrow v) (basisCopy b) ↔ v = 0 ∨ ∃ i, v = b i := by
  have hb (i : ι) := (isCopyable_ketArrow_iff (b i) (basisCopy b)).2 (basisCopy_basis b i)
  constructor
  · intro hv
    by_cases hz : v = 0
    · exact Or.inl hz
    let : IsIsometry (basisCopy b) := (classicalStructureOfOrthonormalBasis b).isIsometry_comul
    obtain ⟨i, hi⟩ : ∃ i, inner ℂ (b i) v ≠ 0 := by
      by_contra! h
      exact hz (by simpa [h] using (b.sum_repr' v).symm)
    exact Or.inr ⟨i, ((eq_or_inner_eq_zero_of_isCopyable (hb i) hv).resolve_right hi).symm⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · simp [isCopyable_ketArrow_iff]
    · exact hb i

end Qudit
