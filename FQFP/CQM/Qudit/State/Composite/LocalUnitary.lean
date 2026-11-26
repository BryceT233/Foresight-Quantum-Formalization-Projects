/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Composite.SchmidtRank
public import FQFP.Analysis.InnerProductSpace.Orthonormal
import FQFP.Data.Fintype.Fibers

/-!
# Local unitary equivalence of pure states

The positive Schmidt coefficients are recorded as a multiset, retaining multiplicities.
Two unit vectors on the same bipartite system are locally unitarily equivalent exactly
when these multisets agree. Equality of vectors is exact, since a global phase can be
absorbed into either local unitary.

## Main definitions and results

* `Qudit.UnitState.schmidtCoefficients`: the multiset of positive Schmidt coefficients.
* `Qudit.UnitState.LocallyUnitaryEquivalent`: local unitary equivalence with exact vector equality.
* `Qudit.UnitState.locallyUnitaryEquivalent_iff_schmidtCoefficients_eq`: local unitary equivalence
  is characterized by the Schmidt coefficients.
* `Qudit.UnitState.schmidtRank_map_localUnitary`: local unitary invariance of Schmidt rank.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct

namespace Qudit.UnitState

noncomputable section

variable {H K : Qudit}

/-- The positive Schmidt coefficients, including repeated coefficients. -/
def schmidtCoefficients (ψ : UnitState (H ⊗ K)) : Multiset ℝ :=
  Finset.univ.val.map ψ.schmidtCoefficient

/-- Schmidt coefficients are square roots of the nonzero marginal eigenvalues. -/
lemma schmidtCoefficients_eq_map_sqrt (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtCoefficients =
      (Density.pure ψ).partialTraceRight.nonzeroEigenvalues.map Real.sqrt := by
  classical
  unfold schmidtCoefficients schmidtCoefficient
  rw [show (fun i : ψ.SchmidtIndex => Real.sqrt
    ((Density.pure ψ).partialTraceRight.eigenvalue i.val)) =
    Subtype.restrict (fun i => 0 < (Density.pure ψ).partialTraceRight.eigenvalue i)
      (fun i => Real.sqrt ((Density.pure ψ).partialTraceRight.eigenvalue i)) from rfl,
    Finset.univ_val_map_subtype_restrict]
  simp only [Density.nonzeroEigenvalues, Multiset.filter_map, Multiset.map_map,
    Function.comp_def]
  congr 1
  change (Finset.univ.filter _).val = (Finset.univ.filter _).val
  congr 1
  apply Finset.filter_congr
  intro i _
  exact (lt_iff_le_and_ne).trans (by
    simp [(Density.pure ψ).partialTraceRight.eigenvalue_nonneg i, ne_comm])

/-- The Schmidt coefficient multiset has cardinality the Schmidt rank. -/
lemma card_schmidtCoefficients (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtCoefficients.card = ψ.schmidtRank := by
  simp [schmidtCoefficients, schmidtRank]

/-- Squaring the Schmidt coefficients recovers the nonzero marginal eigenvalues. -/
lemma map_sq_schmidtCoefficients (ψ : UnitState (H ⊗ K)) :
    ψ.schmidtCoefficients.map (fun s => s ^ 2) =
      (Density.pure ψ).partialTraceRight.nonzeroEigenvalues := by
  classical
  rw [schmidtCoefficients_eq_map_sqrt, Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id (Density.pure ψ).partialTraceRight.nonzeroEigenvalues]
  apply Multiset.map_congr rfl
  intro r hr
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_filter.mp hr).1
  exact Real.sq_sqrt ((Density.pure ψ).partialTraceRight.eigenvalue_nonneg i)

/-- Equality of Schmidt coefficients is equivalent to equality of nonzero marginal spectra. -/
lemma schmidtCoefficients_eq_iff_nonzeroEigenvalues_eq (ψ φ : UnitState (H ⊗ K)) :
    ψ.schmidtCoefficients = φ.schmidtCoefficients ↔
      (Density.pure ψ).partialTraceRight.nonzeroEigenvalues =
        (Density.pure φ).partialTraceRight.nonzeroEigenvalues := by
  constructor
  · intro h
    rw [← map_sq_schmidtCoefficients, ← map_sq_schmidtCoefficients, h]
  · intro h
    rw [schmidtCoefficients_eq_map_sqrt, schmidtCoefficients_eq_map_sqrt, h]

/-- Local unitary evolution leaves the coefficient matrix unchanged in the transported bases. -/
lemma coefficientMatrix_map_localUnitary {H' K' : Qudit} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ψ : UnitState (H ⊗ K)) (f : H ⟶ H') (g : K ⟶ K') [IsUnitary f] [IsUnitary g]
    (b : OrthonormalBasis ι ℂ H.state) (c : OrthonormalBasis κ ℂ K.state) :
    (ψ.map (f ⊗ₘ g)).coefficientMatrix
      (b.map (LIEquivOfIsUnitary f)) (c.map (LIEquivOfIsUnitary g)) =
      ψ.coefficientMatrix b c := by
  ext i j
  simp only [coefficientMatrix, OrthonormalBasis.map_apply, LIEquivOfIsUnitary_apply, coe_map]
  rw [← tensorHom_tmul]
  exact inner_map_map_of_isIsometry (f ⊗ₘ g) _ _

/-- Local unitary evolution preserves the positive Schmidt coefficients with multiplicity. -/
lemma schmidtCoefficients_map_localUnitary {H' K' : Qudit} (ψ : UnitState (H ⊗ K))
    (f : H ⟶ H') (g : K ⟶ K') [IsUnitary f] [IsUnitary g] :
    (ψ.map (f ⊗ₘ g)).schmidtCoefficients = ψ.schmidtCoefficients := by
  classical
  rw [schmidtCoefficients_eq_map_sqrt, schmidtCoefficients_eq_map_sqrt]
  congr 1
  let b := stdOrthonormalBasis ℂ H.state
  let c := stdOrthonormalBasis ℂ K.state
  have hm : (Density.pure (ψ.map (f ⊗ₘ g))).partialTraceRight.toMatrix
      (b.map (LIEquivOfIsUnitary f)) = (Density.pure ψ).partialTraceRight.toMatrix b := by
    rw [Density.toMatrix_partialTraceRight_pure _ _ (c.map (LIEquivOfIsUnitary g)),
      coefficientMatrix_map_localUnitary, Density.toMatrix_partialTraceRight_pure ψ b c]
  have hp := congrArg Matrix.charpoly hm
  change (LinearMap.toMatrix (b.map (LIEquivOfIsUnitary f)).toBasis
    (b.map (LIEquivOfIsUnitary f)).toBasis _).charpoly =
    (LinearMap.toMatrix b.toBasis b.toBasis _).charpoly at hp
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix] at hp
  apply Multiset.map_injective Complex.ofReal_injective
  rw [← Density.roots_charpoly_filter_ne_zero, ← Density.roots_charpoly_filter_ne_zero, hp]

/-- Local unitary equivalence uses dagger-unitary morphisms and exact vector equality. -/
def LocallyUnitaryEquivalent (ψ φ : UnitState (H ⊗ K)) : Prop :=
  ∃ (f : H ⟶ H) (g : K ⟶ K) (_ : IsUnitary f) (_ : IsUnitary g),
    φ = ψ.map (f ⊗ₘ g)

/-- Equal Schmidt coefficient multisets construct local unitaries taking one vector to the other. -/
lemma locallyUnitaryEquivalent_of_schmidtCoefficients_eq
    (ψ φ : UnitState (H ⊗ K)) (h : ψ.schmidtCoefficients = φ.schmidtCoefficients) :
    ψ.LocallyUnitaryEquivalent φ := by
  classical
  obtain ⟨e, he⟩ := Fintype.exists_equiv_of_multiset_eq ψ.schmidtCoefficient φ.schmidtCoefficient h
  obtain ⟨U, hU⟩ := ψ.orthonormal_schmidtLeft.exists_linearIsometryEquiv
    (φ.orthonormal_schmidtLeft.comp e e.injective) rfl
  obtain ⟨V, hV⟩ := ψ.orthonormal_schmidtRight.exists_linearIsometryEquiv
    (φ.orthonormal_schmidtRight.comp e e.injective) rfl
  let f : H ⟶ H := (isoMk U.toLinearEquiv).hom
  let g : K ⟶ K := (isoMk V.toLinearEquiv).hom
  let : IsUnitary f := isUnitary_isoMk_coe_LIEquiv U
  let : IsUnitary g := isUnitary_isoMk_coe_LIEquiv V
  exact ⟨f, g, inferInstance, inferInstance, ψ.eq_map_of_schmidt φ f g e he hU hV⟩

/-- Two pure vectors on the same bipartite system are locally unitarily equivalent exactly
when their positive Schmidt coefficients agree, with multiplicity. -/
theorem locallyUnitaryEquivalent_iff_schmidtCoefficients_eq (ψ φ : UnitState (H ⊗ K)) :
    ψ.LocallyUnitaryEquivalent φ ↔ ψ.schmidtCoefficients = φ.schmidtCoefficients := by
  constructor
  · rintro ⟨f, g, hf, hg, rfl⟩
    exact (ψ.schmidtCoefficients_map_localUnitary f g).symm
  · exact ψ.locallyUnitaryEquivalent_of_schmidtCoefficients_eq φ

/-- Local unitary equivalence is reflexive. -/
lemma LocallyUnitaryEquivalent.refl (ψ : UnitState (H ⊗ K)) :
    ψ.LocallyUnitaryEquivalent ψ :=
  (locallyUnitaryEquivalent_iff_schmidtCoefficients_eq _ _).mpr rfl

/-- Local unitary equivalence is symmetric. -/
lemma LocallyUnitaryEquivalent.symm {ψ φ : UnitState (H ⊗ K)}
    (h : ψ.LocallyUnitaryEquivalent φ) : φ.LocallyUnitaryEquivalent ψ := by
  rw [locallyUnitaryEquivalent_iff_schmidtCoefficients_eq] at h ⊢
  exact h.symm

/-- Local unitary equivalence is transitive. -/
lemma LocallyUnitaryEquivalent.trans {ψ φ χ : UnitState (H ⊗ K)}
    (h₁ : ψ.LocallyUnitaryEquivalent φ) (h₂ : φ.LocallyUnitaryEquivalent χ) :
    ψ.LocallyUnitaryEquivalent χ := by
  rw [locallyUnitaryEquivalent_iff_schmidtCoefficients_eq] at h₁ h₂ ⊢
  exact h₁.trans h₂

/-- Global phase leaves the Schmidt coefficient multiset unchanged. -/
lemma schmidtCoefficients_phase (ψ : UnitState (H ⊗ K)) (c : ℂ) (hc : ‖c‖ = 1) :
    (ψ.phase c hc).schmidtCoefficients = ψ.schmidtCoefficients := by
  rw [schmidtCoefficients_eq_map_sqrt, Density.pure_phase, ← schmidtCoefficients_eq_map_sqrt]

/-- Schmidt rank is invariant under local unitary evolution, also between isomorphic systems. -/
lemma schmidtRank_map_localUnitary {H' K' : Qudit} (ψ : UnitState (H ⊗ K))
    (f : H ⟶ H') (g : K ⟶ K') [IsUnitary f] [IsUnitary g] :
    (ψ.map (f ⊗ₘ g)).schmidtRank = ψ.schmidtRank := by
  rw [← card_schmidtCoefficients, schmidtCoefficients_map_localUnitary, card_schmidtCoefficients]

/-- Locally unitarily equivalent pure states have equal Schmidt ranks. -/
lemma LocallyUnitaryEquivalent.schmidtRank_eq {ψ φ : UnitState (H ⊗ K)}
    (h : ψ.LocallyUnitaryEquivalent φ) : ψ.schmidtRank = φ.schmidtRank := by
  rw [← card_schmidtCoefficients, ← card_schmidtCoefficients,
    (locallyUnitaryEquivalent_iff_schmidtCoefficients_eq _ _).mp h]

end

end Qudit.UnitState
