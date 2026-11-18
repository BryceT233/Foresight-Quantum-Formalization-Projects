/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Composite.Schmidt
public import FQFP.Analysis.InnerProductSpace.Orthonormal

/-!
# Purification of density operators

Every density operator admits a pure state on a larger system whose right partial trace
is the original density. The construction pairs its eigenvectors, weighted by square roots
of eigenvalues, with an orthonormal basis of an auxiliary system. Zero eigenvalues remain
allowed. The default auxiliary system is a second copy of the original qudit, with its
standard orthonormal basis; the chosen purification vector is not basis-independent.

This adapts physlib's `MState.purify`, `MState.purify_spec` and `MState.purifyX` to the
existing coordinate-free `UnitState`, `Density` and partial trace interfaces.

Any two purifications of the same density on equal-dimensional auxiliary systems are
related by a unitary on the auxiliary factor alone. Equality is of unit vectors, so the
unitary also absorbs global phase. No full-rank or nondegenerate-spectrum assumption is
needed: the common marginal fixes the left Schmidt vectors, and the matching right
Schmidt families extend to a unitary on the whole auxiliary space.
If the auxiliary dimensions differ, an isometry from the smaller auxiliary system to
the larger one relates the purifications. Isometries on the auxiliary factor preserve
the retained marginal, without any surjectivity assumption.

## Main definitions and results

* `Qudit.Density.purifyWith`: spectral purification in an explicit auxiliary orthonormal basis.
* `Qudit.Density.purify`: a spectral purification using a second copy of the system.
* `Qudit.Density.exists_unitary_of_purifications`: uniqueness at equal auxiliary dimensions.
* `Qudit.Density.exists_isometry_of_purifications`: uniqueness toward a larger auxiliary system.
-/

@[expose] public section

open CategoryTheory MonoidalCategory DaggerCategory
open scoped TensorProduct BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- The spectral purification sum has the original density as its unnormalized marginal. -/
lemma partialTraceRight_outer_spectral_sum (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    Operator.partialTraceRight
      (Operator.outer (∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i)
        (∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i)) = ρ.op := by
  rw [Operator.partialTraceRight_outer_sum_tmul, ρ.op_eq_sum_eigenvalue_smul_outer]
  apply Finset.sum_congr rfl
  intro i _
  rw [Operator.outer_smul_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow,
    Real.sq_sqrt (ρ.eigenvalue_nonneg i)]

/-- Purify a density operator using an explicit orthonormal basis for the auxiliary system. -/
def purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    UnitState (H ⊗ K) :=
  ⟨∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i, by
    have ht := (LinearMap.trace_partialTraceRight _).symm.trans
      (congrArg Operator.trace (ρ.partialTraceRight_outer_spectral_sum b))
    exact (Operator.trace_outer _ _).symm.trans (ht.trans ρ.trace_one)⟩

/-- The vector of an explicit-basis purification is its square-root-weighted spectral sum. -/
lemma coe_purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    (ρ.purifyWith b).val =
      ∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i := rfl

/-- Discarding the auxiliary system of an explicit-basis purification recovers the input. -/
lemma partialTraceRight_pure_purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    (pure (ρ.purifyWith b)).partialTraceRight = ρ := by
  apply Density.ext
  exact ρ.partialTraceRight_outer_spectral_sum b

/-- The spectral purification using a full-dimensional copy of the original system. -/
def purify (ρ : Density H) : UnitState (H ⊗ H) :=
  ρ.purifyWith (stdOrthonormalBasis ℂ H.state)

/-- The default purification uses the standard orthonormal basis on the auxiliary copy. -/
lemma coe_purify (ρ : Density H) :
    ρ.purify.val = ∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ]
      stdOrthonormalBasis ℂ H.state i := rfl

/-- The right partial trace of the pure spectral purification is the original density. -/
lemma partialTraceRight_pure_purify (ρ : Density H) :
    (pure ρ.purify).partialTraceRight = ρ :=
  ρ.partialTraceRight_pure_purifyWith (stdOrthonormalBasis ℂ H.state)

/-- A purification bundled with its marginal recovery property. -/
def purification (ρ : Density H) :
    {ψ : UnitState (H ⊗ H) // (pure ψ).partialTraceRight = ρ} :=
  ⟨ρ.purify, ρ.partialTraceRight_pure_purify⟩

/-- Every density operator is the marginal of a pure state on two copies of its system. -/
lemma exists_purification (ρ : Density H) :
    ∃ ψ : UnitState (H ⊗ H), (pure ψ).partialTraceRight = ρ :=
  ⟨ρ.purify, ρ.partialTraceRight_pure_purify⟩

/-- With the auxiliary copy moved to the left, the left partial trace recovers the input. -/
lemma partialTraceLeft_pure_purify_swap (ρ : Density H) :
    (pure ρ.purify.swap).partialTraceLeft = ρ := by
  have h := partialTraceRight_pure_swap ρ.purify.swap
  rw [UnitState.swap_swap, ρ.partialTraceRight_pure_purify] at h
  exact h.symm

end

end Qudit.Density

namespace Qudit.UnitState

noncomputable section

variable {H K L : Qudit}

/-- Contracting the unchanged leg commutes with an isometry on the auxiliary leg. -/
lemma contractLeft_map_isometry (ψ : UnitState (H ⊗ K)) (V : K ⟶ L) [IsIsometry V]
    (x : H.state) : (ψ.map (𝟙 H ⊗ₘ V)).contractLeft x = V (ψ.contractLeft x) := by
  apply ext_inner_left ℂ
  intro y
  rw [inner_contractLeft]
  change inner ℂ (x ⊗ₜ[ℂ] y) ((𝟙 H ⊗ₘ V).hom ψ.val) =
    inner ℂ y (V.hom (ψ.contractLeft x))
  rw [hom_tensorHom, hom_id, ← LinearMap.adjoint_inner_left, TensorProduct.adjoint_map,
    TensorProduct.map_tmul, LinearMap.adjoint_id, LinearMap.id_apply,
    ← inner_contractLeft, LinearMap.adjoint_inner_left]

/-- An auxiliary isometry leaves the retained marginal of a pure state unchanged. -/
lemma partialTraceRight_pure_map_isometry (ψ : UnitState (H ⊗ K))
    (V : K ⟶ L) [IsIsometry V] :
    (Density.pure (ψ.map (𝟙 H ⊗ₘ V))).partialTraceRight =
      (Density.pure ψ).partialTraceRight := by
  apply Density.ext
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [← inner_contractLeft_contractLeft, ← inner_contractLeft_contractLeft,
    contractLeft_map_isometry, contractLeft_map_isometry]
  exact inner_map_map_of_isIsometry V _ _

/-- Contracting the unchanged leg commutes with a unitary on the auxiliary leg. -/
lemma contractLeft_map_unitary (ψ : UnitState (H ⊗ K)) (U : K ⟶ L) [IsUnitary U]
    (x : H.state) : (ψ.map (𝟙 H ⊗ₘ U)).contractLeft x = U (ψ.contractLeft x) :=
  ψ.contractLeft_map_isometry U x

/-- An auxiliary unitary leaves the retained marginal of a pure state unchanged. -/
lemma partialTraceRight_pure_map_unitary (ψ : UnitState (H ⊗ K))
    (U : K ⟶ L) [IsUnitary U] :
    (Density.pure (ψ.map (𝟙 H ⊗ₘ U))).partialTraceRight =
      (Density.pure ψ).partialTraceRight :=
  ψ.partialTraceRight_pure_map_isometry U

/-- Two purifications with the same left marginal and equal-dimensional auxiliary systems
are related by a unitary acting only on the auxiliary system. The vector equality is exact. -/
theorem exists_unitary_of_partialTraceRight_eq (ψ : UnitState (H ⊗ K))
    (φ : UnitState (H ⊗ L)) (hdim : Module.finrank ℂ K.state = Module.finrank ℂ L.state)
    (h : (Density.pure ψ).partialTraceRight = (Density.pure φ).partialTraceRight) :
    ∃ (U : K ⟶ L) (_ : IsUnitary U), φ = ψ.map (𝟙 H ⊗ₘ U) := by
  let e : ψ.SchmidtIndex ≃ φ.SchmidtIndex :=
    Equiv.subtypeEquivRight (fun i => by rw [h])
  have hc (i : ψ.SchmidtIndex) : φ.schmidtCoefficient (e i) = ψ.schmidtCoefficient i := by
    simp only [schmidtCoefficient, e, Equiv.subtypeEquivRight_apply, h]
  have hl (i : ψ.SchmidtIndex) : φ.schmidtLeft (e i) = ψ.schmidtLeft i := by
    simp only [schmidtLeft, e, Equiv.subtypeEquivRight_apply, h]
  obtain ⟨V, hV⟩ := ψ.orthonormal_schmidtRight.exists_linearIsometryEquiv
    (φ.orthonormal_schmidtRight.comp e e.injective) hdim
  let U : K ⟶ L := (isoMk V.toLinearEquiv).hom
  let : IsUnitary U := isUnitary_isoMk_coe_LIEquiv V
  refine ⟨U, inferInstance, Subtype.ext ?_⟩
  change φ.val = (𝟙 H ⊗ₘ U).hom ψ.val
  rw [ψ.schmidt_decomposition, map_sum, φ.schmidt_decomposition]
  rw [← e.sum_comp (fun i => (φ.schmidtCoefficient i : ℂ) •
    (φ.schmidtLeft i ⊗ₜ[ℂ] φ.schmidtRight i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hom_tensorHom, TensorProduct.map_tmul]
  change (φ.schmidtCoefficient (e i) : ℂ) •
    (φ.schmidtLeft (e i) ⊗ₜ[ℂ] φ.schmidtRight (e i)) =
    (ψ.schmidtCoefficient i : ℂ) • (ψ.schmidtLeft i ⊗ₜ[ℂ] V (ψ.schmidtRight i))
  rw [hc, hl, hV]
  rfl

/-- Equal retained marginals characterize auxiliary-only unitary equivalence when the
auxiliary dimensions agree. -/
theorem partialTraceRight_eq_iff_exists_unitary (ψ : UnitState (H ⊗ K))
    (φ : UnitState (H ⊗ L)) (hdim : Module.finrank ℂ K.state = Module.finrank ℂ L.state) :
    (Density.pure ψ).partialTraceRight = (Density.pure φ).partialTraceRight ↔
      ∃ (U : K ⟶ L) (_ : IsUnitary U), φ = ψ.map (𝟙 H ⊗ₘ U) := by
  constructor
  · exact ψ.exists_unitary_of_partialTraceRight_eq φ hdim
  · rintro ⟨U, hU, rfl⟩
    exact (ψ.partialTraceRight_pure_map_unitary U).symm

/-- Purifications of the same retained state are related by an auxiliary isometry whenever
the source auxiliary dimension is at most the target auxiliary dimension. -/
theorem exists_isometry_of_partialTraceRight_eq (ψ : UnitState (H ⊗ K))
    (φ : UnitState (H ⊗ L)) (hdim : Module.finrank ℂ K.state ≤ Module.finrank ℂ L.state)
    (h : (Density.pure ψ).partialTraceRight = (Density.pure φ).partialTraceRight) :
    ∃ (V : K ⟶ L) (_ : IsIsometry V), φ = ψ.map (𝟙 H ⊗ₘ V) := by
  let J : K ⟶ L := ofLinearIsometry (LinearIsometry.ofFinrankLE hdim)
  obtain ⟨U, hU, hφ⟩ := (ψ.map (𝟙 H ⊗ₘ J)).exists_unitary_of_partialTraceRight_eq
    φ rfl ((ψ.partialTraceRight_pure_map_isometry J).trans h)
  refine ⟨J ≫ U, inferInstance, hφ.trans (Subtype.ext ?_)⟩
  change ((𝟙 H ⊗ₘ J) ≫ (𝟙 H ⊗ₘ U)).hom ψ.val = (𝟙 H ⊗ₘ (J ≫ U)).hom ψ.val
  rw [tensorHom_comp_tensorHom, Category.id_comp]

/-- Equality of retained marginals characterizes auxiliary isometric equivalence in the
direction from the smaller auxiliary space to the larger one. -/
theorem partialTraceRight_eq_iff_exists_isometry (ψ : UnitState (H ⊗ K))
    (φ : UnitState (H ⊗ L)) (hdim : Module.finrank ℂ K.state ≤ Module.finrank ℂ L.state) :
    (Density.pure ψ).partialTraceRight = (Density.pure φ).partialTraceRight ↔
      ∃ (V : K ⟶ L) (_ : IsIsometry V), φ = ψ.map (𝟙 H ⊗ₘ V) := by
  constructor
  · exact ψ.exists_isometry_of_partialTraceRight_eq φ hdim
  · rintro ⟨V, hV, rfl⟩
    exact (ψ.partialTraceRight_pure_map_isometry V).symm

end

end Qudit.UnitState

namespace Qudit.Density

noncomputable section

variable {H K L : Qudit}

/-- Two purifications of a specified density are related by an auxiliary isometry from
the smaller auxiliary system to the larger one, with exact equality of unit vectors. -/
theorem exists_isometry_of_purifications (ρ : Density H)
    (ψ : UnitState (H ⊗ K)) (φ : UnitState (H ⊗ L))
    (hdim : Module.finrank ℂ K.state ≤ Module.finrank ℂ L.state)
    (hψ : (pure ψ).partialTraceRight = ρ) (hφ : (pure φ).partialTraceRight = ρ) :
    ∃ (V : K ⟶ L) (_ : IsIsometry V), φ = ψ.map (𝟙 H ⊗ₘ V) :=
  ψ.exists_isometry_of_partialTraceRight_eq φ hdim (hψ.trans hφ.symm)

/-- Every purification whose auxiliary dimension is at least the original system's
dimension is an auxiliary-isometric image of the chosen spectral purification. -/
theorem exists_eq_map_purify_of_finrank_le (ρ : Density H) (ψ : UnitState (H ⊗ K))
    (hdim : Module.finrank ℂ H.state ≤ Module.finrank ℂ K.state)
    (hψ : (pure ψ).partialTraceRight = ρ) :
    ∃ (V : H ⟶ K) (_ : IsIsometry V), ψ = ρ.purify.map (𝟙 H ⊗ₘ V) :=
  ρ.exists_isometry_of_purifications ρ.purify ψ hdim ρ.partialTraceRight_pure_purify hψ

/-- Any two purifications of a specified density on equal-dimensional auxiliary systems
differ by a unitary on the auxiliary factor alone. -/
theorem exists_unitary_of_purifications (ρ : Density H)
    (ψ : UnitState (H ⊗ K)) (φ : UnitState (H ⊗ L))
    (hdim : Module.finrank ℂ K.state = Module.finrank ℂ L.state)
    (hψ : (pure ψ).partialTraceRight = ρ) (hφ : (pure φ).partialTraceRight = ρ) :
    ∃ (U : K ⟶ L) (_ : IsUnitary U), φ = ψ.map (𝟙 H ⊗ₘ U) :=
  ψ.exists_unitary_of_partialTraceRight_eq φ hdim (hψ.trans hφ.symm)

/-- Every purification with a full-dimensional auxiliary system is an auxiliary-unitary
image of the chosen spectral purification. -/
theorem exists_eq_map_purify (ρ : Density H) (ψ : UnitState (H ⊗ K))
    (hdim : Module.finrank ℂ H.state = Module.finrank ℂ K.state)
    (hψ : (pure ψ).partialTraceRight = ρ) :
    ∃ (U : H ⟶ K) (_ : IsUnitary U), ψ = ρ.purify.map (𝟙 H ⊗ₘ U) :=
  ρ.exists_unitary_of_purifications ρ.purify ψ hdim ρ.partialTraceRight_pure_purify hψ

end

end Qudit.Density
