/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/

/-
Physlib reference for spectral pinching and the pinching bound.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/Pinching.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Process.Classical
public import FQFP.CQM.Qudit.State.Spectral.FunctionalCalculus
import Mathlib.Algebra.Order.Chebyshev

/-!
# Spectral pinching

The channel sums conjugations by the orthogonal projections onto the distinct eigenspaces
of a reference density, including its kernel when present. Its fixed operators are exactly
those commuting with the reference. In particular, coherences within a degenerate eigenspace
survive, and a reference with simple spectrum gives ordinary eigenbasis dephasing.
The pinching inequality bounds every positive operator by the number of spectral blocks
times its pinched operator.
-/

@[expose] public section

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- Distinct eigenvalues of a density, with each spectral block counted once. -/
def spectralValues (σ : Density H) : Finset ℝ := Finset.univ.image σ.eigenvalue

/-- The eigenvalue of a nonzero eigenvector indexes a spectral block. -/
lemma mem_spectralValues_of_hasEigenvector (σ : Density H) {a : ℝ} {x : H.state}
    (hx : σ.op.HasEigenvector (a : ℂ) x) : a ∈ σ.spectralValues := by
  obtain ⟨i, hi⟩ := σ.positive.isSymmetric.exists_eigenvalues_eq rfl
    (Module.End.hasEigenvalue_of_hasEigenvector hx)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, Complex.ofReal_injective hi⟩

/-- The distinct spectral values can be computed in any orthonormal diagonalization. -/
lemma spectralValues_eq_image_of_eigenbasis {ι : Type*} [Fintype ι] (σ : Density H)
    (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, σ.op (b i) = (w i : ℂ) • b i) : σ.spectralValues = Finset.univ.image w :=
  congrArg Multiset.toFinset (σ.eigenvalues_eq_of_eigenbasis b w hw)

/-- Orthogonal projection onto the entire eigenspace at `a`. -/
def spectralProjection (σ : Density H) (a : ℝ) : Operator H :=
  σ.spectralMap (fun b => if b = a then 1 else 0)

/-- The spectral projection selects an eigenvector according to its eigenvalue. -/
lemma spectralProjection_apply_of_eigenvector (σ : Density H) (a : ℝ) {b : ℝ} {x : H.state}
    (hx : σ.op x = (b : ℂ) • x) :
    σ.spectralProjection a x = if b = a then x else 0 := by
  rw [spectralProjection, σ.spectralMap_apply_of_eigenvector _ hx]
  split_ifs <;> simp

/-- Spectral projections are self-adjoint. -/
lemma adjoint_spectralProjection (σ : Density H) (a : ℝ) :
    (σ.spectralProjection a).adjoint = σ.spectralProjection a := σ.adjoint_spectralMap _

/-- Distinct spectral projections are orthogonal, and each one is idempotent. -/
lemma spectralProjection_mul (σ : Density H) (a b : ℝ) :
    σ.spectralProjection a * σ.spectralProjection b =
      if a = b then σ.spectralProjection a else 0 := by
  apply σ.eigenbasis.toBasis.ext
  intro i
  change σ.spectralProjection a (σ.spectralProjection b (σ.eigenbasis i)) =
    (if a = b then σ.spectralProjection a else 0) (σ.eigenbasis i)
  by_cases hab : a = b <;> by_cases hb : σ.eigenvalue i = b <;>
    simp_all [σ.spectralProjection_apply_of_eigenvector _ (σ.apply_eigenbasis i), eq_comm]

/-- The distinct spectral blocks resolve the identity. -/
lemma sum_spectralProjection (σ : Density H) :
    ∑ a ∈ σ.spectralValues, σ.spectralProjection a = 1 := by
  apply σ.eigenbasis.toBasis.ext
  intro i
  change (∑ a ∈ σ.spectralValues, σ.spectralProjection a) (σ.eigenbasis i) = σ.eigenbasis i
  simp [LinearMap.sum_apply, σ.spectralProjection_apply_of_eigenvector _ (σ.apply_eigenbasis i),
    spectralValues]

/-- Multiplication by the reference acts as a scalar on each spectral block. -/
lemma mul_spectralProjection (σ : Density H) (a : ℝ) :
    σ.op * σ.spectralProjection a = (a : ℂ) • σ.spectralProjection a := by
  apply σ.eigenbasis.toBasis.ext
  intro i
  change σ.op (σ.spectralProjection a (σ.eigenbasis i)) =
    (a : ℂ) • σ.spectralProjection a (σ.eigenbasis i)
  by_cases hi : σ.eigenvalue i = a <;>
    simp [σ.spectralProjection_apply_of_eigenvector _ (σ.apply_eigenbasis i),
      σ.apply_eigenbasis, hi]

/-- The projective measurement with one outcome per distinct eigenvalue, including
the zero eigenvalue when the reference has a kernel. -/
def spectralResolution (σ : Density H) :
    CategoryTheory.OrthogonalResolution H σ.spectralValues where
  op a := .of (ofHom (σ.spectralProjection a))
  isStarProjection a := by
    apply (isStarProjection_iff_hom _).mpr
    change IsStarProjection (σ.spectralProjection a)
    exact ⟨by rw [IsIdempotentElem, spectralProjection_mul, ite_eq_left rfl],
      σ.adjoint_spectralProjection a⟩
  orthogonal := by
    intro a b hab
    apply hom_ext
    change σ.spectralProjection b * σ.spectralProjection a = 0
    rw [spectralProjection_mul, ite_eq_right (fun h ↦ hab (Subtype.ext h.symm))]
  sum_proj := by
    apply hom_ext
    rw [hom_sum]
    exact (σ.spectralValues.sum_coe_sort σ.spectralProjection).trans σ.sum_spectralProjection

/-- The CPTP channel obtained by measuring the spectral blocks and forgetting the outcome. -/
def pinching (σ : Density H) : QuantumChannel H H :=
  QuantumChannel.ofKraus (fun a : σ.spectralValues => σ.spectralProjection a) (by
    change ∑ a : σ.spectralValues, (σ.spectralProjection a).adjoint * σ.spectralProjection a = 1
    simp only [adjoint_spectralProjection, spectralProjection_mul, ite_true]
    exact (σ.spectralValues.sum_coe_sort σ.spectralProjection).trans σ.sum_spectralProjection)

/-- Pinching sums the diagonal blocks of an arbitrary input operator. -/
lemma pinching_apply (σ : Density H) (A : Operator H) :
    σ.pinching.toSuperoperator A =
      ∑ a ∈ σ.spectralValues, σ.spectralProjection a * A * σ.spectralProjection a := by
  change Superoperator.kraus _ A = _
  rw [Superoperator.kraus_apply]
  simp only [adjoint_spectralProjection]
  exact σ.spectralValues.sum_coe_sort fun a => σ.spectralProjection a * A * σ.spectralProjection a

/-- The spectral pinching channel is the unread Lüders measurement of the eigenspaces. -/
theorem pinching_eq_luders_toChannel (σ : Density H) :
    σ.pinching = (POVM.ofOrthogonalResolution σ.spectralResolution).luders.toChannel := by
  apply QuantumChannel.ext
  apply LinearMap.ext
  intro A
  rw [POVM.luders_toChannel_ofOrthogonalResolution, pinching_apply,
    CategoryTheory.OrthogonalResolution.diagonalPart, hom_sum]
  exact (σ.spectralValues.sum_coe_sort
    fun a ↦ σ.spectralProjection a * A * σ.spectralProjection a).symm

/-- **Pinching inequality**. A positive operator is dominated in Löwner order by its
pinching times the number of distinct eigenvalues, including zero when present. -/
theorem le_card_smul_pinching (σ : Density H) (A : Operator H) (hA : A.IsPositive) :
    A ≤ σ.spectralValues.card • σ.pinching.toSuperoperator A := by
  have hp := σ.pinching.completelyPositive.isPositive A hA
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  apply LinearMap.le_def.mpr
  refine ⟨(hp.isSymmetric.smul (by simp)).sub hA.isSymmetric, fun x => ?_⟩
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x ((_ - A) x)).re
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right,
    Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
    sub_nonneg]
  let v (a : ℝ) := A.sqrt (σ.spectralProjection a x)
  have hsum : ∑ a ∈ σ.spectralValues, v a = A.sqrt x := by
    simp only [v, ← map_sum, ← LinearMap.sum_apply, sum_spectralProjection, one_apply_eq_self]
  have hinner (a : ℝ) (y : H.state) :
      inner ℂ x (σ.spectralProjection a y) = inner ℂ (σ.spectralProjection a x) y := by
    rw [← LinearMap.adjoint_inner_left, adjoint_spectralProjection]
  simp only [pinching_apply, LinearMap.sum_apply, mul_apply_eq_comp, inner_sum, Complex.re_sum,
    hinner, A.re_inner_apply_eq_norm_sqrt_sq hA]
  rw [← hsum]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
    (sq_sum_le_card_mul_sum_sq (s := σ.spectralValues) (f := fun a => ‖v a‖))

/-- The density-operator form of the pinching inequality. -/
theorem le_card_smul_pinching_map (ρ σ : Density H) :
    ρ.op ≤ (σ.spectralValues.card : ℝ) • (σ.pinching.map ρ).op := by
  rw [Nat.cast_smul_eq_nsmul]
  exact σ.le_card_smul_pinching ρ.op ρ.positive

/-- Every pinched operator commutes with the reference. -/
lemma commute_pinching (σ : Density H) (A : Operator H) :
    Commute σ.op (σ.pinching.toSuperoperator A) := by
  change σ.op * _ = _ * σ.op
  rw [pinching_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hc := (σ.commute_spectralMap (Commute.refl σ.op) (fun b => if b = a then 1 else 0)).eq
  change σ.op * σ.spectralProjection a = σ.spectralProjection a * σ.op at hc
  rw [← mul_assoc, ← mul_assoc, σ.mul_spectralProjection, smul_mul_assoc, smul_mul_assoc,
    mul_assoc _ (σ.spectralProjection a) σ.op, ← hc, σ.mul_spectralProjection, mul_smul_comm]

/-- Pinching fixes precisely the operators in the commutant of the reference. -/
lemma pinching_apply_eq_self_iff (σ : Density H) (A : Operator H) :
    σ.pinching.toSuperoperator A = A ↔ Commute A σ.op := by
  refine ⟨fun h => h ▸ (σ.commute_pinching A).symm, fun h => ?_⟩
  rw [pinching_apply]
  calc
    _ = ∑ a ∈ σ.spectralValues, A * σ.spectralProjection a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      have hc : Commute A (σ.spectralProjection a) := σ.commute_spectralMap h _
      rw [← hc.eq, mul_assoc, spectralProjection_mul, ite_eq_left rfl]
    _ = A := by rw [← Finset.mul_sum, sum_spectralProjection, mul_one]

/-- The channel fixes its reference density, including singular ones. -/
lemma pinching_map_self (σ : Density H) : σ.pinching.map σ = σ :=
  Density.ext ((σ.pinching_apply_eq_self_iff σ.op).mpr (Commute.refl _))

/-- Applying the pinching channel twice equals applying it once. -/
lemma pinching_idempotent (σ : Density H) : σ.pinching.comp σ.pinching = σ.pinching := by
  rw [pinching_eq_luders_toChannel]
  exact POVM.luders_toChannel_idempotent σ.spectralResolution

/-- The coherence between two eigenvectors survives exactly within a common spectral block.
The eigenvectors can be chosen freely within either eigenspace. -/
lemma pinching_outer_of_eigenvectors (σ : Density H) {x y : H.state} {a b : ℝ}
    (hx : σ.op x = (a : ℂ) • x) (hy : σ.op y = (b : ℂ) • y) :
    σ.pinching.toSuperoperator (Operator.outer x y) = if a = b then Operator.outer x y else 0 := by
  classical
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp [show Operator.outer (0 : H.state) y = 0 by ext z; simp]
  rcases eq_or_ne y 0 with rfl | hy₀
  · simp [show Operator.outer x 0 = 0 by ext z; simp]
  have ha := σ.mem_spectralValues_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hx, hx₀⟩
  have hb := σ.mem_spectralValues_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hy, hy₀⟩
  rw [pinching_eq_luders_toChannel]
  simpa only [Subtype.mk.injEq] using POVM.luders_toChannel_outer σ.spectralResolution
    (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (x := x) (y := y)
    ((σ.spectralProjection_apply_of_eigenvector a hx).trans (ite_eq_left rfl))
    ((σ.spectralProjection_apply_of_eigenvector b hy).trans (ite_eq_left rfl))

/-- For simple spectrum, pinching is dephasing in the eigenbasis. -/
lemma pinching_eq_dephase_of_injective (σ : Density H) (hs : Function.Injective σ.eigenvalue) :
    σ.pinching = QuantumChannel.dephase σ.eigenbasis := by
  classical
  apply QuantumChannel.ext
  apply Operator.basis_outer_ext σ.eigenbasis
  intro i j
  simp only [σ.pinching_outer_of_eigenvectors (σ.apply_eigenbasis i) (σ.apply_eigenbasis j),
    QuantumChannel.dephase_basis_outer, hs.eq_iff]

/-- The maximally mixed reference has a single spectral block. -/
lemma pinching_maximallyMixed (h : Module.finrank ℂ H.state ≠ 0) :
    (maximallyMixed H h).pinching = QuantumChannel.id H := by
  apply QuantumChannel.ext
  refine LinearMap.ext fun A => ((maximallyMixed H h).pinching_apply_eq_self_iff A).mpr ?_
  rw [op_maximallyMixed]
  exact (Commute.one_right A).smul_right _

end

end Qudit.Density
