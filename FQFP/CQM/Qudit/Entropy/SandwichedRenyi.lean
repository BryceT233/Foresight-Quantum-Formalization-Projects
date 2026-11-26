/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for the sandwiched divergence and its trace functional.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/Relative.lean
QuantumInfo/Entropy/DPI.lean
-/

/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/HypothesisTesting.lean: the classical Rényi sum used in
the measurement converse, stated here for any common eigenbasis.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.Relative
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sandwiched Rényi relative entropy

For order `α > 1` put `s = 1 - 1/α`. The sandwich is
`σ^(-s/2) ρ σ^(-s/2)`, with negative powers taken on the support of the reference.
The trace functional sums the `α`-powers of its eigenvalues, including multiplicities.
-/

@[expose] public section

open CategoryTheory DaggerCategory
open scoped BigOperators

namespace Qudit

noncomputable section

variable {H K : Qudit}

namespace Density

/-- The positive operator obtained by sandwiching the source between two spectral powers
of the reference. The exponent on each side is `-s/2`. -/
def renyiSandwich (ρ σ : Density H) (s : ℝ) : Operator H :=
  let A := σ.spectralMap (fun x => x ^ (-s / 2))
  A ∘ₗ ρ.op ∘ₗ A.adjoint

lemma renyiSandwich_positive (ρ σ : Density H) (s : ℝ) : (ρ.renyiSandwich σ s).IsPositive :=
  ρ.positive.conj_adjoint _

/-- The sandwiched trace functional, evaluated by the finite-dimensional spectral theorem. -/
def sandwichedTraceFunctional (ρ σ : Density H) (α : ℝ) : ℝ :=
  let h := ρ.renyiSandwich_positive σ (1 - α⁻¹)
  ∑ i, (h.isSymmetric.eigenvalues rfl i) ^ α

lemma sandwichedTraceFunctional_nonneg (ρ σ : Density H) (α : ℝ) :
    0 ≤ ρ.sandwichedTraceFunctional σ α :=
  Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg ((ρ.renyiSandwich_positive σ _).nonneg_eigenvalues rfl i) α

open Classical in
/-- Sandwiched Rényi relative entropy of order strictly greater than one, in nats. -/
def sandwichedRenyiRelativeEntropy (ρ σ : Density H) (α : Set.Ioi (1 : ℝ)) : ENNReal :=
  if ρ.AbsolutelyContinuous σ then
    ENNReal.ofReal (Real.log (ρ.sandwichedTraceFunctional σ α) / (α.val - 1))
  else ⊤

/-- Infinite divergence is precisely failure of support inclusion. -/
lemma sandwichedRenyiRelativeEntropy_eq_top_iff (ρ σ : Density H) (α : Set.Ioi (1 : ℝ)) :
    ρ.sandwichedRenyiRelativeEntropy σ α = ⊤ ↔ ¬ρ.AbsolutelyContinuous σ := by
  by_cases h : ρ.AbsolutelyContinuous σ <;> simp [sandwichedRenyiRelativeEntropy, h]

/-- Isometric embedding conjugates the sandwich even when the reference has a kernel. -/
lemma renyiSandwich_map_isometry (ρ σ : Density H) {s : ℝ} (hs : s ≠ 0)
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).renyiSandwich (σ.map V) s =
      V.hom ∘ₗ ρ.renyiSandwich σ s ∘ₗ V.hom.adjoint := by
  have hz : (0 : ℝ) ^ (-s / 2) = 0 := Real.zero_rpow (by simpa using hs)
  ext x
  simp only [renyiSandwich, σ.spectralMap_map_isometry (fun x => x ^ (-s / 2)) hz V,
    op_map, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.comp_apply, hom_adjoint_apply_of_isIsometry]

private lemma sum_rpow_eigenvalues_conj {A : Operator H} (hA : A.IsPositive)
    (V : H ⟶ K) [IsIsometry V] {α : ℝ} (hα : α ≠ 0) :
    ∀ {B : Operator K} (hB : B.IsPositive), B = V.hom ∘ₗ A ∘ₗ V.hom.adjoint →
      ∑ i, (hB.isSymmetric.eigenvalues rfl i) ^ α =
        ∑ i, (hA.isSymmetric.eigenvalues rfl i) ^ α := by
  rintro _ hB rfl
  let a := stdOrthonormalBasis ℂ H.state
  let b := stdOrthonormalBasis ℂ K.state
  let M := LinearMap.toMatrix a.toBasis b.toBasis V.hom
  let N := LinearMap.toMatrix b.toBasis a.toBasis (A ∘ₗ V.hom.adjoint)
  let f (z : ℂ) := z.re ^ α
  have he := congrArg (fun p : Polynomial ℂ => (p.roots.map f).sum) (M.charpoly_mul_comm' N)
  have hm : (M * N).charpoly = (V.hom ∘ₗ A ∘ₗ V.hom.adjoint).charpoly := by
    dsimp only [M, N]
    rw [← LinearMap.toMatrix_comp, LinearMap.charpoly_toMatrix]
  have hn : (N * M).charpoly = A.charpoly := by
    rw [← LinearMap.toMatrix_comp, LinearMap.charpoly_toMatrix, LinearMap.comp_assoc,
      hom_adjoint_comp_of_isIsometry, LinearMap.comp_id]
  simp [Polynomial.roots_mul, Matrix.charpoly_monic, Polynomial.Monic.ne_zero] at he
  simpa only [Polynomial.roots_X_pow, Multiset.map_add,
    Multiset.sum_add, Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
    Multiset.sum_singleton, f, Complex.zero_re, Real.zero_rpow hα, nsmul_zero, zero_add, hm, hn,
    (hA.conj_adjoint V.hom).isSymmetric.roots_charpoly_eq_eigenvalues rfl,
    hA.isSymmetric.roots_charpoly_eq_eigenvalues rfl, Multiset.map_map, Finset.sum,
    Function.comp_def, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using he

/-- The sandwiched trace functional is unchanged by an isometric embedding at order `α > 1`. -/
lemma sandwichedTraceFunctional_map_isometry (ρ σ : Density H) {α : ℝ} (hα : 1 < α)
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).sandwichedTraceFunctional (σ.map V) α = ρ.sandwichedTraceFunctional σ α := by
  have hs : 0 < 1 - α⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hα)
  exact sum_rpow_eigenvalues_conj (ρ.renyiSandwich_positive σ _) V (zero_lt_one.trans hα).ne'
    ((ρ.map V).renyiSandwich_positive (σ.map V) _) (ρ.renyiSandwich_map_isometry σ hs.ne' V)

/-- Relative entropy of order `α > 1` is invariant under a common isometric embedding. -/
lemma sandwichedRenyiRelativeEntropy_map_isometry (ρ σ : Density H) (α : Set.Ioi (1 : ℝ))
    (V : H ⟶ K) [IsIsometry V] :
    (ρ.map V).sandwichedRenyiRelativeEntropy (σ.map V) α =
      ρ.sandwichedRenyiRelativeEntropy σ α := by
  classical
  simp only [sandwichedRenyiRelativeEntropy, absolutelyContinuous_map_iff,
    sandwichedTraceFunctional_map_isometry _ _ α.property]

/-- Evaluate the trace functional in an orthonormal eigenbasis of the sandwich. -/
lemma sandwichedTraceFunctional_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (α : ℝ) (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, ρ.renyiSandwich σ (1 - α⁻¹) (b i) = (w i : ℂ) • b i) :
    ρ.sandwichedTraceFunctional σ α = ∑ i, w i ^ α := by
  have he := Operator.eigenvalues_eq_of_eigenbasis
    (ρ.renyiSandwich_positive σ (1 - α⁻¹)).isSymmetric b w hw
  simpa only [sandwichedTraceFunctional, Finset.sum, Multiset.map_map, Function.comp_def] using
    congrArg (fun m : Multiset ℝ => (m.map (fun r => r ^ α)).sum) he

/-- Evaluate the trace functional in any common eigenbasis of the two states. -/
lemma sandwichedTraceFunctional_eq_sum_of_common_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (α : ℝ) (b : OrthonormalBasis ι ℂ H.state) (p q : ι → ℝ)
    (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i) (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) :
    ρ.sandwichedTraceFunctional σ α = ∑ i, (q i ^ (-(1 - α⁻¹) / 2) *
      (p i * q i ^ (-(1 - α⁻¹) / 2))) ^ α := by
  let s := 1 - α⁻¹
  let w (i : ι) := q i ^ (-s / 2) * (p i * q i ^ (-s / 2))
  have hw (i) : ρ.renyiSandwich σ s (b i) = (w i : ℂ) • b i := by
    simp only [renyiSandwich, adjoint_spectralMap, LinearMap.comp_apply,
      σ.spectralMap_apply_of_eigenvector _ (hq i), map_smul, hp, smul_smul, w, Complex.ofReal_mul,
      mul_assoc]
  exact ρ.sandwichedTraceFunctional_eq_sum_of_eigenbasis σ α b w hw

/-- On commuting states the sandwiched trace functional is a sum over eigenvalue pairs.
Terms at zero reference eigenvalues vanish by the pseudoinverse convention. -/
lemma sandwichedTraceFunctional_eq_rpow_sum_of_common_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) {α : ℝ} (hα : 1 < α) (b : OrthonormalBasis ι ℂ H.state) (p q : ι → ℝ)
    (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i) (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i)
    (hp₀ : ∀ i, 0 ≤ p i) (hq₀ : ∀ i, 0 ≤ q i) :
    ρ.sandwichedTraceFunctional σ α = ∑ i, p i ^ α * q i ^ (1 - α) := by
  rw [sandwichedTraceFunctional_eq_sum_of_common_eigenbasis ρ σ α b p q hp hq]
  apply Finset.sum_congr rfl
  intro i _
  let t := -(1 - α⁻¹) / 2
  have hα₀ : 0 < α := zero_lt_one.trans hα
  change (q i ^ t * (p i * q i ^ t)) ^ α = _
  rcases (hq₀ i).eq_or_lt with he | hqpos
  · have ht : t < 0 := div_neg_of_neg_of_pos
      (neg_lt_zero.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hα))) (by norm_num)
    rw [← he, Real.zero_rpow ht.ne, mul_zero, mul_zero, Real.zero_rpow hα₀.ne',
      Real.zero_rpow (sub_neg.mpr hα).ne, mul_zero]
  · rw [mul_left_comm, ← Real.rpow_add hqpos, Real.mul_rpow (hp₀ i) (Real.rpow_nonneg hqpos.le _),
      ← Real.rpow_mul hqpos.le]
    have he : (t + t) * α = 1 - α := by
      dsimp [t]
      field_simp [hα₀.ne']
      ring
    rw [he]

/-- Identical densities have unit sandwiched trace functional at every order above one. -/
lemma sandwichedTraceFunctional_self (ρ : Density H) {α : ℝ} (hα : 1 < α) :
    ρ.sandwichedTraceFunctional ρ α = 1 := by
  rw [sandwichedTraceFunctional_eq_sum_of_common_eigenbasis ρ ρ α ρ.eigenbasis
    ρ.eigenvalue ρ.eigenvalue ρ.apply_eigenbasis ρ.apply_eigenbasis]
  conv_rhs => rw [← ρ.sum_eigenvalue]
  apply Finset.sum_congr rfl
  intro i _
  have ha := zero_lt_one.trans hα
  by_cases hz : ρ.eigenvalue i = 0
  · simp [hz, Real.zero_rpow ha.ne']
  have hp := (ρ.eigenvalue_nonneg i).lt_of_ne' hz
  nth_rw 2 [← Real.rpow_one (ρ.eigenvalue i)]
  rw [← Real.rpow_add hp, ← Real.rpow_add hp, ← Real.rpow_mul hp.le]
  convert Real.rpow_one (ρ.eigenvalue i) using 2
  field_simp
  ring

/-- Identical states have zero sandwiched Rényi relative entropy, including singular states. -/
@[simp]
lemma sandwichedRenyiRelativeEntropy_self (ρ : Density H) (α : Set.Ioi (1 : ℝ)) :
    ρ.sandwichedRenyiRelativeEntropy ρ α = 0 := by
  simp [sandwichedRenyiRelativeEntropy, AbsolutelyContinuous.refl,
    sandwichedTraceFunctional_self ρ α.property]

end Density

end

end Qudit
