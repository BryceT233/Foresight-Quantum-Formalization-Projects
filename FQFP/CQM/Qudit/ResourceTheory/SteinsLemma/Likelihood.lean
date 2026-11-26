/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/SteinsLemma.lean: likelihood tests after pinching in the
direct part of the generalized Stein lemma.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.ResourceTheory.SteinsLemma.SpectralRounding
public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.RenyiBound
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-!
# Likelihood tests after pinching

A common eigenbasis of the pinched null and the reference gives classical likelihoods.
A least favorable alternative controls the mass below a threshold. A sandwiched Rényi
bound against a supported comparison state controls the excess above a second threshold.
-/

@[expose] public noncomputable section

open scoped ComplexOrder ENNReal

namespace Qudit.Density

variable {H : Qudit} {ι : Type*} [Fintype ι]

open Classical in
private lemma exists_common_basis (ρ σ : Density H) (h : Commute ρ.op σ.op) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ H.state)
      (p q : Fin (Module.finrank ℂ H.state) → ℝ),
      (∀ i, ρ.op (b i) = (p i : ℂ) • b i) ∧
        (∀ i, σ.op (b i) = (q i : ℂ) • b i) := by
  let hρ := ρ.positive.isSymmetric
  let hσ := σ.positive.isSymmetric
  let hS := hρ.directSum_isInternal_of_commute hσ h
  let ho := hρ.orthogonalFamily_eigenspace_inf_eigenspace hσ
  let V (i : ℂ × ℂ) : Submodule ℂ H.state :=
    Module.End.eigenspace ρ.op i.2 ⊓ Module.End.eigenspace σ.op i.1
  let c (i : ℂ × ℂ) := stdOrthonormalBasis ℂ (V i)
  let I := Σ i : ℂ × ℂ, Fin (Module.finrank ℂ (V i))
  let B : Module.Basis I ℂ H.state := hS.collectedBasis (fun i => (c i).toBasis)
  have : Finite I := B.finite_index_of_rank_lt_aleph0 (Module.rank_lt_aleph0 ℂ H.state)
  let : Fintype I := Fintype.ofFinite I
  have hB : Orthonormal ℂ B :=
    DirectSum.IsInternal.collectedBasis_orthonormal ho hS (by simp)
  let b₀ := B.toOrthonormalBasis hB
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  let b := b₀.reindex e
  let k := fun i => (e.symm i).1
  have hmb (i) : b i ∈ Module.End.eigenspace ρ.op (k i).2 ∧
      b i ∈ Module.End.eigenspace σ.op (k i).1 := by
    simp only [b, OrthonormalBasis.reindex_apply, b₀, Module.Basis.coe_toOrthonormalBasis]
    exact hS.collectedBasis_mem (fun i => (c i).toBasis) (e.symm i)
  have eig {A : Operator H} (hA : A.IsSymmetric) {x : H.state} (hx : x ≠ 0)
      {a : ℂ} (ha : x ∈ Module.End.eigenspace A a) : A x = (a.re : ℂ) • x := by
    have hv := hA.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨ha, hx⟩)
    have he : (a.re : ℂ) = a := RCLike.conj_eq_iff_re.mp hv
    rw [he]
    exact Module.End.mem_eigenspace_iff.mp ha
  exact ⟨b, fun i => (k i).2.re, fun i => (k i).1.re,
    fun i => eig hρ (b.toBasis.ne_zero i) (hmb i).1,
    fun i => eig hσ (b.toBasis.ne_zero i) (hmb i).2⟩

private lemma probability_eq_eigenvalue (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H)
    {p : ι → ℝ} (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i) (i : ι) :
    (POVM.ofBasis b).probability ρ i = p i := by
  rw [POVM.probability_ofBasis, hp, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re]

private lemma map_dephase_apply_basis (b : OrthonormalBasis ι ℂ H.state) (ρ : Density H)
    (i : ι) :
    ((QuantumChannel.dephase b).map ρ).op (b i) =
      ((POVM.ofBasis b).probability ρ i : ℂ) • b i := by
  classical
  rw [QuantumChannel.op_map, QuantumChannel.dephase_apply, POVM.probability_ofBasis]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Operator.outer_apply, b.inner_eq_ite,
    ite_smul, one_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  exact congrArg (· • b i) (ρ.positive.isSymmetric.coe_re_inner_self_apply (b i)).symm

private lemma basis_projection_commute (b : OrthonormalBasis ι ℂ H.state) (σ : Density H)
    {q : ι → ℝ} (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) (j : ι) :
    Commute (Operator.outer (b j) (b j)) σ.op := by
  classical
  apply b.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, mul_apply_eq_comp, hq, map_smul,
    Operator.outer_apply, b.inner_eq_ite]
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

private lemma probability_of_pinching (ρ σ : Density H) (b : OrthonormalBasis ι ℂ H.state)
    {q : ι → ℝ} (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) (i : ι) :
    (POVM.ofBasis b).probability ρ i = (POVM.ofBasis b).probability (σ.pinching.map ρ) i :=
  (ρ.expectation_pinching_of_commute σ _ (basis_projection_commute b σ hq i)).symm

private def basisTest (b : OrthonormalBasis ι ℂ H.state) (s : Finset ι) :
    Set.Icc (0 : Operator H) 1 := by
  classical
  refine ⟨∑ i ∈ s, Operator.outer (b i) (b i),
    LinearMap.nonneg_iff_isPositive.mpr (LinearMap.isPositive_sum _ fun i _ =>
      Operator.isPositive_outer (b i)), ?_⟩
  have hs : ∑ i, Operator.outer (b i) (b i) = (1 : Operator H) := by
    simpa using Operator.sum_outer_basis b (1 : Operator H)
  rw [← hs]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => ?_
  exact LinearMap.nonneg_iff_isPositive.mpr (Operator.isPositive_outer _)

private lemma expectation_basisTest (b : OrthonormalBasis ι ℂ H.state) (s : Finset ι)
    (ρ : Density H) : ρ.expectation (basisTest b s) = ∑ i ∈ s, (POVM.ofBasis b).probability ρ i :=
  ρ.expectation_sum s _

private lemma basis_probability_le_smul (b : OrthonormalBasis ι ℂ H.state)
    {ρ σ : Density H} {c : ℝ} (hc : ρ.op ≤ c • σ.op) (i : ι) :
    (POVM.ofBasis b).probability ρ i ≤ c * (POVM.ofBasis b).probability σ i := by
  have h := (LinearMap.le_def.mp hc).re_inner_nonneg_right (b i)
  change 0 ≤ (inner ℂ (b i) ((c • σ.op - ρ.op) (b i))).re at h
  rw [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, Complex.sub_re, Complex.mul_re] at h
  simpa only [POVM.probability_ofBasis, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using h

private lemma probability_pos_of_strict (σ : Density H) (hσ : IsStrictlyPositive σ.op)
    (b : OrthonormalBasis ι ℂ H.state) (i : ι) : 0 < (POVM.ofBasis b).probability σ i := by
  rw [POVM.probability_ofBasis]
  apply (σ.positive.re_inner_nonneg_right (b i)).lt_of_ne'
  intro hz
  have hk := (σ.op.apply_eq_zero_iff_re_inner_eq_zero σ.positive _).mpr hz
  have hi := (LinearMap.isUnit_iff_ker_eq_bot σ.op).mp hσ.isUnit
  have := (LinearMap.ker_eq_bot'.mp hi) (b i) hk
  exact b.toBasis.ne_zero i this

private lemma sum_likelihood_le (p L : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    {a lo hi e : ℝ} (ha : 0 < a) (hlo : lo ≤ hi)
    (hprob : ∑ i ∈ Finset.univ.filter (fun i => 0 < p i ∧ lo ≤ L i), p i ≤ 1 - e) :
    ∑ i, p i * L i ≤ hi - e * (hi - lo) +
      (∑ i, p i * Real.exp (a * (L i - hi))) / a := by
  classical
  let S := Finset.univ.filter (fun i => 0 < p i ∧ lo ≤ L i)
  let η i := Real.exp (a * (L i - hi)) / a
  have hη i : 0 ≤ η i := (div_pos (Real.exp_pos _) ha).le
  have hpoint i : p i * L i ≤ lo * p i + (if i ∈ S then (hi - lo) * p i else 0) +
      p i * η i := by
    by_cases h : i ∈ S
    · rw [ite_eq_left h]
      have hL : L i - hi ≤ η i := (le_div_iff₀ ha).mpr (by
        rw [mul_comm]
        linarith [Real.add_one_le_exp (a * (L i - hi))])
      nlinarith [mul_le_mul_of_nonneg_right hL (hp i)]
    · rw [ite_eq_right h, add_zero]
      rcases (hp i).eq_or_lt with hz | hpos
      · simp [← hz]
      · have hn : L i ≤ lo := le_of_not_ge fun hge => h (Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hpos, hge⟩)
        exact (mul_le_mul_of_nonneg_left hn (hp i)).trans
          (by rw [mul_comm (p i) lo]; exact le_add_of_nonneg_right (mul_nonneg (hp i) (hη i)))
  calc
    _ ≤ ∑ i, (lo * p i + (if i ∈ S then (hi - lo) * p i else 0) + p i * η i) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = lo + (hi - lo) * (∑ i ∈ S, p i) + (∑ i, p i * Real.exp (a * (L i - hi))) / a := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one, η, ← mul_div_assoc,
        ← Finset.sum_div]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.mul_sum]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hprob (sub_nonneg.mpr hlo)]

private lemma sum_comparison_moment_le (ρ τ σ : Density H) (b : OrthonormalBasis ι ℂ H.state)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpb : ∀ i, (POVM.ofBasis b).probability ρ i = p i)
    (hqb : ∀ i, (POVM.ofBasis b).probability τ i = q i)
    (α : Set.Ioi (1 : ℝ)) (hac : ρ.AbsolutelyContinuous σ)
    {C hi : ℝ} (hC : 0 < C) (hdom : σ.op ≤ C • τ.op) :
    ∑ i, p i * Real.exp ((α.val - 1) * (Real.log (p i) - Real.log (q i) - hi)) ≤
      Real.exp ((α.val - 1) *
        ((ρ.sandwichedRenyiRelativeEntropy σ α).toReal + Real.log C - hi)) := by
  let Φ := QuantumChannel.dephase b
  let r := (POVM.ofBasis b).probability σ
  have hα := α.property
  have hα₀ : 0 < α.val := zero_lt_one.trans hα
  have hrd (i) : r i ≤ C * q i := by
    rw [← hqb i]
    exact basis_probability_le_smul b hdom i
  have hzp (i) (hr : r i = 0) : p i = 0 := by
    have hd := (absolutelyContinuous_iff_of_eigenbasis (Φ.map ρ) (Φ.map σ) b p r
      (fun i => (hpb i) ▸ map_dephase_apply_basis b ρ i)
      (map_dephase_apply_basis b σ)).mp (Φ.absolutelyContinuous_map hac)
    exact hd i hr
  have htrace := Φ.sandwichedTraceFunctional_map_le ρ σ hα hac
  rw [sandwichedTraceFunctional_eq_rpow_sum_of_common_eigenbasis _ _ hα b p r
    (fun i => (hpb i) ▸ map_dephase_apply_basis b ρ i) (map_dephase_apply_basis b σ)
    hp ((POVM.ofBasis b).probability_nonneg σ)] at htrace
  have hpoint (i) :
      p i * Real.exp ((α.val - 1) * (Real.log (p i) - Real.log (q i) - hi)) ≤
        Real.exp ((α.val - 1) * (Real.log C - hi)) * (p i ^ α.val * r i ^ (1 - α.val)) := by
    rcases (hp i).eq_or_lt with hz | hpp
    · simp [← hz, Real.zero_rpow hα₀.ne']
    · have hrp : 0 < r i := ((POVM.ofBasis b).probability_nonneg σ i).lt_of_ne'
        fun hr => hpp.ne' (hzp i hr)
      have hlog := Real.log_le_log hrp (hrd i)
      rw [Real.log_mul hC.ne' (hq i).ne'] at hlog
      calc
        _ = Real.exp (Real.log (p i) +
            (α.val - 1) * (Real.log (p i) - Real.log (q i) - hi)) := by
              rw [Real.exp_add, Real.exp_log hpp]
        _ ≤ Real.exp ((α.val - 1) * (Real.log C - hi) +
            (Real.log (p i) * α.val + Real.log (r i) * (1 - α.val))) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hα.le)]
        _ = _ := by
          rw [Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos hpp, ← Real.rpow_def_of_pos hrp]
  let Q := ρ.sandwichedTraceFunctional σ α
  have hQ : 1 ≤ Q := ρ.one_le_sandwichedTraceFunctional σ hα hac
  have hd : Real.log Q = (α.val - 1) * (ρ.sandwichedRenyiRelativeEntropy σ α).toReal := by
    rw [sandwichedRenyiRelativeEntropy, ite_eq_left hac]
    change Real.log Q = (α.val - 1) * (ENNReal.ofReal (Real.log Q / (α.val - 1))).toReal
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.log_nonneg hQ) (sub_nonneg.mpr hα.le)),
      mul_div_cancel₀ _ (sub_pos.mpr hα).ne']
  calc
    _ ≤ ∑ i, Real.exp ((α.val - 1) * (Real.log C - hi)) * (p i ^ α.val * r i ^ (1 - α.val)) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ ≤ Real.exp ((α.val - 1) * (Real.log C - hi)) * Q := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left htrace (Real.exp_pos _).le
    _ = _ := by
      nth_rw 1 [← Real.exp_log (zero_lt_one.trans_le hQ), ← Real.exp_add, hd]
      congr 1
      ring

/-- Bound the pinched relative entropy using a test against one alternative and a
Rényi divergence against a second, supported alternative. Both alternatives are dominated
by the pinching reference up to the same positive factor. -/
theorem relativeEntropyReal_pinching_le_of_test_and_renyi
    (ρ τ σ η : Density H) (hτ : IsStrictlyPositive τ.op)
    (ε : unitInterval) (α : Set.Ioi (1 : ℝ)) (hac : ρ.AbsolutelyContinuous η)
    {C lo hi : ℝ} (hC : 0 < C) (hlo : lo ≤ hi)
    (hσ : σ.op ≤ C • τ.op) (hη : η.op ≤ C • τ.op)
    (htest : C * Real.exp (-lo) < (ρ.optimalTypeIIError ε {σ} : ℝ)) :
    (τ.pinching.map ρ).relativeEntropyReal τ ≤ hi - ε.val * (hi - lo) +
      Real.exp ((α.val - 1) *
        ((ρ.sandwichedRenyiRelativeEntropy η α).toReal + Real.log C - hi)) / (α.val - 1) := by
  classical
  let ω := τ.pinching.map ρ
  obtain ⟨b, p, q, hpb, hqb⟩ := exists_common_basis ω τ (τ.commute_pinching ρ.op).symm
  have heq (i) : (POVM.ofBasis b).probability τ i = q i :=
    probability_eq_eigenvalue b τ hqb i
  have hep (i) : (POVM.ofBasis b).probability ρ i = p i :=
    (probability_of_pinching ρ τ b hqb i).trans (probability_eq_eigenvalue b ω hpb i)
  have hp (i) : 0 ≤ p i := hep i ▸ (POVM.ofBasis b).probability_nonneg ρ i
  have hq (i) : 0 < q i := heq i ▸ probability_pos_of_strict τ hτ b i
  have hsum : ∑ i, p i = 1 := by simpa only [hep] using (POVM.ofBasis b).sum_probability ρ
  let L i := Real.log (p i) - Real.log (q i)
  let S := Finset.univ.filter (fun i => 0 < p i ∧ lo ≤ L i)
  let T := basisTest b S
  have htp : ρ.expectation T = ∑ i ∈ S, p i := by rw [expectation_basisTest]; simp only [hep]
  have htq : σ.expectation T ≤ C * Real.exp (-lo) := by
    rw [expectation_basisTest]
    calc
      _ ≤ ∑ i ∈ S, C * (Real.exp (-lo) * p i) := by
        apply Finset.sum_le_sum
        intro i hiS
        obtain ⟨hpi, hiL⟩ := (Finset.mem_filter.mp hiS).2
        have hqexp : q i ≤ Real.exp (-lo) * p i := calc
          q i = Real.exp (Real.log (q i)) := (Real.exp_log (hq i)).symm
          _ ≤ Real.exp (-lo + Real.log (p i)) := Real.exp_le_exp.mpr (by dsimp [L] at hiL; linarith)
          _ = _ := by rw [Real.exp_add, Real.exp_log hpi]
        exact (basis_probability_le_smul b hσ i).trans
          (mul_le_mul_of_nonneg_left ((heq i).symm ▸ hqexp) hC.le)
      _ ≤ _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        have hs : ∑ i ∈ S, p i ≤ 1 := hsum ▸
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)
        simpa using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (Real.exp_pos (-lo)).le) hC.le
  have hmass : ∑ i ∈ S, p i ≤ 1 - ε.val := by
    by_contra! h
    have hb : ρ.expectation (1 - T.val) ≤ ε := by
      rw [expectation_sub, expectation_one, htp]
      linarith
    have he := ρ.optimalTypeIIError_le ε {σ} T hb
    rw [worstCaseTypeIIError_singleton] at he
    exact htest.not_ge ((show (ρ.optimalTypeIIError ε {σ} : ℝ) ≤ σ.expectation T from he).trans htq)
  change ω.relativeEntropyReal τ ≤ _
  rw [relativeEntropyReal_eq_sum_of_eigenbasis ω τ b p q hpb hqb]
  exact (sum_likelihood_le p L hp hsum (sub_pos.mpr α.property) hlo hmass).trans
    (add_le_add_right (div_le_div_of_nonneg_right
      (sum_comparison_moment_le ρ τ η b p q hp hq hep heq α hac hC hη)
      (sub_nonneg.mpr α.property.le)) _)

end Qudit.Density
