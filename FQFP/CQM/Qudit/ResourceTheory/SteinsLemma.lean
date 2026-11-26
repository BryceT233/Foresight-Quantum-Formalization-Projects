/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/SteinsLemma.lean: the direct part and the final convergence.
The direct part uses the regularized infimum to turn the likelihood estimate into a
contradiction without iterating the improvement of the alternatives.

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.Minimax
public import FQFP.CQM.Qudit.ResourceTheory.SteinsLemma.Converse
public import FQFP.CQM.Qudit.ResourceTheory.SteinsLemma.Likelihood

/-!
# The generalized quantum Stein lemma

For any type I error budget strictly between zero and one, the optimal type II error
exponent against the free states converges to the regularized resource relative entropy.
The direct part mixes a least favorable alternative, a repeated free block, and a
full-support free product. After rounding and pinching, the likelihood estimate
contradicts the regularized lower bound if the testing exponent falls below the limit.
-/

@[expose] public noncomputable section

open Filter
open scoped ENNReal Topology

namespace Qudit.FreeStateTheory

variable {H : Qudit}

private lemma minSpectrum_tensorPower (θ : Density H) (n : ℕ) :
    sInf (spectrum ℝ (θ.tensorPower n).op) = sInf (spectrum ℝ θ.op) ^ (n + 1) := by
  induction n with
  | zero =>
    rw [pow_one]
    rfl
  | succ n ih =>
    change sInf (spectrum ℝ (θ.tensor (θ.tensorPower n)).op) = _
    rw [Density.sInf_realSpectrum_tensor, ih]
    exact (pow_succ' _ (n + 1)).symm

private lemma one_third_le_mix (F : FreeStateSet H) (σ η θ : Density H)
    (hσ : σ ∈ F) (hη : η ∈ F) (hθ : θ ∈ F) :
    ∃ ω ∈ F, (1 / 3 : ℝ) • σ.op ≤ ω.op ∧ (1 / 3 : ℝ) • η.op ≤ ω.op ∧
      (1 / 3 : ℝ) • θ.op ≤ ω.op := by
  let u := η.mix (1 / 2) (by norm_num) (by norm_num) θ
  let ω := σ.mix (1 / 3) (by norm_num) (by norm_num) u
  have hu : u ∈ F := F.mix_mem hη hθ _ _ _
  have hop : ω.op = (1 / 3 : ℝ) • σ.op + (1 / 3 : ℝ) • η.op + (1 / 3 : ℝ) • θ.op := by
    change (1 / 3 : ℝ) • σ.op + (1 - 1 / 3 : ℝ) •
      ((1 / 2 : ℝ) • η.op + (1 - 1 / 2 : ℝ) • θ.op) = _
    module
  have h (ρ : Density H) : 0 ≤ (1 / 3 : ℝ) • ρ.op :=
    smul_nonneg (by norm_num) (LinearMap.nonneg_iff_isPositive.mpr ρ.positive)
  refine ⟨ω, F.mix_mem hσ hu _ _ _, ?_⟩
  rw [hop]
  exact ⟨(le_add_of_nonneg_right (h η)).trans (le_add_of_nonneg_right (h θ)),
    (le_add_of_nonneg_left (h σ)).trans (le_add_of_nonneg_right (h θ)),
    le_add_of_nonneg_left (add_nonneg (h σ) (h η))⟩

private lemma exists_comparison_reference (F : FreeStateTheory H) (θ : Density H)
    (hθ : θ ∈ F.free 0) {x L : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hLx : L = -Real.log x + Real.log 3)
    (hmin : sInf (spectrum ℝ θ.op) = x) (n : ℕ) (σ η : Density (tensorPower H n))
    (hσ : σ ∈ F.free n) (hη : η ∈ F.free n) :
    ∃ ω ∈ F.free n, IsStrictlyPositive ω.op ∧
      ∃ τ : Density (tensorPower H n), IsStrictlyPositive τ.op ∧
        τ.spectralValues.card ≤ n + 2 ∧ τ.op ≤ Real.exp L • ω.op ∧
        σ.op ≤ (3 * Real.exp L) • τ.op ∧ η.op ≤ (3 * Real.exp L) • τ.op := by
  obtain ⟨ω, hω, hs, he, hθp⟩ := one_third_le_mix (F.free n) σ η (θ.tensorPower n)
    hσ hη (F.tensorPower_mem hθ n)
  let P := Operator (tensorPower H n)
  have hpow₀ : (x ^ (n + 1) : ℝ) • (1 : P) ≤ (θ.tensorPower n).op := by
    rw [← Algebra.algebraMap_eq_smul_one]
    apply (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) (θ.tensorPower n).adjoint_op).mpr
    obtain ⟨i, hi⟩ := (θ.tensorPower n).exists_isLeast_eigenvalue
    rw [← hmin, ← minSpectrum_tensorPower θ n, hi.csInf_eq]
    exact hi.2
  have hpow : (x ^ (n + 1) / 3 : ℝ) • (1 : P) ≤ ω.op := by
    have h := smul_le_smul_of_nonneg_left hpow₀ (by norm_num : 0 ≤ (1 / 3 : ℝ))
    simpa only [smul_smul, one_div_mul_eq_div] using h.trans hθp
  have he₀ : Real.exp (-((n + 1 : ℝ) * L)) ≤ x ^ (n + 1) / 3 := calc
    _ = Real.exp ((n + 1 : ℝ) * Real.log x - (n + 1 : ℝ) * Real.log 3) := by
      rw [hLx]
      ring_nf
    _ ≤ Real.exp ((n + 1 : ℝ) * Real.log x - Real.log 3) := by
      apply Real.exp_le_exp.mpr
      have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) h3]
    _ = _ := by
      rw [Real.exp_sub, ← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log hx,
        Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hall : Real.exp (-((n + 1 : ℝ) * L)) • (1 : P) ≤ ω.op :=
    (smul_le_smul_of_nonneg_right he₀ zero_le_one).trans hpow
  have hωp : IsStrictlyPositive ω.op := IsStrictlyPositive.of_le
    (IsStrictlyPositive.smul (Real.exp_pos _) (isStrictlyPositive_one (A := P))) hall
  obtain ⟨τ, hτ, hcard, hlow, hupp⟩ := ω.exists_spectralRounding (N := n + 1) hL hωp (by
    rw [← Algebra.algebraMap_eq_smul_one] at hall
    have hv := (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) ω.adjoint_op).mp hall
    intro i
    rw [Nat.cast_add_one]
    exact hv _ (ω.realSpectrum_eq_range_eigenvalue ▸ Set.mem_range_self i))
  have dom {A : P} (h : (1 / 3 : ℝ) • A ≤ ω.op) : A ≤ (3 * Real.exp L) • τ.op := calc
    A = (3 * Real.exp L) • (Real.exp (-L) • ((1 / 3 : ℝ) • A)) := by
      rw [smul_smul, smul_smul, mul_assoc (3 : ℝ) (Real.exp L), ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]
      norm_num
    _ ≤ (3 * Real.exp L) • (Real.exp (-L) • ω.op) :=
      smul_le_smul_of_nonneg_left (smul_le_smul_of_nonneg_left h (Real.exp_pos _).le)
        (by positivity)
    _ ≤ _ := smul_le_smul_of_nonneg_left hlow (by positivity)
  exact ⟨ω, hω, hωp, τ, hτ, hcard, hupp, dom hs, dom he⟩

private lemma regularized_mul_le_relativeEntropyReal (F : FreeStateTheory H) (ρ : Density H)
    (n : ℕ) (σ : Density (tensorPower H n)) (hσ : σ ∈ F.free n)
    (ha : (ρ.tensorPower n).AbsolutelyContinuous σ) :
    (F.regularizedRelativeEntropy ρ : ℝ) * (n + 1) ≤ (ρ.tensorPower n).relativeEntropyReal σ := by
  have h := F.regularizedRelativeEntropy_le_div ρ (n := n + 1) (by positivity)
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_natCast, Nat.cast_add_one] at h
  have ht := (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mp h
  refine ht.trans ?_
  change ((F.free n).relativeEntropy (ρ.tensorPower n) : ℝ) ≤ _
  rw [← ENNReal.coe_toReal, (F.free n).coe_relativeEntropy,
    ← (ρ.tensorPower n).toReal_relativeEntropy σ ha]
  apply ENNReal.toReal_mono (((ρ.tensorPower n).relativeEntropy_ne_top_iff σ).mpr ha)
  exact iInf_le (fun η : F.free n => (ρ.tensorPower n).relativeEntropy η) ⟨σ, hσ⟩

private lemma spectralValues_card_pos (σ : Density H) : 0 < σ.spectralValues.card := by
  classical
  obtain ⟨i, _⟩ := σ.exists_isLeast_eigenvalue
  exact Finset.card_pos.mpr ⟨σ.eigenvalue i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

private lemma relativeEntropyReal_le_pinched_add (ρ σ : Density H) (hσ : IsStrictlyPositive σ.op) :
    ρ.relativeEntropyReal σ ≤ (σ.pinching.map ρ).relativeEntropyReal σ +
      Real.log σ.spectralValues.card := by
  have h (τ : Density H) : τ.AbsolutelyContinuous σ :=
    (τ.absolutelyContinuous_iff_support_le σ).mpr
      ((σ.isStrictlyPositive_iff_support_eq_top.mp hσ).symm ▸ le_top)
  have hp := ρ.absolutelyContinuous_pinching σ
  rw [← ρ.toReal_relativeEntropy σ (h ρ), ρ.pinching_pythagoras σ,
    ENNReal.toReal_add ((ρ.relativeEntropy_ne_top_iff _).mpr hp)
      (((σ.pinching.map ρ).relativeEntropy_ne_top_iff _).mpr (h _)),
    (σ.pinching.map ρ).toReal_relativeEntropy σ (h _)]
  have hlog : 0 ≤ Real.log σ.spectralValues.card := by
    apply Real.log_nonneg
    exact_mod_cast spectralValues_card_pos σ
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (ρ.relativeEntropy_pinching_le_log_card σ)
  rw [ENNReal.toReal_ofReal hlog] at hh
  linarith

private lemma eventually_lt_typeIIErrorExponent (F : FreeStateTheory H) (ρ : Density H)
    {ε : unitInterval} (hε : 0 < ε) (hε₁ : ε < 1)
    {R : ℝ} (hR : R < F.regularizedRelativeEntropy ρ) :
    ∀ᶠ n in atTop, R < F.typeIIErrorExponent ρ ε n := by
  let D : ℝ := F.regularizedRelativeEntropy ρ
  let lo := (R + D) / 2
  let hi := D + ε.val * (D - lo) / 2
  have he : 0 < (ε : ℝ) := hε
  have hlo : R < lo := by dsimp [lo]; linarith
  have hld : lo < D := by dsimp [lo]; linarith
  have hdh : D < hi := lt_add_of_pos_right _ (div_pos (mul_pos he (sub_pos.mpr hld)) (by norm_num))
  have hmix : hi - ε.val * (hi - lo) < D := by
    dsimp [hi]
    nlinarith [mul_pos he (sub_pos.mpr hld), mul_nonneg (sq_nonneg ε.val) (sub_nonneg.mpr hld.le)]
  obtain ⟨m, μ, α, hμ, hμc, hm⟩ := F.exists_free_block_sandwichedRenyiRate_lt ρ hdh
  obtain ⟨θ, hθ, hθp⟩ := (F.free 0).exists_strictlyPositive
  have hθc : ρ.AbsolutelyContinuous θ := (ρ.absolutelyContinuous_iff_support_le θ).mpr
    ((θ.isStrictlyPositive_iff_support_eq_top.mp hθp).symm ▸ le_top)
  let x := sInf (spectrum ℝ θ.op)
  have hx : 0 < x := θ.isStrictlyPositive_iff_sInf_realSpectrum_pos.mp hθp
  have hx₁ : x ≤ 1 := by
    obtain ⟨i, hi⟩ := θ.exists_isLeast_eigenvalue
    change sInf (spectrum ℝ θ.op) ≤ 1
    rw [hi.csInf_eq]
    exact θ.eigenvalue_le_one i
  let L := -Real.log x + Real.log 3
  have hL : 0 < L := add_pos_of_nonneg_of_pos (neg_nonneg.mpr (Real.log_nonpos hx.le hx₁))
    (Real.log_pos (by norm_num))
  let C := 3 * Real.exp L
  have hC : 0 < C := by positivity
  let a := α.val - 1
  have ha : 0 < a := sub_pos.mpr α.property
  let B := (m + 1 : ℝ) * (ρ.sandwichedRenyiRelativeEntropy θ α).toReal
  let K := Real.exp (a * (B + Real.log C)) / a + L
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n + 2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    convert h using 2
    simp only [one_mul, pow_one]
    congr 1
    ring
  have herr : Tendsto (fun n : ℕ => (K + Real.log (n + 2 : ℝ)) / (n + 1)) atTop (𝓝 0) := by
    simpa only [add_div, zero_add] using (tendsto_const_nhds (x := K)).div_atTop hn |>.add hlog
  have hRdiff := hn.const_mul_atTop (sub_pos.mpr hlo)
  filter_upwards [(tendsto_atTop.mp hRdiff (Real.log C + 1)),
    herr.eventually (gt_mem_nhds (sub_pos.mpr hmix))] with n hbig hsmall
  by_contra! hbad
  let ρn := ρ.tensorPower n
  let N : ℝ := n + 1
  have hN : 0 < N := by positivity
  obtain ⟨σ, hσ, htest⟩ := ρn.exists_leastFavorableAlternative ε (F.free n).nonempty
    (F.free n).isCompact (F.free n).convex
  obtain ⟨η, hη, hηc, hrate⟩ := F.exists_free_sandwichedRenyi_le_of_block ρ α m μ hμ hμc θ hθ hθc n
  obtain ⟨ω, hω, hωp, τ, hτ, hcard, hupp, hσdom, hηdom⟩ :=
    F.exists_comparison_reference θ hθ hx hL rfl rfl n σ η hσ hη
  let β : ℝ := ρn.optimalTypeIIError ε (F.free n)
  have hβ : 0 < β := F.optimalTypeIIError_pos ρ hε₁ n
  have hbad' : -Real.log β ≤ R * N := (div_le_iff₀ hN).mp hbad
  have htest' : C * Real.exp (-(N * lo)) < (ρn.optimalTypeIIError ε {σ} : ℝ) := by
    rw [htest]
    change C * Real.exp (-(N * lo)) < β
    calc
      _ = Real.exp (Real.log C - N * lo) := by rw [Real.exp_sub, Real.exp_log hC, Real.exp_neg,
        div_eq_mul_inv]
      _ < Real.exp (Real.log β) := Real.exp_lt_exp.mpr (by
        change Real.log C + 1 ≤ (lo - R) * N at hbig
        nlinarith)
      _ = β := Real.exp_log hβ
  have hcut := ρn.relativeEntropyReal_pinching_le_of_test_and_renyi τ σ η hτ ε α hηc hC
    (mul_le_mul_of_nonneg_left (hld.trans hdh).le hN.le) hσdom hηdom htest'
  have hterm :
      Real.exp (a * ((ρn.sandwichedRenyiRelativeEntropy η α).toReal + Real.log C - N * hi)) / a ≤
        Real.exp (a * (B + Real.log C)) / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ ha.le
    have hh : (ρn.sandwichedRenyiRelativeEntropy η α).toReal ≤ N * hi + B :=
      hrate.trans (add_le_add_left (mul_le_mul_of_nonneg_left hm.le hN.le) B)
    linarith only [hh]
  have hac : ρn.AbsolutelyContinuous ω := (ρn.absolutelyContinuous_iff_support_le ω).mpr
    ((ω.isStrictlyPositive_iff_support_eq_top.mp hωp).symm ▸ le_top)
  have hd := F.regularized_mul_le_relativeEntropyReal ρ n ω hω hac
  have hpert := ρn.relativeEntropyReal_le_of_reference_le_smul ω τ (Real.exp_pos L) hωp hτ hupp
  rw [Real.log_exp] at hpert
  have hpinch := relativeEntropyReal_le_pinched_add ρn τ hτ
  have hlogcard : Real.log τ.spectralValues.card ≤ Real.log (n + 2 : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast spectralValues_card_pos τ)
    exact_mod_cast hcard
  have hsum : D * N ≤ N * (hi - ε.val * (hi - lo)) + (K + Real.log (n + 2 : ℝ)) := by
    dsimp only [K]
    nlinarith
  have hsmall' := (div_lt_iff₀ hN).mp hsmall
  nlinarith

/-- Generalized quantum Stein lemma for tensor-closed convex free sets, in nats per copy. -/
theorem tendsto_typeIIErrorExponent (F : FreeStateTheory H) (ρ : Density H)
    {ε : unitInterval} (hε : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (F.typeIIErrorExponent ρ ε) atTop (𝓝 (F.regularizedRelativeEntropy ρ : ℝ)) :=
  tendsto_order.mpr ⟨fun _ hR => F.eventually_lt_typeIIErrorExponent ρ hε hε₁ hR,
    fun _ hR => F.eventually_typeIIErrorExponent_lt ρ hε₁ hR⟩

/-- The generalized Stein limit in the extended nonnegative reals, with the same
normalization as the relative entropy of resource. -/
theorem tendsto_hypothesisTestingRelativeEntropy_div (F : FreeStateTheory H) (ρ : Density H)
    {ε : unitInterval} (hε : 0 < ε) (hε₁ : ε < 1) :
    Tendsto (fun n => (ρ.tensorPower n).hypothesisTestingRelativeEntropy ε (F.free n) / (n + 1))
      atTop (𝓝 (F.regularizedRelativeEntropy ρ : ℝ≥0∞)) := by
  have h := ENNReal.tendsto_ofReal (F.tendsto_typeIIErrorExponent ρ hε hε₁)
  rw [ENNReal.ofReal_coe_nnreal] at h
  refine h.congr fun n => ?_
  rw [(ρ.tensorPower n).hypothesisTestingRelativeEntropy_eq_of_pos _ _
    (F.optimalTypeIIError_pos ρ hε₁ n), typeIIErrorExponent,
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]

end Qudit.FreeStateTheory
