/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/SteinsLemma.lean: the block alternative and the converse bound
in Lemma 6 and GeneralizedQSteinsLemma.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.LimitAtOne
public import FQFP.CQM.Qudit.Entropy.SandwichedRenyi.Tensor
public import FQFP.CQM.Qudit.Measurement.HypothesisTesting.RenyiBound
public import FQFP.CQM.Qudit.ResourceTheory.RelativeEntropy

/-!
# Converse of the generalized quantum Stein lemma

The type II exponent at a fixed type I error budget below one is bounded above asymptotically
by the regularized resource relative entropy. Independent repetitions of a fixed free block
give a bound at any Rényi order above one. Single-site free states fill the fewer than one
block of remaining sites, giving a bounded correction. Taking the order down to one and
optimizing the block gives the regularized bound.
-/

@[expose] public noncomputable section

open CategoryTheory DaggerCategory Filter
open scoped ENNReal Topology

namespace Qudit.FreeStateTheory

variable {H : Qudit}

/-- The negative log of the optimal type II error against the free states, in nats per copy.
The block has `n + 1` sites. The error is strictly positive whenever `ε < 1`. -/
def typeIIErrorExponent (F : FreeStateTheory H) (ρ : Density H) (ε : unitInterval) (n : ℕ) : ℝ :=
  -Real.log ((ρ.tensorPower n).optimalTypeIIError ε (F.free n)) / (n + 1)

/-- Testing a tensor power against its free set always has positive error below unit budget. -/
lemma optimalTypeIIError_pos (F : FreeStateTheory H) (ρ : Density H) {ε : unitInterval}
    (hε : ε < 1) (n : ℕ) : 0 < (ρ.tensorPower n).optimalTypeIIError ε (F.free n) := by
  obtain ⟨σ, hσ, hs⟩ := (F.free n).exists_absolutelyContinuous (ρ.tensorPower n)
  exact (ρ.tensorPower n).optimalTypeIIError_pos_of_absolutelyContinuous hε hσ hs

/-- The normalized type II exponent is nonnegative. -/
lemma typeIIErrorExponent_nonneg (F : FreeStateTheory H) (ρ : Density H)
    (ε : unitInterval) (n : ℕ) : 0 ≤ F.typeIIErrorExponent ρ ε n := by
  apply div_nonneg _ (by positivity)
  let β := (ρ.tensorPower n).optimalTypeIIError ε (F.free n)
  exact neg_nonneg.mpr (Real.log_nonpos β.2.1 β.2.2)

private lemma renyi_ne_top {K : Qudit} {ρ σ : Density K}
    (h : ρ.AbsolutelyContinuous σ) (α : Set.Ioi (1 : ℝ)) :
    ρ.sandwichedRenyiRelativeEntropy σ α ≠ ⊤ :=
  fun ht => ((ρ.sandwichedRenyiRelativeEntropy_eq_top_iff σ α).mp ht) h

private lemma renyi_tensor_toReal {K : Qudit} (ρ σ : Density H) (τ ω : Density K)
    (h₁ : ρ.AbsolutelyContinuous σ) (h₂ : τ.AbsolutelyContinuous ω) (α : Set.Ioi (1 : ℝ)) :
    ((ρ.tensor τ).sandwichedRenyiRelativeEntropy (σ.tensor ω) α).toReal =
      (ρ.sandwichedRenyiRelativeEntropy σ α).toReal +
        (τ.sandwichedRenyiRelativeEntropy ω α).toReal := by
  rw [Density.sandwichedRenyiRelativeEntropy_tensor, ENNReal.toReal_add
    (renyi_ne_top h₁ α) (renyi_ne_top h₂ α)]

private lemma support_tensorPower {ρ σ : Density H} (h : ρ.AbsolutelyContinuous σ) (n : ℕ) :
    (ρ.tensorPower n).AbsolutelyContinuous (σ.tensorPower n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact h.tensor ih

private lemma renyi_tensorPower (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ)
    (α : Set.Ioi (1 : ℝ)) (n : ℕ) :
    ((ρ.tensorPower n).sandwichedRenyiRelativeEntropy (σ.tensorPower n) α).toReal =
      (n + 1 : ℝ) * (ρ.sandwichedRenyiRelativeEntropy σ α).toReal := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_add, one_mul] using
      (show ((ρ.tensorPower 0).sandwichedRenyiRelativeEntropy (σ.tensorPower 0) α).toReal =
        (ρ.sandwichedRenyiRelativeEntropy σ α).toReal from rfl)
  | succ n ih =>
    change ((ρ.tensor (ρ.tensorPower n)).sandwichedRenyiRelativeEntropy
      (σ.tensor (σ.tensorPower n)) α).toReal = _
    rw [renyi_tensor_toReal _ _ _ _ h (support_tensorPower h n), ih, Nat.cast_succ]
    ring

/-- Given a supported free block, every register admits a supported free alternative with
Rényi divergence at most the rate of that block times the register length, plus a fixed
error for the remaining sites. -/
theorem exists_free_sandwichedRenyi_le_of_block (F : FreeStateTheory H) (ρ : Density H)
    (α : Set.Ioi (1 : ℝ)) (m : ℕ) (σ : Density (tensorPower H m))
    (hσ : σ ∈ F.free m) (ha : (ρ.tensorPower m).AbsolutelyContinuous σ)
    (τ : Density H) (hτ : τ ∈ F.free 0) (ht : ρ.AbsolutelyContinuous τ) (n : ℕ) :
    ∃ ω ∈ F.free n, (ρ.tensorPower n).AbsolutelyContinuous ω ∧
      ((ρ.tensorPower n).sandwichedRenyiRelativeEntropy ω α).toReal ≤
        (n + 1 : ℝ) * (((ρ.tensorPower m).sandwichedRenyiRelativeEntropy σ α).toReal / (m + 1)) +
          (m + 1 : ℝ) * (ρ.sandwichedRenyiRelativeEntropy τ α).toReal := by
  let d := ((ρ.tensorPower m).sandwichedRenyiRelativeEntropy σ α).toReal
  let r := d / (m + 1 : ℝ)
  let c := (ρ.sandwichedRenyiRelativeEntropy τ α).toReal
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hmr : (m + 1 : ℝ) * r = d := mul_div_cancel₀ _ hm.ne'
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hr : 0 ≤ r := div_nonneg ENNReal.toReal_nonneg hm.le
  change ∃ ω ∈ F.free n, (ρ.tensorPower n).AbsolutelyContinuous ω ∧
    ((ρ.tensorPower n).sandwichedRenyiRelativeEntropy ω α).toReal ≤
      (n + 1 : ℝ) * r + (m + 1 : ℝ) * c
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · refine ⟨τ.tensorPower n, F.tensorPower_mem hτ n, support_tensorPower ht n, ?_⟩
      rw [renyi_tensorPower ρ τ ht α]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hnm.le) hc).trans
        (le_add_of_nonneg_left (mul_nonneg (by positivity) hr))
    · exact ⟨σ, hσ, ha, hmr ▸ le_add_of_nonneg_right (mul_nonneg hm.le hc)⟩
    · obtain ⟨k, hk⟩ : ∃ k, n = k + m + 1 := ⟨n - (m + 1), by lia⟩
      have hkn : k < n := by lia
      obtain ⟨ω, hω, haw, hb⟩ := ih k hkn
      subst n
      let U := tensorPowerAppend H m k
      refine ⟨(σ.tensor ω).map U, F.append_mem hσ hω, ?_, ?_⟩
      · rw [← ρ.tensorPower_append m k]
        exact (Density.absolutelyContinuous_map_iff _ _ U).mpr (ha.tensor haw)
      · rw [← ρ.tensorPower_append m k,
          Density.sandwichedRenyiRelativeEntropy_map_isometry,
          renyi_tensor_toReal _ _ _ _ ha haw]
        change d + ((ρ.tensorPower k).sandwichedRenyiRelativeEntropy ω α).toReal ≤ _
        have hcast : (↑(k + m + 1) : ℝ) + 1 = (↑k + 1) + (↑m + 1) := by push_cast; ring
        rw [hcast, add_mul, hmr]
        linarith

/-- Any rate above the regularized divergence exceeds a finite-block sandwiched Rényi rate
at some order greater than one. The free alternative can be chosen with support inclusion. -/
theorem exists_free_block_sandwichedRenyiRate_lt (F : FreeStateTheory H) (ρ : Density H)
    {R : ℝ} (hR : (F.regularizedRelativeEntropy ρ : ℝ) < R) :
    ∃ (m : ℕ) (σ : Density (tensorPower H m)) (α : Set.Ioi (1 : ℝ)), σ ∈ F.free m ∧
      (ρ.tensorPower m).AbsolutelyContinuous σ ∧
      ((ρ.tensorPower m).sandwichedRenyiRelativeEntropy σ α).toReal / (m + 1) < R := by
  have ht := (NNReal.tendsto_coe.mpr (F.tendsto_relativeEntropy_div ρ)).comp
    (tendsto_add_atTop_nat 1)
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hR)).exists
  change ((F.relativeEntropy ρ (m + 1) / (↑(m + 1) : NNReal) : NNReal) : ℝ) < R at hm
  rw [NNReal.coe_div, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one] at hm
  obtain ⟨σ, hσ, he⟩ := (F.free m).exists_relativeEntropy_eq (ρ.tensorPower m)
  have hne : (ρ.tensorPower m).relativeEntropy σ ≠ ⊤ := he.trans_ne ENNReal.coe_ne_top
  have ha := ((ρ.tensorPower m).relativeEntropy_ne_top_iff σ).mp hne
  have hD : ((ρ.tensorPower m).relativeEntropy σ).toReal / (m + 1 : ℝ) < R := by
    rw [he, ENNReal.coe_toReal]
    exact hm
  have hlim := ((ENNReal.tendsto_toReal hne).comp
    ((ρ.tensorPower m).tendsto_sandwichedRenyiRelativeEntropy_one σ)).div_const (m + 1 : ℝ)
  obtain ⟨α, hα⟩ := (hlim.eventually (gt_mem_nhds hD)).exists
  exact ⟨m, σ, α, hσ, ha, hα⟩

/-- For any fixed type I budget below one, every rate above the regularized resource
relative entropy eventually exceeds the optimal type II exponent. -/
theorem eventually_typeIIErrorExponent_lt (F : FreeStateTheory H) (ρ : Density H)
    {ε : unitInterval} (hε : ε < 1) {R : ℝ} (hR : (F.regularizedRelativeEntropy ρ : ℝ) < R) :
    ∀ᶠ n in atTop, F.typeIIErrorExponent ρ ε n < R := by
  obtain ⟨m, σ, α, hσ, ha, hrate⟩ := F.exists_free_block_sandwichedRenyiRate_lt ρ hR
  obtain ⟨τ, hτ, ht⟩ := (F.free 0).exists_absolutelyContinuous ρ
  let r := ((ρ.tensorPower m).sandwichedRenyiRelativeEntropy σ α).toReal / (m + 1)
  let C := (m + 1 : ℝ) * (ρ.sandwichedRenyiRelativeEntropy τ α).toReal +
    (α.val / (α.val - 1)) * (-Real.log (1 - ε.val))
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => r + C / (n + 1)) atTop (𝓝 r) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hn)
  filter_upwards [hlim.eventually (gt_mem_nhds hrate)] with n hnR
  obtain ⟨ω, hω, hw, hb⟩ := F.exists_free_sandwichedRenyi_le_of_block ρ α m σ hσ ha τ hτ ht n
  have hp : 0 < (ρ.tensorPower n).optimalTypeIIError ε {ω} :=
    (ρ.tensorPower n).optimalTypeIIError_pos_of_absolutelyContinuous hε (Set.mem_singleton _) hw
  have hβ := (ρ.tensorPower n).optimalTypeIIError_mono ε (Set.singleton_subset_iff.mpr hω)
  have hl := neg_le_neg (Real.log_le_log hp hβ)
  have hfin := (ρ.tensorPower n).neg_log_optimalTypeIIError_singleton_le_sandwichedRenyi ω ε hε α hw
  refine lt_of_le_of_lt ?_ hnR
  unfold typeIIErrorExponent
  have hn₀ : (0 : ℝ) < n + 1 := by positivity
  apply (div_le_iff₀ hn₀).mpr
  rw [add_mul, div_mul_cancel₀ _ hn₀.ne']
  change ((ρ.tensorPower n).sandwichedRenyiRelativeEntropy ω α).toReal ≤
    (n + 1 : ℝ) * r + (m + 1 : ℝ) * (ρ.sandwichedRenyiRelativeEntropy τ α).toReal at hb
  dsimp only [C]
  linarith

/-- The converse bound for the generalized quantum Stein lemma. -/
theorem limsup_typeIIErrorExponent_le_regularizedRelativeEntropy (F : FreeStateTheory H)
    (ρ : Density H) {ε : unitInterval} (hε : ε < 1) :
    atTop.limsup (F.typeIIErrorExponent ρ ε) ≤ F.regularizedRelativeEntropy ρ := by
  have hlow : (atTop : Filter ℕ).IsCoboundedUnder (· ≤ ·) (F.typeIIErrorExponent ρ ε) :=
    isCoboundedUnder_le_of_le atTop (F.typeIIErrorExponent_nonneg ρ ε)
  have hupp : (atTop : Filter ℕ).IsBoundedUnder (· ≤ ·) (F.typeIIErrorExponent ρ ε) :=
    ⟨(F.regularizedRelativeEntropy ρ : ℝ) + 1, (F.eventually_typeIIErrorExponent_lt ρ hε
      (lt_add_of_pos_right _ zero_lt_one)).mono fun _ hn => hn.le⟩
  exact (limsup_le_iff hlow hupp).mpr fun _ hR => F.eventually_typeIIErrorExponent_lt ρ hε hR

end Qudit.FreeStateTheory
