/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/FreeState.lean: relative entropy to free states, subadditivity
on tensor powers, and the regularized limit.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.DataProcessing
public import FQFP.CQM.Qudit.Entropy.Relative.Continuity
public import FQFP.CQM.Qudit.Entropy.Relative.Tensor
public import FQFP.CQM.Qudit.ResourceTheory.FreeState
public import Mathlib.Analysis.Subadditive

/-!
# Relative entropy of resource

The relative entropy of resource minimizes the Umegaki divergence over free alternatives.
Full support of one free alternative makes this infimum finite. Tensor closure and additivity
of the divergence give the regularized limit via Fekete's lemma.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology NNReal ENNReal

namespace Qudit.FreeStateSet

variable {H K : Qudit}

/-- The extended divergence to a free set, as an infimum over all free alternatives. -/
def relativeEntropyInf (F : FreeStateSet H) (ρ : Density H) : ℝ≥0∞ :=
  ⨅ σ : F, ρ.relativeEntropy σ

/-- A full-support free alternative ensures finite divergence to the free set. -/
lemma relativeEntropyInf_ne_top (F : FreeStateSet H) (ρ : Density H) :
    F.relativeEntropyInf ρ ≠ ⊤ := by
  obtain ⟨σ, hσ, h⟩ := F.exists_absolutelyContinuous ρ
  exact ne_top_of_le_ne_top ((ρ.relativeEntropy_ne_top_iff σ).mpr h)
    (iInf_le (fun τ : F => ρ.relativeEntropy τ) ⟨σ, hσ⟩)

/-- Relative entropy of resource, in nats. -/
def relativeEntropy (F : FreeStateSet H) (ρ : Density H) : ℝ≥0 :=
  (F.relativeEntropyInf ρ).toNNReal

/-- The finite and extended values of the relative entropy of resource coincide. -/
lemma coe_relativeEntropy (F : FreeStateSet H) (ρ : Density H) :
    (F.relativeEntropy ρ : ℝ≥0∞) = F.relativeEntropyInf ρ :=
  ENNReal.coe_toNNReal (F.relativeEntropyInf_ne_top ρ)

/-- A free alternative attains the minimum relative entropy. -/
theorem exists_relativeEntropy_eq (F : FreeStateSet H) (ρ : Density H) :
    ∃ σ ∈ F, ρ.relativeEntropy σ = (F.relativeEntropy ρ : ℝ≥0∞) := by
  have hs := ρ.lowerSemicontinuous_relativeEntropy.lowerSemicontinuousOn (F : Set (Density H))
  obtain ⟨σ, hσ, hm⟩ := hs.exists_isMinOn F.nonempty F.isCompact
  refine ⟨σ, hσ, ?_⟩
  rw [F.coe_relativeEntropy]
  exact le_antisymm (le_iInf fun τ : F => hm τ.2) (iInf_le _ (⟨σ, hσ⟩ : F))

/-- Relative entropy of resource vanishes exactly on free states. -/
theorem relativeEntropy_eq_zero_iff (F : FreeStateSet H) (ρ : Density H) :
    F.relativeEntropy ρ = 0 ↔ ρ ∈ F := by
  constructor
  · intro h
    obtain ⟨σ, hσ, he⟩ := F.exists_relativeEntropy_eq ρ
    rw [h, ENNReal.coe_zero, Density.relativeEntropy_eq_zero_iff] at he
    exact he.symm ▸ hσ
  · intro h
    rw [← ENNReal.coe_inj, ENNReal.coe_zero, F.coe_relativeEntropy]
    exact le_antisymm ((iInf_le _ (⟨ρ, h⟩ : F)).trans_eq ρ.relativeEntropy_self) bot_le

/-- A free-preserving channel cannot increase relative entropy of resource. -/
theorem relativeEntropy_map_le (F : FreeStateSet H) (G : FreeStateSet K) (Φ : QuantumChannel H K)
    (hΦ : Set.MapsTo Φ.map (F : Set (Density H)) (G : Set (Density K))) (ρ : Density H) :
    G.relativeEntropy (Φ.map ρ) ≤ F.relativeEntropy ρ := by
  rw [← ENNReal.coe_le_coe, G.coe_relativeEntropy, F.coe_relativeEntropy]
  refine le_iInf fun σ : F => ?_
  exact (iInf_le (fun τ : G => (Φ.map ρ).relativeEntropy τ) ⟨Φ.map σ, hΦ σ.2⟩).trans
    (Φ.relativeEntropy_map_le ρ σ)

end Qudit.FreeStateSet

namespace Qudit.FreeStateTheory

variable {H : Qudit}

/-- Divergence to the free set on `n` copies. The empty register has zero divergence. -/
def relativeEntropy (F : FreeStateTheory H) (ρ : Density H) : ℕ → ℝ≥0
  | 0 => 0
  | n + 1 => (F.free n).relativeEntropy (ρ.tensorPower n)

/-- The per-block divergences of independent copies form a subadditive sequence. -/
theorem subadditive_relativeEntropy (F : FreeStateTheory H) (ρ : Density H) :
    Subadditive fun n => (F.relativeEntropy ρ n : ℝ) := by
  intro m n
  cases m with
  | zero => simp [relativeEntropy]
  | succ a =>
    cases n with
    | zero => simp [relativeEntropy]
    | succ b =>
      have hab : a + 1 + (b + 1) = (b + a + 1) + 1 := by lia
      rw [hab]
      change (((F.free (b + a + 1)).relativeEntropy _) : ℝ) ≤
        ((F.free a).relativeEntropy (ρ.tensorPower a) : ℝ) +
          ((F.free b).relativeEntropy (ρ.tensorPower b) : ℝ)
      rw [← NNReal.coe_add, NNReal.coe_le_coe, ← ENNReal.coe_le_coe, ENNReal.coe_add]
      simp only [FreeStateSet.coe_relativeEntropy, FreeStateSet.relativeEntropyInf]
      refine ENNReal.le_iInf_add_iInf fun (σ : F.free a) (τ : F.free b) => ?_
      let U := tensorPowerAppend H a b
      let ω : F.free (b + a + 1) := ⟨((σ : Density _).tensor τ).map U, F.append_mem σ.2 τ.2⟩
      refine (iInf_le _ ω).trans ?_
      change (ρ.tensorPower (b + a + 1)).relativeEntropy (((σ : Density _).tensor τ).map U) ≤ _
      rw [← ρ.tensorPower_append a b, Density.relativeEntropy_map_unitary,
        Density.relativeEntropy_tensor]

/-- The infimum of the per-copy relative entropies over positive block lengths. -/
def regularizedRelativeEntropy (F : FreeStateTheory H) (ρ : Density H) : ℝ≥0 :=
  ⟨(F.subadditive_relativeEntropy ρ).lim, by
    rw [Subadditive.lim]
    exact Real.sInf_nonneg (by rintro x ⟨n, hn, rfl⟩; positivity)⟩

private lemma bddBelow_relativeEntropy_div (F : FreeStateTheory H) (ρ : Density H) :
    BddBelow (Set.range fun n : ℕ => (F.relativeEntropy ρ n : ℝ) / n) :=
  ⟨0, by rintro x ⟨n, rfl⟩; positivity⟩

/-- Every positive block length gives an upper bound on the regularized relative entropy. -/
theorem regularizedRelativeEntropy_le_div (F : FreeStateTheory H) (ρ : Density H)
    {n : ℕ} (hn : n ≠ 0) :
    F.regularizedRelativeEntropy ρ ≤ F.relativeEntropy ρ n / n := by
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_natCast]
  exact (F.subadditive_relativeEntropy ρ).lim_le_div (F.bddBelow_relativeEntropy_div ρ) hn

/-- A free state has zero regularized relative entropy. -/
theorem regularizedRelativeEntropy_eq_zero_of_mem (F : FreeStateTheory H) {ρ : Density H}
    (hρ : ρ ∈ F.free 0) : F.regularizedRelativeEntropy ρ = 0 := by
  apply le_antisymm ((F.regularizedRelativeEntropy_le_div ρ one_ne_zero).trans_eq ?_) zero_le
  have h : F.relativeEntropy ρ 1 = 0 := ((F.free 0).relativeEntropy_eq_zero_iff ρ).mpr hρ
  simpa only [Nat.cast_one, div_one] using h

/-- The relative entropy per copy converges to the regularized relative entropy. -/
theorem tendsto_relativeEntropy_div (F : FreeStateTheory H) (ρ : Density H) :
    Tendsto (fun n : ℕ => F.relativeEntropy ρ n / n) atTop
      (𝓝 (F.regularizedRelativeEntropy ρ)) := by
  rw [← NNReal.tendsto_coe]
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  exact (F.subadditive_relativeEntropy ρ).tendsto_lim (F.bddBelow_relativeEntropy_div ρ)

/-- The convergence also holds for the original extended divergence on positive block lengths. -/
theorem tendsto_relativeEntropyInf_div (F : FreeStateTheory H) (ρ : Density H) :
    Tendsto (fun n : ℕ => (F.free n).relativeEntropyInf (ρ.tensorPower n) / (n + 1 : ℝ≥0∞))
      atTop (𝓝 (F.regularizedRelativeEntropy ρ : ℝ≥0∞)) := by
  have ht := (ENNReal.tendsto_coe.mpr (F.tendsto_relativeEntropy_div ρ)).comp
    (tendsto_add_atTop_nat 1)
  refine ht.congr fun n => ?_
  change ((F.relativeEntropy ρ (n + 1) / (↑(n + 1) : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = _
  rw [ENNReal.coe_div (by positivity), ENNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
    relativeEntropy, FreeStateSet.coe_relativeEntropy]

end Qudit.FreeStateTheory
