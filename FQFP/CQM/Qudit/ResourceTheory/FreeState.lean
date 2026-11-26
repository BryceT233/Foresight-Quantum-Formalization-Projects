/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/

/-
leanprover-community/physlib @ 101e93cf91f0304f5ab9bfbfdec6cebcc031f7cd
QuantumInfo/ResourceTheory/FreeState.lean: free states, global robustness, and
asymptotically nongenerating operations.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Channel.Basic
public import FQFP.CQM.Qudit.State.StrictPositivity
public import FQFP.CQM.Qudit.State.TensorPower
public import FQFP.CQM.Qudit.State.Topology
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Free states on finite quantum registers

A free set on a register is closed and convex and contains a full-support state. A resource
theory specifies such a set at each positive block length, compatible with appending independent
blocks. This allows the free sets to depend on the tensor decomposition of the register.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Filter
open scoped Topology NNReal

namespace Qudit

/-- A closed convex set of density states containing at least one full-support state. -/
structure FreeStateSet (H : Qudit) where
  /-- The free density states. -/
  carrier : Set (Density H)
  /-- The free states are closed in trace distance. -/
  isClosed : IsClosed carrier
  /-- The underlying operators of the free states form a real convex set. -/
  convex : Convex ℝ (Density.op '' carrier)
  /-- A free state with full support exists. -/
  exists_strictlyPositive : ∃ σ ∈ carrier, IsStrictlyPositive (Density.op σ)

namespace FreeStateSet

variable {H : Qudit}

instance : SetLike (FreeStateSet H) (Density H) where
  coe := carrier
  coe_injective := by
    rintro ⟨s, hs, hc, hp⟩ ⟨t, ht, hd, hq⟩ h
    cases h
    rfl

/-- A free set is nonempty because it contains a full-support state. -/
lemma nonempty (F : FreeStateSet H) : (F : Set (Density H)).Nonempty :=
  F.exists_strictlyPositive.imp fun _ h => h.1

/-- The free states form a compact subset of the density-operator space. -/
lemma isCompact (F : FreeStateSet H) : IsCompact (F : Set (Density H)) :=
  F.isClosed.isCompact

/-- Every state is supported by some free alternative. -/
lemma exists_absolutelyContinuous (F : FreeStateSet H) (ρ : Density H) :
    ∃ σ ∈ F, ρ.AbsolutelyContinuous σ := by
  obtain ⟨σ, hσ, hp⟩ := F.exists_strictlyPositive
  refine ⟨σ, hσ, (ρ.absolutelyContinuous_iff_support_le σ).mpr ?_⟩
  rw [σ.isStrictlyPositive_iff_support_eq_top.mp hp]
  exact le_top

/-- A convex mixture of free states is free. -/
lemma mix_mem (F : FreeStateSet H) {ρ σ : Density H} (hρ : ρ ∈ F) (hσ : σ ∈ F)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : ρ.mix p hp₀ hp₁ σ ∈ F := by
  obtain ⟨τ, hτ, he⟩ := F.convex (Set.mem_image_of_mem _ hρ) (Set.mem_image_of_mem _ hσ)
    hp₀ (sub_nonneg.mpr hp₁) (by ring)
  have heq : τ = ρ.mix p hp₀ hp₁ σ := Density.ext (he.trans (Density.op_mix p hp₀ hp₁ ρ σ).symm)
  exact heq ▸ hτ

/-- The global robustness is the least amount of arbitrary noise needed to make a state free.
The parameter is the ratio of noise to the original state. -/
def globalRobustness (F : FreeStateSet H) (ρ : Density H) : ℝ≥0 :=
  sInf {s | ∃ σ, ρ.mix (1 + (s : ℝ))⁻¹ (by positivity)
    (inv_le_one_of_one_le₀ (le_add_of_nonneg_right s.2)) σ ∈ F}

/-- A finite amount of noise suffices for every state. -/
theorem exists_mix_mem (F : FreeStateSet H) (ρ : Density H) :
    ∃ (s : ℝ≥0) (τ : Density H), ρ.mix (1 + (s : ℝ))⁻¹ (by positivity)
      (inv_le_one_of_one_le₀ (le_add_of_nonneg_right s.2)) τ ∈ F := by
  obtain ⟨σ, hσ, hfull⟩ := F.exists_strictlyPositive
  let m := sInf (spectrum ℝ σ.op)
  have hm : 0 < m := σ.isStrictlyPositive_iff_sInf_realSpectrum_pos.mp hfull
  let s : ℝ≥0 := ⟨m⁻¹, (inv_pos.mpr hm).le⟩
  let p : ℝ := (1 + (s : ℝ))⁻¹
  have hs : 1 < 1 + (s : ℝ) := lt_add_of_pos_right _ (inv_pos.mpr hm)
  have hp₀ : 0 < p := inv_pos.mpr (zero_lt_one.trans hs)
  have hp₁ : p < 1 := inv_lt_one_of_one_lt₀ hs
  have hpm : p ≤ m := calc
    p ≤ (m⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hm) (le_add_of_nonneg_left zero_le_one)
    _ = m := inv_inv _
  have hρ : ρ.op ≤ 1 := (CFC.le_one_iff (R := ℝ) (p := IsSelfAdjoint) ρ.op ρ.adjoint_op).mpr (by
    rw [ρ.realSpectrum_eq_range_eigenvalue]
    rintro x ⟨i, rfl⟩
    exact ρ.eigenvalue_le_one i)
  have hdom : p • ρ.op ≤ σ.op := calc
    _ ≤ p • (1 : Operator H) := smul_le_smul_of_nonneg_left hρ hp₀.le
    _ = algebraMap ℝ (Operator H) p := (Algebra.algebraMap_eq_smul_one p).symm
    _ ≤ σ.op := (algebraMap_le_iff_le_spectrum (p := IsSelfAdjoint) σ.adjoint_op).mpr fun x hx =>
      hpm.trans (csInf_le ⟨0, fun _ hy => by
        rw [σ.realSpectrum_eq_range_eigenvalue] at hy
        obtain ⟨i, rfl⟩ := hy
        exact σ.eigenvalue_nonneg i⟩ hx)
  let A : Operator H := σ.op - (p : ℂ) • ρ.op
  have hA : A.IsPositive := by
    apply LinearMap.nonneg_iff_isPositive.mp
    change (0 : Operator H) ≤ σ.op - (p : ℂ) • ρ.op
    rw [sub_nonneg]
    exact hdom
  have htr : A.trace = ((1 - p : ℝ) : ℂ) := by
    change (LinearMap.trace ℂ H.state) (σ.op - (p : ℂ) • ρ.op) = _
    rw [map_sub, map_smul]
    change σ.op.trace - (p : ℂ) • ρ.op.trace = _
    simp [σ.trace_one, ρ.trace_one]
  have ht : ((1 - p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hp₁).ne'
  let τ := Density.normalize hA htr ht
  refine ⟨s, τ, ?_⟩
  have he : ρ.mix p hp₀.le hp₁.le τ = σ := by
    apply Density.ext
    change (p : ℂ) • ρ.op + ((1 - p : ℝ) : ℂ) • (((1 - p : ℝ) : ℂ)⁻¹ • A) = σ.op
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
    simp [A]
  exact he.symm ▸ hσ

/-- A free state has zero global robustness. -/
lemma globalRobustness_eq_zero_of_mem (F : FreeStateSet H) {ρ : Density H} (hρ : ρ ∈ F) :
    F.globalRobustness ρ = 0 := by
  apply le_antisymm _ zero_le
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨ρ, by simpa using hρ⟩

end FreeStateSet

/-- Compatible free sets on all positive tensor powers of one system. -/
structure FreeStateTheory (H : Qudit) where
  /-- The free states on a block of `n + 1` sites. -/
  free (n : ℕ) : FreeStateSet (tensorPower H n)
  /-- Appending two independent free blocks gives a free state on the joint register. -/
  append_mem {a b : ℕ} {ρ : Density (tensorPower H a)} {σ : Density (tensorPower H b)} :
    ρ ∈ free a → σ ∈ free b → (ρ.tensor σ).map (tensorPowerAppend H a b) ∈ free (b + a + 1)

namespace FreeStateTheory

variable {H K : Qudit}

/-- Independent copies of a free one-site state are free at every block length. -/
lemma tensorPower_mem (F : FreeStateTheory H) {ρ : Density H} (hρ : ρ ∈ F.free 0) (n : ℕ) :
    ρ.tensorPower n ∈ F.free n := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
    simpa only [Density.tensorPower_append, Nat.add_zero] using
      F.append_mem (ρ := ρ.tensorPower 0) hρ ih

/-- A sequence of channels is asymptotically nongenerating if every sequence of free inputs yields
outputs whose global robustness tends to zero. -/
def IsAsymptoticallyNongenerating (F : FreeStateTheory H) (G : FreeStateTheory K)
    (Φ : (n : ℕ) → QuantumChannel (tensorPower H n) (tensorPower K n)) : Prop :=
  ∀ ρ : (n : ℕ) → Density (tensorPower H n), (∀ n, ρ n ∈ F.free n) →
    Tendsto (fun n => (G.free n).globalRobustness ((Φ n).map (ρ n))) atTop (𝓝 0)

/-- Free-preserving channels on each block are asymptotically nongenerating. -/
lemma isAsymptoticallyNongenerating_of_mapsTo (F : FreeStateTheory H) (G : FreeStateTheory K)
    {Φ : (n : ℕ) → QuantumChannel (tensorPower H n) (tensorPower K n)}
    (h : ∀ n, Set.MapsTo (Φ n).map (F.free n) (G.free n)) :
    F.IsAsymptoticallyNongenerating G Φ := by
  intro ρ hρ
  exact tendsto_const_nhds.congr fun n =>
    ((G.free n).globalRobustness_eq_zero_of_mem (h n (hρ n))).symm

end FreeStateTheory

end Qudit
