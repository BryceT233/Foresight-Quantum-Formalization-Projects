/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Ensemble.lean: nonnegative ensemble averages and mixtures with pure output.
QuantumInfo/States/Entanglement.lean: pure and mixed convex roofs and their bounds.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.Support
public import Mathlib.Basic.ENNReal.Basic

/-!
# Convex roofs over finite ensembles

Pure densities represent rays, so a function on them is automatically phase invariant.
Both roofs take the infimum in the nonnegative reals. The spectral ensemble witnesses
nonemptiness for the pure roof, and the singleton ensemble does so for the mixed roof.
-/

@[expose] public noncomputable section

open scoped ENNReal NNReal
open Convexity

namespace Qudit

variable {H : Qudit}

namespace Ensemble

/-- Average of nonnegative costs assigned to the labels of a finite ensemble. -/
def averageCost {ι : Type*} [Fintype ι] (w : StdSimplex ℝ ι) (c : ι → ℝ≥0) : ℝ≥0 :=
  ⟨∑ i, w.weights i * c i, Finset.sum_nonneg fun i _ => mul_nonneg (w.weights_nonneg i) (c i).2⟩

lemma averageCost_eq_of_const {ι : Type*} [Fintype ι] (w : StdSimplex ℝ ι)
    (c : ι → ℝ≥0) (a : ℝ≥0) (h : ∀ i, w.weights i ≠ 0 → c i = a) :
    averageCost w c = a := by
  apply NNReal.eq
  change ∑ i, w.weights i * (c i : ℝ) = a
  calc
    _ = ∑ i, w.weights i * (a : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w.weights i = 0
      · simp [hi]
      · rw [h i hi]
    _ = _ := by rw [← Finset.sum_mul, w.total_of_fintype, one_mul]

/-- Each positive-weight component is supported on the mixture. -/
lemma absolutelyContinuous_mix {ι : Type*} [Fintype ι] (e : Ensemble H ι)
    (i : ι) (hi : e.weight i ≠ 0) : (e.state i).AbsolutelyContinuous e.mix := by
  intro x hx
  change e.mix.op x = 0 at hx
  have hz := congrArg (fun y => (inner ℂ x y).re) hx
  simp only [op_mix, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    inner_zero_right, Complex.zero_re] at hz
  apply ((e.state i).op.apply_eq_zero_iff_re_inner_eq_zero (e.state i).positive x).mpr
  exact (mul_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (e.weight_nonneg j) ((e.state j).positive.re_inner_nonneg_right x))).mp hz i
      (Finset.mem_univ i))).resolve_left hi

/-- All positive-weight components of an ensemble with pure mixture equal the mixture. -/
lemma state_eq_of_mix_eq_pure {ι : Type*} [Fintype ι] (e : Ensemble H ι) {ψ : UnitState H}
    (hmix : e.mix = Density.pure ψ) (i : ι) (hi : e.weight i ≠ 0) :
    e.state i = Density.pure ψ :=
  ((e.state i).absolutelyContinuous_pure_iff ψ).mp (hmix ▸ e.absolutelyContinuous_mix i hi)

end Ensemble

namespace Density

/-- The attainable average costs of decompositions of a density into a given family of states. -/
def ensembleCosts {α : Type*} (state : α → Density H) (cost : α → ℝ≥0)
    (ρ : Density H) : Set ℝ≥0 :=
  {a | ∃ (ι : Type) (_ : Fintype ι) (w : StdSimplex ℝ ι) (v : ι → α),
    (Ensemble.mk w (state ∘ v)).mix = ρ ∧ Ensemble.averageCost w (cost ∘ v) = a}

private lemma self_mem_ensembleCosts {α : Type*} (state : α → Density H) (cost : α → ℝ≥0)
    (x : α) : cost x ∈ ensembleCosts state cost (state x) := by
  let w : StdSimplex ℝ Unit := .single ()
  exact ⟨Unit, inferInstance, w, fun _ => x, Ensemble.mix_const w (state x),
    Ensemble.averageCost_eq_of_const w _ _ fun _ _ => rfl⟩

/-- The mixed convex roof minimizes average cost over all finite mixed-state decompositions. -/
def mixedConvexRoof (ρ : Density H) (f : Density H → ℝ≥0) : ℝ≥0 :=
  sInf (ensembleCosts id f ρ)

/-- The pure convex roof minimizes average cost over decompositions into pure densities. -/
def convexRoof (ρ : Density H) (g : {σ : Density H // σ.IsPure} → ℝ≥0) : ℝ≥0 :=
  sInf (ensembleCosts (fun ψ => pure ψ) (fun ψ => g ⟨pure ψ, isPure_pure ψ⟩) ρ)

private lemma pure_ensembleCosts_nonempty (ρ : Density H) (g : {σ : Density H // σ.IsPure} → ℝ≥0) :
    (ensembleCosts pure (fun ψ => g ⟨pure ψ, isPure_pure ψ⟩) ρ).Nonempty :=
  ⟨_, _, inferInstance, ρ.spectrum, UnitState.ofBasis ρ.eigenbasis, ρ.mix_spectralEnsemble, rfl⟩

/-- The extended-real infimum over pure decompositions is the finite convex roof. -/
lemma coe_convexRoof (ρ : Density H) (g : {σ : Density H // σ.IsPure} → ℝ≥0) :
    (ρ.convexRoof g : ℝ≥0∞) =
      ⨅ a ∈ ensembleCosts pure (fun ψ => g ⟨pure ψ, isPure_pure ψ⟩) ρ, (a : ℝ≥0∞) :=
  ENNReal.coe_sInf (pure_ensembleCosts_nonempty ρ g)

/-- The extended-real infimum over mixed decompositions is the finite mixed convex roof. -/
lemma coe_mixedConvexRoof (ρ : Density H) (f : Density H → ℝ≥0) :
    (ρ.mixedConvexRoof f : ℝ≥0∞) = ⨅ a ∈ ensembleCosts id f ρ, (a : ℝ≥0∞) :=
  ENNReal.coe_sInf ⟨_, self_mem_ensembleCosts id f ρ⟩

lemma mixedConvexRoof_le_averageCost {ι : Type} [Fintype ι] (e : Ensemble H ι)
    (f : Density H → ℝ≥0) :
    e.mix.mixedConvexRoof f ≤ Ensemble.averageCost e.distribution (f ∘ e.state) :=
  csInf_le (OrderBot.bddBelow _) ⟨ι, inferInstance, e.distribution, e.state, rfl, rfl⟩

lemma le_mixedConvexRoof {ρ : Density H} {f : Density H → ℝ≥0} {a : ℝ≥0}
    (h : ∀ (ι : Type) [Fintype ι] (e : Ensemble H ι), e.mix = ρ →
      a ≤ Ensemble.averageCost e.distribution (f ∘ e.state)) : a ≤ ρ.mixedConvexRoof f := by
  apply le_csInf ⟨_, self_mem_ensembleCosts id f ρ⟩
  rintro _ ⟨ι, _, w, v, hmix, rfl⟩
  exact h ι ⟨w, v⟩ hmix

lemma convexRoof_le_averageCost {ι : Type} [Fintype ι] (w : StdSimplex ℝ ι)
    (v : ι → UnitState H) (g : {σ : Density H // σ.IsPure} → ℝ≥0) :
    (Ensemble.ofPure w v).mix.convexRoof g ≤
      Ensemble.averageCost w (fun i => g ⟨pure (v i), isPure_pure _⟩) :=
  csInf_le (OrderBot.bddBelow _) ⟨ι, inferInstance, w, v, rfl, rfl⟩

lemma le_convexRoof {ρ : Density H} {g : {σ : Density H // σ.IsPure} → ℝ≥0} {a : ℝ≥0}
    (h : ∀ (ι : Type) [Fintype ι] (w : StdSimplex ℝ ι) (v : ι → UnitState H),
      (Ensemble.ofPure w v).mix = ρ →
        a ≤ Ensemble.averageCost w (fun i => g ⟨pure (v i), isPure_pure _⟩)) :
    a ≤ ρ.convexRoof g := by
  apply le_csInf (pure_ensembleCosts_nonempty ρ g)
  rintro _ ⟨ι, _, w, v, hmix, rfl⟩
  exact h ι w v hmix

/-- Allowing mixed components can only decrease the infimum. -/
lemma mixedConvexRoof_le_convexRoof (ρ : Density H) (f : Density H → ℝ≥0) :
    ρ.mixedConvexRoof f ≤ ρ.convexRoof (fun σ => f σ.val) := by
  apply le_convexRoof
  rintro ι _ w v rfl
  exact mixedConvexRoof_le_averageCost (Ensemble.ofPure w v) f

@[simp]
lemma convexRoof_pure (ψ : UnitState H) (g : {σ : Density H // σ.IsPure} → ℝ≥0) :
    (pure ψ).convexRoof g = g ⟨pure ψ, isPure_pure ψ⟩ := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) (self_mem_ensembleCosts _ _ ψ)
  · apply le_convexRoof
    intro ι _ w v hmix
    apply le_of_eq
    symm
    apply Ensemble.averageCost_eq_of_const
    intro i hi
    exact congrArg g (Subtype.ext ((Ensemble.mix_ofPure_eq_pure_iff w v ψ).mp hmix i hi))

@[simp]
lemma mixedConvexRoof_pure (ψ : UnitState H) (f : Density H → ℝ≥0) :
    (pure ψ).mixedConvexRoof f = f (pure ψ) := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) (self_mem_ensembleCosts id f _)
  · apply le_mixedConvexRoof
    intro ι _ e hmix
    exact (Ensemble.averageCost_eq_of_const _ _ _ fun i hi =>
      congrArg f (e.state_eq_of_mix_eq_pure hmix i hi)).ge

/-- One decomposition of zero cost suffices for the convex roof to vanish. -/
lemma convexRoof_eq_zero_of_mix {ι : Type} [Fintype ι] (w : StdSimplex ℝ ι)
    (v : ι → UnitState H) (g : {σ : Density H // σ.IsPure} → ℝ≥0)
    (hg : ∀ i, w.weights i ≠ 0 → g ⟨pure (v i), isPure_pure _⟩ = 0) :
    (Ensemble.ofPure w v).mix.convexRoof g = 0 :=
  le_antisymm ((convexRoof_le_averageCost w v g).trans_eq
    (Ensemble.averageCost_eq_of_const w _ 0 hg)) zero_le

end Density

end Qudit
