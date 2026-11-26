/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/

/-
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/States/Entanglement.lean: entanglement of formation, its value on separable
states and on the maximally entangled state, and the latter's reduced density.

QuantumInfo/States/Pure/Braket.lean: the normalized maximally entangled vector in a basis
and its entanglement in local dimension at least two.
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.Entropy.VonNeumann.Composite
public import FQFP.CQM.Qudit.State.Composite.Separable
public import FQFP.CQM.Qudit.State.ConvexRoof
public import FQFP.CQM.Qudit.State.Purification.Mixture

/-!
# Entanglement of formation

The cost of a pure bipartite state is its marginal entropy in nats. Taking the
pure convex roof gives its entanglement of formation for arbitrary mixed states.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped NNReal TensorProduct

namespace Qudit

variable {H K : Qudit}

namespace UnitState

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The normalized sum of equally labelled basis tensors of two copies of a qudit. -/
def maximallyEntangled (b : OrthonormalBasis ι ℂ H.state) : UnitState (H ⊗ H) :=
  purifyMixture b (fun _ => (Fintype.card ι : ℝ)⁻¹) (fun _ => by positivity)
    (by simp [Fintype.card_ne_zero]) (ofBasis b)

/-- In the defining basis the common diagonal amplitude is the inverse square root of dimension. -/
lemma coe_maximallyEntangled (b : OrthonormalBasis ι ℂ H.state) :
    (maximallyEntangled b).val =
      ((Real.sqrt (Fintype.card ι) : ℂ)⁻¹) • ∑ i, b i ⊗ₜ[ℂ] b i := by
  simp only [maximallyEntangled, purifyMixture, coe_ofBasis, Real.sqrt_inv, Complex.ofReal_inv,
    TensorProduct.smul_tmul', Finset.smul_sum]

/-- Discarding one half of the maximally entangled vector gives the maximally mixed state. -/
lemma partialTraceRight_pure_maximallyEntangled (b : OrthonormalBasis ι ℂ H.state) :
    (Density.pure (maximallyEntangled b)).partialTraceRight =
      Density.maximallyMixed H (by
        rw [Module.finrank_eq_card_basis b.toBasis]
        exact Fintype.card_ne_zero) := by
  rw [maximallyEntangled, partialTraceRight_pure_purifyMixture]
  apply Density.ext
  rw [Density.op_mixture, Density.op_maximallyMixed, Module.finrank_eq_card_basis b.toBasis]
  simp only [Density.op_pure, coe_ofBasis, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.smul_sum]
  congr 1
  simpa using Operator.sum_outer_basis b (1 : Operator H)

end UnitState

namespace Density

/-- A convex roof vanishes on separable states if the cost vanishes on pure products. -/
lemma convexRoof_eq_zero_of_isSeparable {ρ : Density (H ⊗ K)} (hρ : ρ.IsSeparable)
    (g : {σ : Density (H ⊗ K) // σ.IsPure} → ℝ≥0)
    (hg : ∀ (v : UnitState H) (u : UnitState K), g ⟨pure (v.tensor u), isPure_pure _⟩ = 0) :
    ρ.convexRoof g = 0 := by
  obtain ⟨ι, _, w, v, u, rfl⟩ := (isSeparable_iff_exists_pure_ensemble ρ).mp hρ
  exact convexRoof_eq_zero_of_mix w _ g fun i _ => hg (v i) (u i)

/-- Entanglement of formation in nats, the pure convex roof of the left marginal's entropy. -/
def entanglementOfFormation (ρ : Density (H ⊗ K)) : ℝ≥0 :=
  ρ.convexRoof (fun σ => ⟨σ.val.partialTraceRight.vonNeumannEntropy,
    σ.val.partialTraceRight.vonNeumannEntropy_nonneg⟩)

/-- On pure states the entanglement of formation equals the retained marginal's entropy. -/
@[simp]
lemma entanglementOfFormation_pure (ψ : UnitState (H ⊗ K)) :
    ((pure ψ).entanglementOfFormation : ℝ) = (pure ψ).partialTraceRight.vonNeumannEntropy := by
  exact congrArg NNReal.toReal (convexRoof_pure ψ (fun σ =>
    ⟨σ.val.partialTraceRight.vonNeumannEntropy, σ.val.partialTraceRight.vonNeumannEntropy_nonneg⟩))

/-- A pure product decomposition witnesses zero entanglement of formation. -/
lemma entanglementOfFormation_eq_zero_of_isSeparable {ρ : Density (H ⊗ K)} (hρ : ρ.IsSeparable) :
    ρ.entanglementOfFormation = 0 := by
  apply convexRoof_eq_zero_of_isSeparable hρ
  intro v u
  apply NNReal.eq
  change (pure (v.tensor u)).partialTraceRight.vonNeumannEntropy = 0
  rw [← tensor_pure, partialTraceRight_tensor, vonNeumannEntropy_pure]

/-- A maximally entangled pair in local dimension `d` has entanglement of formation `log d`. -/
lemma entanglementOfFormation_maximallyEntangled {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : OrthonormalBasis ι ℂ H.state) :
    ((pure (UnitState.maximallyEntangled b)).entanglementOfFormation : ℝ) =
      Real.log (Fintype.card ι) := by
  rw [entanglementOfFormation_pure, UnitState.partialTraceRight_pure_maximallyEntangled,
    vonNeumannEntropy_maximallyMixed, Module.finrank_eq_card_basis b.toBasis]

/-- A maximally entangled pair is inseparable in every local dimension greater than one. -/
lemma not_isSeparable_pure_maximallyEntangled {ι : Type*} [Fintype ι] [Nontrivial ι]
    (b : OrthonormalBasis ι ℂ H.state) : ¬ (pure (UnitState.maximallyEntangled b)).IsSeparable := by
  intro h
  have hz := congrArg NNReal.toReal (entanglementOfFormation_eq_zero_of_isSeparable h)
  change ((pure (UnitState.maximallyEntangled b)).entanglementOfFormation : ℝ) = 0 at hz
  rw [entanglementOfFormation_maximallyEntangled] at hz
  exact (Real.log_pos (by exact_mod_cast Fintype.one_lt_card (α := ι))).ne' hz

end Density

end Qudit
