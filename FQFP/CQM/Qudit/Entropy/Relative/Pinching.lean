/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/

/-
Physlib reference for the relative entropy identity for pinching.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Channels/Pinching.lean

Modified by Foresight Quantum in 2026
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Pinching
public import FQFP.CQM.Qudit.Entropy.Relative
public import FQFP.CQM.Qudit.Entropy.VonNeumann.Exchange

/-!
# Relative entropy under spectral pinching

For the spectral pinching of a reference σ, write τ for the pinched source ρ. Then
`D(ρ ‖ σ) = D(ρ ‖ τ) + D(τ ‖ σ)` in the extended nonnegative reals. The first term is
always finite. The second is infinite exactly when the source has support outside σ.
This is the pinching Pythagorean identity (Hayashi, *A Group Theoretic Approach to
Quantum Information*, Exercise 2.8).

The first term equals the entropy increase in nats and is bounded above by the logarithm
of the number of distinct eigenvalues of the reference.
-/

@[expose] public section

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- Pinching the state leaves expectations of observables commuting with the reference
unchanged, by self-duality of the sum of projection conjugations. -/
lemma expectation_pinching_of_commute (ρ σ : Density H) (A : Operator H) (h : Commute A σ.op) :
    (σ.pinching.map ρ).expectation A = ρ.expectation A := by
  have he := Superoperator.trace_kraus_adjoint
    (fun a : σ.spectralValues => σ.spectralProjection a) ρ.op A
  simp only [adjoint_spectralProjection] at he
  change (σ.pinching.toSuperoperator A * ρ.op).trace = (A * σ.pinching.toSuperoperator ρ.op).trace
    at he
  rw [(σ.pinching_apply_eq_self_iff A).mpr h] at he
  exact congrArg Complex.re he.symm

/-- The pinching inequality implies that the pinched support contains the source support. -/
lemma absolutelyContinuous_pinching (ρ σ : Density H) :
    ρ.AbsolutelyContinuous (σ.pinching.map ρ) := by
  intro x hx
  change (σ.pinching.map ρ).op x = 0 at hx
  have h := (LinearMap.le_def.mp (ρ.le_card_smul_pinching_map σ)).re_inner_nonneg_right x
  apply (ρ.op.apply_eq_zero_iff_re_inner_eq_zero ρ.positive x).mpr
  apply le_antisymm _ (ρ.positive.re_inner_nonneg_right x)
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, hx, smul_zero, zero_sub,
    inner_neg_right, map_neg, neg_nonneg] using h

/-- Pinching with respect to σ preserves and reflects support inclusion in σ,
including when the zero eigenvalue has multiplicity greater than one. -/
lemma absolutelyContinuous_pinching_iff (ρ σ : Density H) :
    (σ.pinching.map ρ).AbsolutelyContinuous σ ↔ ρ.AbsolutelyContinuous σ := by
  refine ⟨fun h => (ρ.absolutelyContinuous_pinching σ).trans h, fun h x hx => ?_⟩
  have hx' : σ.op x = ((0 : ℝ) : ℂ) • x := by simpa using hx
  have hρ : ρ.op x = 0 := h hx
  change σ.pinching.toSuperoperator ρ.op x = 0
  rw [pinching_apply, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : (0 : ℝ) = a <;>
    simp [σ.spectralProjection_apply_of_eigenvector _ hx', ha, hρ]

/-- The Umegaki relative entropy splits into the cost of pinching the source and the
relative entropy of its pinched state to the reference, also for infinite values. -/
theorem pinching_pythagoras (ρ σ : Density H) :
    ρ.relativeEntropy σ = ρ.relativeEntropy (σ.pinching.map ρ) +
      (σ.pinching.map ρ).relativeEntropy σ := by
  let τ := σ.pinching.map ρ
  have hρτ : ρ.AbsolutelyContinuous τ := ρ.absolutelyContinuous_pinching σ
  have hs := ρ.absolutelyContinuous_pinching_iff σ
  by_cases h : ρ.AbsolutelyContinuous σ
  · have hτσ : τ.AbsolutelyContinuous σ := hs.mpr h
    have hc : Commute σ.op τ.op := σ.commute_pinching ρ.op
    have heτ := ρ.expectation_pinching_of_commute σ τ.logOp
      (τ.commute_spectralMap hc Real.log).symm
    have heσ := ρ.expectation_pinching_of_commute σ σ.logOp
      (σ.commute_spectralMap (Commute.refl _) Real.log).symm
    change τ.expectation τ.logOp = _ at heτ
    change τ.expectation σ.logOp = _ at heσ
    change ρ.relativeEntropy σ = ρ.relativeEntropy τ + τ.relativeEntropy σ
    simp only [relativeEntropy, h, hρτ, hτσ, ↓reduceIte]
    rw [← ENNReal.ofReal_add (ρ.relativeEntropyReal_nonneg τ hρτ)
      (τ.relativeEntropyReal_nonneg σ hτσ)]
    congr 1
    simp only [relativeEntropyReal, expectation_sub, heτ, heσ]
    ring
  · rw [(ρ.relativeEntropy_eq_top_iff σ).mpr h,
      ((σ.pinching.map ρ).relativeEntropy_eq_top_iff σ).mpr (hs.not.mpr h), add_top]

/-- The entropy gained by pinching is exactly the finite relative entropy to the pinched state. -/
lemma toReal_relativeEntropy_pinching (ρ σ : Density H) :
    (ρ.relativeEntropy (σ.pinching.map ρ)).toReal =
      (σ.pinching.map ρ).vonNeumannEntropy - ρ.vonNeumannEntropy := by
  let τ := σ.pinching.map ρ
  have hc : Commute σ.op τ.op := σ.commute_pinching ρ.op
  have he := ρ.expectation_pinching_of_commute σ τ.logOp (τ.commute_spectralMap hc Real.log).symm
  change τ.expectation τ.logOp = ρ.expectation τ.logOp at he
  change (ρ.relativeEntropy τ).toReal = τ.vonNeumannEntropy - ρ.vonNeumannEntropy
  rw [toReal_relativeEntropy _ _ (ρ.absolutelyContinuous_pinching σ),
    relativeEntropyReal_eq_neg_entropy_sub, ← he, expectation_logOp_self]
  abel

/-- Pinching has zero entropy gain exactly for states commuting with the reference,
including states supported in its kernel. -/
lemma vonNeumannEntropy_pinching_sub_eq_zero_iff (ρ σ : Density H) :
    (σ.pinching.map ρ).vonNeumannEntropy - ρ.vonNeumannEntropy = 0 ↔ Commute ρ.op σ.op := by
  have hf := (relativeEntropy_ne_top_iff _ _).mpr (ρ.absolutelyContinuous_pinching σ)
  rw [← toReal_relativeEntropy_pinching, ENNReal.toReal_eq_zero_iff, or_iff_left hf,
    relativeEntropy_eq_zero_iff, ← σ.pinching_apply_eq_self_iff]
  exact ⟨fun h => congrArg Density.op h.symm, fun h => (Density.ext h).symm⟩

/-- Spectral pinching cannot decrease the von Neumann entropy. -/
lemma vonNeumannEntropy_le_pinching (ρ σ : Density H) :
    ρ.vonNeumannEntropy ≤ (σ.pinching.map ρ).vonNeumannEntropy :=
  sub_nonneg.mp ((ρ.toReal_relativeEntropy_pinching σ) ▸ ENNReal.toReal_nonneg)

/-- Recording one environment label per distinct eigenvalue bounds the entropy gain in nats. -/
lemma vonNeumannEntropy_pinching_sub_le_log_card (ρ σ : Density H) :
    (σ.pinching.map ρ).vonNeumannEntropy - ρ.vonNeumannEntropy ≤
      Real.log σ.spectralValues.card := by
  have he := σ.pinching.entropyExchange_le_log_card_of_kraus
    (fun a : σ.spectralValues => σ.spectralProjection a) rfl ρ
  rw [Fintype.card_coe] at he
  have hc := σ.pinching.coherentInfo_le_input_entropy ρ
  rw [QuantumChannel.coherentInfo_eq_sub_entropyExchange] at hc
  linarith

/-- The relative entropy to the pinched state is at most the log of the number of blocks. -/
lemma relativeEntropy_pinching_le_log_card (ρ σ : Density H) :
    ρ.relativeEntropy (σ.pinching.map ρ) ≤ ENNReal.ofReal (Real.log σ.spectralValues.card) := by
  have hf := (relativeEntropy_ne_top_iff _ _).mpr (ρ.absolutelyContinuous_pinching σ)
  rw [← ENNReal.ofReal_toReal hf, toReal_relativeEntropy_pinching]
  exact ENNReal.ofReal_le_ofReal (ρ.vonNeumannEntropy_pinching_sub_le_log_card σ)

end

end Qudit.Density
