/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Entropy.Basic
public import FQFP.CQM.Qudit.State.FunctionalCalculus
public import FQFP.CQM.Qudit.State.Support
public import FQFP.Analysis.SpecialFunctions.RelativeEntropy

/-!
# Quantum relative entropy

Umegaki relative entropy uses natural logarithms and takes values in `ENNReal`.
It is infinite exactly when the source support is not contained in the reference support.
Klein's inequality proves that the finite trace formula is nonnegative, so `ofReal`
does not truncate the mathematical value. No full-rank or commutativity assumption is used.

The definition follows Watrous, *The Theory of Quantum Information*, Definition 5.18,
with natural logarithms in place of base two.

## Main definitions and results

* `Qudit.Density.relativeEntropy`: Umegaki relative entropy in nats, with values in `ENNReal`.
* `Qudit.Density.relativeEntropy_ne_top_iff`: finiteness is equivalent to support inclusion.
* `Qudit.Density.relativeEntropyReal_nonneg`: Klein's inequality on the finite-value domain.
* `Qudit.Density.relativeEntropy_eq_classical_of_eigenbasis`: reduction in a common eigenbasis.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory DaggerCategory

namespace Qudit.Density

noncomputable section

variable {H : Qudit}

/-- The finite trace expression, interpreted as relative entropy only under support inclusion. -/
def relativeEntropyReal (ρ σ : Density H) : ℝ := ρ.expectation (ρ.logOp - σ.logOp)

/-- The spectral logarithm recovers the negative von Neumann entropy. -/
lemma expectation_logOp_self (ρ : Density H) :
    ρ.expectation ρ.logOp = -ρ.vonNeumannEntropy := by
  rw [logOp, expectation_spectralMap_self, vonNeumannEntropy_eq_sum]
  simp only [Real.negMulLog, neg_mul, ← Finset.sum_neg_distrib, neg_neg]

/-- The finite trace expression is negative entropy minus the reference log expectation. -/
lemma relativeEntropyReal_eq_neg_entropy_sub (ρ σ : Density H) :
    ρ.relativeEntropyReal σ = -ρ.vonNeumannEntropy - ρ.expectation σ.logOp := by
  rw [relativeEntropyReal, expectation_sub, expectation_logOp_self]

/-- A double spectral sum for the finite trace expression, including noncommuting states. -/
lemma relativeEntropyReal_eq_sum (ρ σ : Density H) :
    ρ.relativeEntropyReal σ = ∑ i, ∑ j,
      ρ.eigenvalue i * (Real.log (ρ.eigenvalue i) - Real.log (σ.eigenvalue j)) *
        ‖inner ℂ (σ.eigenbasis j) (ρ.eigenbasis i)‖ ^ 2 := by
  rw [relativeEntropyReal, expectation_sub, logOp, logOp,
    expectation_spectralMap_self, expectation_spectralMap]
  symm
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    σ.eigenbasis.sum_sq_norm_inner_right, ρ.eigenbasis.norm_eq_one, one_pow, mul_one]

/-- **Klein's inequality** for density operators, with the exact finite-value support condition. -/
lemma relativeEntropyReal_nonneg (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) :
    0 ≤ ρ.relativeEntropyReal σ := by
  let w (i j : Fin (Module.finrank ℂ H.state)) :=
    ‖inner ℂ (σ.eigenbasis j) (ρ.eigenbasis i)‖ ^ 2
  have hrow (i) : ∑ j, w i j = 1 := by
    simp only [w, σ.eigenbasis.sum_sq_norm_inner_right, ρ.eigenbasis.norm_eq_one, one_pow]
  have hcol (j) : ∑ i, w i j = 1 := by
    simp only [w, ρ.eigenbasis.sum_sq_norm_inner_left, σ.eigenbasis.norm_eq_one, one_pow]
  have hb (i j) : (ρ.eigenvalue i - σ.eigenvalue j) * w i j ≤
      ρ.eigenvalue i * (Real.log (ρ.eigenvalue i) - Real.log (σ.eigenvalue j)) * w i j := by
    by_cases hj : σ.eigenvalue j = 0
    · have hz : ρ.eigenvalue i * w i j = 0 := h.eigenvalue_mul_overlap_eq_zero i j hj
      simp only [hj, sub_zero, Real.log_zero]
      rw [mul_right_comm _ (Real.log _) _, hz, zero_mul]
    · exact mul_le_mul_of_nonneg_right
        (Real.sub_le_mul_log_sub (ρ.eigenvalue_nonneg i)
          (lt_of_le_of_ne (σ.eigenvalue_nonneg j) (Ne.symm hj))) (sq_nonneg _)
  have hz : ∑ i, ∑ j, (ρ.eigenvalue i - σ.eigenvalue j) * w i j = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow, mul_one]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hcol, mul_one, ρ.sum_eigenvalue, σ.sum_eigenvalue, sub_self]
  rw [relativeEntropyReal_eq_sum, ← hz]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j

open Classical in
/-- Umegaki relative entropy in nats, infinite outside the support inclusion domain. -/
def relativeEntropy (ρ σ : Density H) : ENNReal :=
  if ρ.AbsolutelyContinuous σ then ENNReal.ofReal (ρ.relativeEntropyReal σ) else ⊤

/-- Relative entropy is finite exactly when the source support is contained in the reference. -/
lemma relativeEntropy_ne_top_iff (ρ σ : Density H) :
    ρ.relativeEntropy σ ≠ ⊤ ↔ ρ.AbsolutelyContinuous σ := by
  classical
  simp only [relativeEntropy]
  split_ifs <;> simp_all

/-- Support failure is exactly the infinite case. -/
lemma relativeEntropy_eq_top_iff (ρ σ : Density H) :
    ρ.relativeEntropy σ = ⊤ ↔ ¬ρ.AbsolutelyContinuous σ := by
  simpa using not_congr (ρ.relativeEntropy_ne_top_iff σ)

/-- The real value agrees with the trace formula whenever the relative entropy is finite. -/
lemma toReal_relativeEntropy (ρ σ : Density H) (h : ρ.AbsolutelyContinuous σ) :
    (ρ.relativeEntropy σ).toReal = ρ.relativeEntropyReal σ := by
  simp [relativeEntropy, h, ENNReal.toReal_ofReal (ρ.relativeEntropyReal_nonneg σ h)]

/-- A state has zero relative entropy with respect to itself, including singular states. -/
@[simp]
lemma relativeEntropy_self (ρ : Density H) : ρ.relativeEntropy ρ = 0 := by
  simp [relativeEntropy, AbsolutelyContinuous.refl, relativeEntropyReal,
    expectation, expectationComplex]

/-- A common orthonormal eigenbasis reduces the trace expression to a classical sum. -/
lemma relativeEntropyReal_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (b : OrthonormalBasis ι ℂ H.state) (p q : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hσ : ∀ i, σ.op (b i) = (q i : ℂ) • b i) :
    ρ.relativeEntropyReal σ = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  rw [relativeEntropyReal, expectation, expectationComplex, Operator.trace,
    LinearMap.trace_eq_sum_inner _ b]
  simp only [Module.End.mul_apply, hρ, map_smul, LinearMap.sub_apply,
    ρ.logOp_apply_of_eigenvector (hρ _), σ.logOp_apply_of_eigenvector (hσ _),
    inner_smul_right, inner_sub_right, OrthonormalBasis.inner_eq_one, mul_one,
    Complex.re_sum, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The spectral logarithm of the maximally mixed state is scalar. -/
lemma logOp_maximallyMixed (H : Qudit) (hn : Module.finrank ℂ H.state ≠ 0) :
    (maximallyMixed H hn).logOp =
      (-Real.log (Module.finrank ℂ H.state) : ℂ) • (1 : Operator H) := by
  ext v
  have h := (maximallyMixed H hn).logOp_apply_of_eigenvector (v := v)
    (a := (Module.finrank ℂ H.state : ℝ)⁻¹) (by simp [op_maximallyMixed])
  simpa only [Real.log_inv, Complex.ofReal_neg, LinearMap.smul_apply,
    Module.End.one_apply] using h

/-- Relative entropy to the maximally mixed state measures the entropy deficit. -/
lemma relativeEntropy_maximallyMixed (ρ : Density H) (hn : Module.finrank ℂ H.state ≠ 0) :
    ρ.relativeEntropy (maximallyMixed H hn) =
      ENNReal.ofReal (Real.log (Module.finrank ℂ H.state) - ρ.vonNeumannEntropy) := by
  rw [relativeEntropy, ite_eq_left (ρ.absolutelyContinuous_maximallyMixed hn),
    relativeEntropyReal_eq_neg_entropy_sub, logOp_maximallyMixed]
  congr 1
  have hs : ((-Real.log (Module.finrank ℂ H.state) : ℂ) • (1 : Operator H)) =
      (-Real.log (Module.finrank ℂ H.state)) • (1 : Operator H) := by
    exact_mod_cast (rfl : (-Real.log (Module.finrank ℂ H.state) : ℝ) • (1 : Operator H) = _)
  rw [hs, expectation_smul, expectation_one]
  ring

open Classical in
/-- A pure reference gives zero only for that same density, and infinity for every other state. -/
lemma relativeEntropy_pure_right (ρ : Density H) (ψ : UnitState H) :
    ρ.relativeEntropy (pure ψ) = if ρ = pure ψ then 0 else ⊤ := by
  by_cases h : ρ = pure ψ
  · simp [h]
  · rw [ite_eq_right h]
    exact (relativeEntropy_eq_top_iff _ _).mpr
      (fun hc => h ((absolutelyContinuous_pure_iff _ _).mp hc))

/-- Quantum relative entropy in a common diagonal basis is classical relative entropy. -/
lemma relativeEntropy_eq_classical_of_eigenbasis {ι : Type*} [Fintype ι]
    (ρ σ : Density H) (b : OrthonormalBasis ι ℂ H.state)
    (p q : Convexity.StdSimplex ℝ ι)
    (hρ : ∀ i, ρ.op (b i) = (p.weights i : ℂ) • b i)
    (hσ : ∀ i, σ.op (b i) = (q.weights i : ℂ) • b i) :
    ρ.relativeEntropy σ = p.relativeEntropy q := by
  classical
  have hc : ρ.AbsolutelyContinuous σ ↔ p.AbsolutelyContinuous q :=
    absolutelyContinuous_iff_of_eigenbasis ρ σ b p.weights q.weights hρ hσ
  by_cases h : p.AbsolutelyContinuous q
  · rw [relativeEntropy, Convexity.StdSimplex.relativeEntropy,
      ite_eq_left h, ite_eq_left (hc.mpr h)]
    congr 1
    exact relativeEntropyReal_eq_sum_of_eigenbasis ρ σ b p.weights q.weights hρ hσ
  · rw [relativeEntropy, Convexity.StdSimplex.relativeEntropy,
      ite_eq_right h, ite_eq_right (hc.not.mpr h)]

/-- Classical orthogonal mixtures preserve relative entropy, including its infinite cases. -/
lemma relativeEntropy_mix_ofBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (p q : Convexity.StdSimplex ℝ ι) :
    (Ensemble.ofPure p (UnitState.ofBasis b)).mix.relativeEntropy
      (Ensemble.ofPure q (UnitState.ofBasis b)).mix = p.relativeEntropy q :=
  relativeEntropy_eq_classical_of_eigenbasis _ _ b p q
    (Ensemble.op_mix_ofPure_ofBasis_apply b p) (Ensemble.op_mix_ofPure_ofBasis_apply b q)

/-- The finite trace expression is invariant under simultaneous unitary transport. -/
lemma relativeEntropyReal_map_unitary {K : Qudit} (ρ σ : Density H)
    (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).relativeEntropyReal (σ.map U) = ρ.relativeEntropyReal σ := by
  simp only [relativeEntropyReal, expectation_sub, logOp_map_unitary, expectation_map_conj]

/-- Relative entropy is invariant under unitary transport, including its infinite cases. -/
@[simp]
lemma relativeEntropy_map_unitary {K : Qudit} (ρ σ : Density H)
    (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).relativeEntropy (σ.map U) = ρ.relativeEntropy σ := by
  classical
  by_cases h : ρ.AbsolutelyContinuous σ
  · have hu := (absolutelyContinuous_map_iff ρ σ U).mpr h
    simp only [relativeEntropy, h, hu, reduceIte, relativeEntropyReal_map_unitary]
  · have hu := (absolutelyContinuous_map_iff ρ σ U).not.mpr h
    simp only [relativeEntropy, h, hu, reduceIte]

end

end Qudit.Density
