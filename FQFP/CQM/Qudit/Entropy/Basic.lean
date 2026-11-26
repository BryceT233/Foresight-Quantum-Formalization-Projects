/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

/-
Physlib reference for von Neumann entropy and its spectral formula.
leanprover-community/physlib @ adccea9195c7c347a5f8cde1ddf6874f89ea6a9a
QuantumInfo/Entropy/VonNeumann.lean

QuantumInfo/States/Entanglement.lean: entropy as the trace of the spectral function.
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Authors: FQFP authors
-/
module

public import FQFP.Analysis.SpecialFunctions.Entropy
public import FQFP.CQM.Qudit.State.Pure
public import FQFP.CQM.Qudit.State.Spectral.FunctionalCalculus
import FQFP.CQM.Qudit.State.Spectral.Tensor

/-!
# Von Neumann entropy

Entropy is the Shannon entropy of the existing spectral distribution, using natural
logarithms. Singular densities are included: zero eigenvalues contribute zero.
Spectral sums in arbitrary orthonormal eigenbases give a coordinate-independent API.
The conventions agree with physlib's `QuantumInfo/Entropy/VonNeumann.lean`.

## Main definitions and results

* `Qudit.Density.vonNeumannEntropy`: von Neumann entropy in nats, including singular densities.
* `Qudit.Density.vonNeumannEntropy_le_log_finrank`: the dimension bound on entropy.
* `Qudit.Density.vonNeumannEntropy_pure`: pure states have zero entropy.
* `Qudit.Density.vonNeumannEntropy_map_unitary`: invariance under unitary transport.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory MonoidalCategory DaggerCategory

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- Von Neumann entropy in nats, defined on all density operators. -/
def vonNeumannEntropy (ρ : Density H) : ℝ := ρ.spectrum.shannonEntropy

/-- Entropy is the sum of `-λ log λ` over the spectrum, including zero eigenvalues. -/
lemma vonNeumannEntropy_eq_sum (ρ : Density H) :
    ρ.vonNeumannEntropy = ∑ i, Real.negMulLog (ρ.eigenvalue i) := rfl

/-- Von Neumann entropy is nonnegative. -/
lemma vonNeumannEntropy_nonneg (ρ : Density H) : 0 ≤ ρ.vonNeumannEntropy :=
  ρ.spectrum.shannonEntropy_nonneg

/-- Entropy is bounded by the logarithm of the Hilbert-space dimension. -/
lemma vonNeumannEntropy_le_log_finrank (ρ : Density H) :
    ρ.vonNeumannEntropy ≤ Real.log (Module.finrank ℂ H.state) := by
  simpa only [vonNeumannEntropy, Fintype.card_fin] using ρ.spectrum.shannonEntropy_le_log_card

/-- Entropy can be calculated in any orthonormal eigenbasis. -/
lemma vonNeumannEntropy_eq_sum_of_eigenbasis {ι : Type*} [Fintype ι] (ρ : Density H)
    (b : OrthonormalBasis ι ℂ H.state) (w : ι → ℝ)
    (hw : ∀ i, ρ.op (b i) = (w i : ℂ) • b i) :
    ρ.vonNeumannEntropy = ∑ i, Real.negMulLog (w i) :=
  ρ.sum_eigenvalue_eq_of_eigenbasis b w hw Real.negMulLog

/-- Zero eigenvalues can be removed without changing entropy. -/
lemma vonNeumannEntropy_eq_sum_nonzeroEigenvalues (ρ : Density H) :
    ρ.vonNeumannEntropy = (ρ.nonzeroEigenvalues.map Real.negMulLog).sum :=
  ρ.sum_eigenvalue_eq_sum_nonzeroEigenvalues Real.negMulLog Real.negMulLog_zero

/-- States on possibly different spaces with equal nonzero spectra have equal entropy. -/
lemma vonNeumannEntropy_eq_of_nonzeroEigenvalues_eq (ρ : Density H) (σ : Density K)
    (h : ρ.nonzeroEigenvalues = σ.nonzeroEigenvalues) :
    ρ.vonNeumannEntropy = σ.vonNeumannEntropy := by
  rw [vonNeumannEntropy_eq_sum_nonzeroEigenvalues,
    vonNeumannEntropy_eq_sum_nonzeroEigenvalues, h]

/-- The entropy of a pure state is zero. -/
@[simp]
lemma vonNeumannEntropy_pure (ψ : UnitState H) : (pure ψ).vonNeumannEntropy = 0 := by
  rw [vonNeumannEntropy_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  let ρ := pure ψ
  change Real.negMulLog (ρ.eigenvalue i) = 0
  have hsq : ρ.eigenvalue i ^ 2 = ρ.eigenvalue i := by
    rw [pow_two]
    have he := LinearMap.congr_fun (pure_mul_self ψ) (ρ.eigenbasis i)
    change (ρ.op * ρ.op) (ρ.eigenbasis i) = ρ.op (ρ.eigenbasis i) at he
    simp only [mul_apply_eq_comp, apply_eigenbasis, map_smul, smul_smul] at he
    exact_mod_cast smul_left_injective ℂ (ρ.eigenbasis.toBasis.ne_zero i) he
  rcases eq_zero_or_one_of_sq_eq_self hsq with h | h <;>
    simp only [h, Real.negMulLog_zero, Real.negMulLog_one]

/-- Every density known to be pure has zero entropy. -/
lemma IsPure.vonNeumannEntropy_eq_zero {ρ : Density H} (hρ : ρ.IsPure) :
    ρ.vonNeumannEntropy = 0 := by
  obtain ⟨ψ, rfl⟩ := hρ
  exact vonNeumannEntropy_pure ψ

/-- An orthogonal classical mixture has the Shannon entropy of its probabilities. -/
lemma vonNeumannEntropy_mix_ofBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (p : Convexity.StdSimplex ℝ ι) :
    (Ensemble.ofPure p (UnitState.ofBasis b)).mix.vonNeumannEntropy = p.shannonEntropy :=
  vonNeumannEntropy_eq_sum_of_eigenbasis _ b p.weights
    (Ensemble.op_mix_ofPure_ofBasis_apply b p)

/-- Unitary transport between isomorphic systems preserves entropy. -/
@[simp]
lemma vonNeumannEntropy_map_unitary (ρ : Density H) (U : H ⟶ K) [IsUnitary U] :
    (ρ.map U).vonNeumannEntropy = ρ.vonNeumannEntropy := by
  apply vonNeumannEntropy_eq_of_nonzeroEigenvalues_eq
  simp only [nonzeroEigenvalues, ρ.eigenvalues_map_unitary U]

/-- Von Neumann entropy is the trace of the spectral function `x ↦ -x log x`. -/
lemma vonNeumannEntropy_eq_trace_spectralMap (ρ : Density H) :
    ρ.vonNeumannEntropy = (ρ.spectralMap Real.negMulLog).trace.re := by
  simp [vonNeumannEntropy_eq_sum, spectralMap, Operator.trace_outer, Complex.re_sum]

/-- A maximally mixed state has entropy equal to the logarithm of the dimension. -/
@[simp]
lemma vonNeumannEntropy_maximallyMixed (H : Qudit) (hn : Module.finrank ℂ H.state ≠ 0) :
    (maximallyMixed H hn).vonNeumannEntropy = Real.log (Module.finrank ℂ H.state) := by
  let ρ := maximallyMixed H hn
  have he (i : Fin (Module.finrank ℂ H.state)) :
      ρ.op (ρ.eigenbasis i) = (↑((Module.finrank ℂ H.state : ℝ)⁻¹) : ℂ) •
        ρ.eigenbasis i := by
    simp [ρ, op_maximallyMixed]
  rw [vonNeumannEntropy_eq_sum_of_eigenbasis ρ ρ.eigenbasis
    (fun _ => (Module.finrank ℂ H.state : ℝ)⁻¹) he]
  have hn' : (Module.finrank ℂ H.state : ℝ) ≠ 0 := by exact_mod_cast hn
  simp [Real.negMulLog, Real.log_inv, hn']

end

end Qudit.Density
