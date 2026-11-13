/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.PureComposite

/-!
# Purification of density operators

Every density operator admits a pure state on a larger system whose right partial trace
is the original density. The construction pairs its eigenvectors, weighted by square roots
of eigenvalues, with an orthonormal basis of an auxiliary system. Zero eigenvalues remain
allowed. The default auxiliary system is a second copy of the original qudit, with its
standard orthonormal basis; the chosen purification vector is not basis-independent.

This adapts physlib's `MState.purify`, `MState.purify_spec` and `MState.purifyX` to the
existing coordinate-free `UnitState`, `Density` and partial trace interfaces.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct BigOperators

namespace Qudit.Density

noncomputable section

variable {H K : Qudit}

/-- The spectral purification sum has the original density as its unnormalized marginal. -/
lemma partialTraceRight_outer_spectral_sum (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    Operator.partialTraceRight
      (Operator.outer (∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i)
        (∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i)) = ρ.op := by
  rw [Operator.partialTraceRight_outer_sum_tmul, ρ.op_eq_sum_eigenvalue_smul_outer]
  apply Finset.sum_congr rfl
  intro i _
  rw [Operator.outer_smul_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow,
    Real.sq_sqrt (ρ.eigenvalue_nonneg i)]

/-- Purify a density operator using an explicit orthonormal basis for the auxiliary system. -/
def purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    UnitState (H ⊗ K) :=
  ⟨∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i, by
    have ht := (LinearMap.trace_partialTraceRight _).symm.trans
      (congrArg Operator.trace (ρ.partialTraceRight_outer_spectral_sum b))
    exact (Operator.trace_outer _ _).symm.trans (ht.trans ρ.trace_one)⟩

/-- The vector of an explicit-basis purification is its square-root-weighted spectral sum. -/
lemma coe_purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    (ρ.purifyWith b).val =
      ∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ] b i := rfl

/-- Discarding the auxiliary system of an explicit-basis purification recovers the input. -/
lemma partialTraceRight_pure_purifyWith (ρ : Density H)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    (pure (ρ.purifyWith b)).partialTraceRight = ρ := by
  apply Density.ext
  exact ρ.partialTraceRight_outer_spectral_sum b

/-- The spectral purification using a full-dimensional copy of the original system. -/
def purify (ρ : Density H) : UnitState (H ⊗ H) :=
  ρ.purifyWith (stdOrthonormalBasis ℂ H.state)

/-- The default purification uses the standard orthonormal basis on the auxiliary copy. -/
lemma coe_purify (ρ : Density H) :
    ρ.purify.val = ∑ i, ((Real.sqrt (ρ.eigenvalue i) : ℂ) • ρ.eigenbasis i) ⊗ₜ[ℂ]
      stdOrthonormalBasis ℂ H.state i := rfl

/-- The right partial trace of the pure spectral purification is the original density. -/
lemma partialTraceRight_pure_purify (ρ : Density H) :
    (pure ρ.purify).partialTraceRight = ρ :=
  ρ.partialTraceRight_pure_purifyWith (stdOrthonormalBasis ℂ H.state)

/-- A purification bundled with its marginal recovery property. -/
def purification (ρ : Density H) :
    {ψ : UnitState (H ⊗ H) // (pure ψ).partialTraceRight = ρ} :=
  ⟨ρ.purify, ρ.partialTraceRight_pure_purify⟩

/-- Every density operator is the marginal of a pure state on two copies of its system. -/
lemma exists_purification (ρ : Density H) :
    ∃ ψ : UnitState (H ⊗ H), (pure ψ).partialTraceRight = ρ :=
  ⟨ρ.purify, ρ.partialTraceRight_pure_purify⟩

/-- With the auxiliary copy moved to the left, the left partial trace recovers the input. -/
lemma partialTraceLeft_pure_purify_swap (ρ : Density H) :
    (pure ρ.purify.swap).partialTraceLeft = ρ := by
  have h := partialTraceRight_pure_swap ρ.purify.swap
  rw [UnitState.swap_swap, ρ.partialTraceRight_pure_purify] at h
  exact h.symm

end

end Qudit.Density
