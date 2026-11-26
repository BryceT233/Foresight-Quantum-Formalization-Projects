/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.State.Spectral.FunctionalCalculus
public import FQFP.CQM.Qudit.State.Spectral.Tensor
public import FQFP.CQM.Qudit.State.Topology
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Continuity of spectral functions

For continuous functions on the interval of density eigenvalues, the finite spectral
calculus agrees with the continuous functional calculus for operators.
-/

@[expose] public noncomputable section

open scoped Topology
open Complex

namespace Qudit.Density

variable {H : Qudit}

private lemma eigenvalue_mem_spectrum (ρ : Density H) (i : Fin (Module.finrank ℂ H.state)) :
    ρ.eigenvalue i ∈ _root_.spectrum ℝ ρ.op := by
  rw [ρ.realSpectrum_eq_range_eigenvalue]
  exact Set.mem_range_self i

open Classical in
private def spectralHom (ρ : Density H) : C(_root_.spectrum ℝ ρ.op, ℝ) →⋆ₐ[ℝ] Operator H :=
  let extend (g : C(_root_.spectrum ℝ ρ.op, ℝ)) (x : ℝ) :=
    if hx : x ∈ _root_.spectrum ℝ ρ.op then g ⟨x, hx⟩ else 0
  { toFun := fun g => ρ.spectralMap (extend g)
    map_zero' := by simp [spectralMap, extend]
    map_one' := by
      apply ρ.eigenbasis.toBasis.ext
      intro i
      simp [spectralMap_apply_eigenbasis, extend, eigenvalue_mem_spectrum]
    map_add' := by
      intro f g
      apply ρ.eigenbasis.toBasis.ext
      intro i
      simp [spectralMap_apply_eigenbasis, extend, eigenvalue_mem_spectrum, add_smul]
    map_mul' := by
      intro f g
      apply ρ.eigenbasis.toBasis.ext
      intro i
      simp only [OrthonormalBasis.coe_toBasis, mul_apply_eq_comp, spectralMap_apply_eigenbasis,
        extend, dite_eq_left (ρ.eigenvalue_mem_spectrum i), map_smul, ContinuousMap.mul_apply,
        smul_smul, Complex.ofReal_mul, mul_comm]
    commutes' := by
      intro r
      apply ρ.eigenbasis.toBasis.ext
      intro i
      simp [spectralMap_apply_eigenbasis, extend, eigenvalue_mem_spectrum,
        Algebra.algebraMap_eq_smul_one]
    map_star' := by
      intro f
      change ρ.spectralMap (extend (star f)) = (ρ.spectralMap (extend f)).adjoint
      rw [adjoint_spectralMap]
      simp [extend] }

private lemma continuous_spectralHom (ρ : Density H) : Continuous ρ.spectralHom := by
  simp only [spectralHom, StarAlgHom.coe_mk, spectralMap,
    dite_eq_left (ρ.eigenvalue_mem_spectrum _)]
  fun_prop

/-- The continuous functional calculus agrees with the finite spectral formula. -/
theorem cfc_eq_spectralMap (ρ : Density H) (f : ℝ → ℝ)
    (hf : ContinuousOn f (_root_.spectrum ℝ ρ.op)) : cfc f ρ.op = ρ.spectralMap f := by
  have ha : IsSelfAdjoint ρ.op := ρ.adjoint_op
  have he : cfcHom ha = ρ.spectralHom := by
    apply cfcHom_eq_of_continuous_of_map_id ha _ (continuous_spectralHom ρ)
    apply ρ.eigenbasis.toBasis.ext
    intro i
    simp [spectralHom, spectralMap_apply_eigenbasis, eigenvalue_mem_spectrum, apply_eigenbasis]
  rw [cfc_apply f ρ.op ha hf, he]
  apply ρ.eigenbasis.toBasis.ext
  intro i
  simp [spectralHom, spectralMap_apply_eigenbasis, eigenvalue_mem_spectrum]

/-- A scalar function continuous on `[0, 1]` induces a continuous function of the state. -/
theorem continuous_spectralMap (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    Continuous (fun ρ : Density H => ρ.spectralMap f) := by
  have hs (ρ : Density H) : _root_.spectrum ℝ ρ.op ⊆ Set.Icc 0 1 := by
    rw [ρ.realSpectrum_eq_range_eigenvalue]
    rintro x ⟨i, rfl⟩
    exact ⟨ρ.eigenvalue_nonneg i, ρ.eigenvalue_le_one i⟩
  simp_rw [← cfc_eq_spectralMap _ f (hf.mono (hs _))]
  exact (continuousOn_cfc (Operator H) isCompact_Icc f hf).comp_continuous
    continuous_op (fun ρ => ⟨ρ.adjoint_op, hs ρ⟩)

end Qudit.Density
