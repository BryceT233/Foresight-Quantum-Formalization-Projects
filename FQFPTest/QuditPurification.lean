/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.Purification
import FQFP.CQM.Qudit.State.Separable

/-!
# Purification regressions

These clients cover singular mixed inputs, an auxiliary system in standard coordinates,
changes of auxiliary basis, swapped system order, local expectations and the distinction
between purification of pure and genuinely mixed states.
-/

open CategoryTheory MonoidalCategory Qudit

noncomputable section

private def singularQutrit : Density (std 3) :=
  Density.mix (1 / 3) (by norm_num) (by norm_num)
    (Density.pure (UnitState.ofBasis (ZBasis 3) 0))
    (Density.pure (UnitState.ofBasis (ZBasis 3) 1))

-- The construction permits a nontrivial kernel; no full-rank premise is supplied.
example : singularQutrit.op (ZBasis 3 2) = 0 := by
  simp [singularQutrit, LinearMap.add_apply, LinearMap.smul_apply]

example : (Density.pure singularQutrit.purify).partialTraceRight = singularQutrit :=
  singularQutrit.partialTraceRight_pure_purify

-- Normalization is part of the output type, even when some eigenvalues vanish.
example : ‖singularQutrit.purify.val‖ = 1 := singularQutrit.purify.norm_eq_one

-- A coordinate-free input can use a distinct auxiliary qudit in standard coordinates.
example {H : Qudit} (ρ : Density H) :
    (Density.pure (ρ.purifyWith (ZBasis (Module.finrank ℂ H.state)))).partialTraceRight = ρ :=
  ρ.partialTraceRight_pure_purifyWith _

-- The recovered input is independent of the auxiliary basis, not the purification vector.
example {H K : Qudit} (ρ : Density H)
    (b c : OrthonormalBasis (Fin (Module.finrank ℂ H.state)) ℂ K.state) :
    (Density.pure (ρ.purifyWith b)).partialTraceRight =
      (Density.pure (ρ.purifyWith c)).partialTraceRight := by
  rw [ρ.partialTraceRight_pure_purifyWith, ρ.partialTraceRight_pure_purifyWith]

-- The bundled witness retains its reconstruction property.
example {H : Qudit} (ρ : Density H) :
    (Density.pure ρ.purification.val).partialTraceRight = ρ := ρ.purification.property

-- Placing the auxiliary copy on the left changes which partial trace must be used.
example : (Density.pure singularQutrit.purify.swap).partialTraceLeft = singularQutrit :=
  singularQutrit.partialTraceLeft_pure_purify_swap

-- All local complex expectations are preserved, including off-diagonal observables.
example {H : Qudit} (ρ : Density H) (A : Operator H) :
    (Density.pure ρ.purify).expectationComplex (Operator.tensor A 1) =
      ρ.expectationComplex A := by
  rw [← Density.expectationComplex_partialTraceRight, ρ.partialTraceRight_pure_purify]

-- The previous purity criterion composes directly with purification.
example {H : Qudit} (ρ : Density H) : ρ.purify.IsProduct ↔ ρ.IsPure := by
  rw [UnitState.isProduct_iff_isPure_partialTraceRight, ρ.partialTraceRight_pure_purify]

-- Pure inputs need no special constructor and retain the full auxiliary dimension.
example (v : UnitState (std 3)) : (Density.pure v).purify.IsProduct := by
  rw [UnitState.isProduct_iff_isPure_partialTraceRight,
    Density.partialTraceRight_pure_purify]
  exact Density.isPure_pure v

-- A genuinely mixed input is recovered from an entangled pure state.
example {H : Qudit} (ρ : Density H) (hρ : ¬ ρ.IsPure) :
    ¬ (Density.pure ρ.purify).IsSeparable := by
  rw [Density.isSeparable_pure_iff_isPure_partialTraceRight,
    ρ.partialTraceRight_pure_purify]
  exact hρ

-- In particular, the maximally mixed qubit has an entangled purification.
example : let ρ := Density.maximallyMixed Qubit (by simp [Qubit])
    ¬ (Density.pure ρ.purify).IsSeparable := by
  dsimp only
  rw [Density.isSeparable_pure_iff_isPure_partialTraceRight,
    Density.partialTraceRight_pure_purify, Density.isPure_iff_finrank_range_eq_one]
  have hop : (Density.maximallyMixed Qubit (by simp [Qubit])).op =
      (1 / 2 : ℂ) • (1 : Operator Qubit) := by simp [Qubit]
  rw [hop, LinearMap.range_smul _ _ (by norm_num)]
  change Module.finrank ℂ (LinearMap.range (LinearMap.id : Operator Qubit)) ≠ 1
  rw [LinearMap.range_id, finrank_top]
  norm_num [Qubit]

end
