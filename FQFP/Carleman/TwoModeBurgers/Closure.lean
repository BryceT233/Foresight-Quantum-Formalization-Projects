/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Carleman.TwoModeBurgers.Monomials
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Polynomial closure of the isotropically damped energy

When both damping rates agree, the energy observable is an eigenvector of the
Lie derivative. Its one-generator span is therefore a finite invariant space.

## Main result

* `TwoModeBurgers.energy_has_finite_polynomial_closure` constructs the closure.
-/

@[expose] public section

noncomputable section

namespace TwoModeBurgers

open MvPolynomial

/-- In the equal-damping model, energy is a Lie-derivative eigenvector. -/
lemma lieDerivation_energy_eq_smul (α β : ℝ) :
    (mkDerivation ℝ (vectorField α α β)) energy = (-(2 * α)) • energy := by
  rw [lieDerivation_energy_of_equal_damping]
  simp [Algebra.smul_def]

/-- Energy is a nonzero polynomial observable. -/
lemma energy_ne_zero : energy ≠ 0 := by
  intro h
  have he := congrArg (fun p : MvPolynomial (Fin 2) ℝ ↦ aeval ![(1 : ℝ), 0] p) h
  norm_num [energy] at he

/-- The invariant energy span has dimension exactly one. -/
theorem finrank_energy_span : Module.finrank ℝ (ℝ ∙ energy) = 1 :=
  finrank_span_singleton energy_ne_zero

/-- The energy span is preserved by the equal-damping Lie derivative. -/
theorem energy_span_invariant (α β : ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p ∈ ℝ ∙ energy) : (mkDerivation ℝ (vectorField α α β)) p ∈ ℝ ∙ energy := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hp
  rw [Derivation.map_smul, lieDerivation_energy_eq_smul, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨r * (-(2 * α)), rfl⟩

/-- Equal damping gives an exact finite polynomial closure of energy. -/
theorem energy_has_finite_polynomial_closure (α β : ℝ) :
    ∃ V : Submodule ℝ (MvPolynomial (Fin 2) ℝ),
      FiniteDimensional ℝ V ∧ Module.finrank ℝ V = 1 ∧ energy ∈ V ∧
        ∀ p ∈ V, (mkDerivation ℝ (vectorField α α β)) p ∈ V := by
  refine ⟨ℝ ∙ energy, ?_, finrank_energy_span,
    Submodule.mem_span_singleton_self _, ?_⟩
  · infer_instance
  · exact energy_span_invariant α β

end TwoModeBurgers
