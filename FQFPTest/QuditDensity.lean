/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

import FQFP.CQM.Qudit.State.Density
import FQFP.CQM.Qudit.Measurement.Basic

/-!
# Density-state and Dirac-notation regressions

These examples check notation alongside tuple syntax, the order of bra/ket composition,
global phase, singular pure states, mixed computational-basis probabilities and coordinate
reconstruction. They also connect density expectations with the existing Born-rule API.
-/

open CategoryTheory Qudit
open scoped Qudit.Braket ComplexOrder

-- The Unicode notation works alongside tuple constructors.
example {H : Qudit} (v w : H.state) :
    ((⟨v∣) w, ∣w⟩ (1 : ℂ)) = ⟨inner ℂ v w, w⟩ := by simp [bra, ket]

example {H : Qudit} (v w : H.state) : ⟨v‖w⟩ = inner ℂ v w := rfl

-- The order is essential: ket after bra acts on H, while bra after ket acts on ℂ.
example {H : Qudit} (v w x : H.state) :
    (∣v⟩ ∘ₗ ⟨w∣) x = ⟨w‖x⟩ • v := rfl

example {H : Qudit} (v w : H.state) (z : ℂ) :
    (⟨w∣ ∘ₗ ∣v⟩) z = z * ⟨w‖v⟩ := by simp [bra, ket, inner_smul_right]

example {H : Qudit} (v : UnitState H) :
    Density.pure (v.phase Complex.I (by simp)) = Density.pure v := by simp

-- No spurious default density state is introduced on the zero space.
example : IsEmpty (UnitState (std 0)) := inferInstance

example : IsEmpty (Density (std 0)) := inferInstance

noncomputable section

local notation "v₀" => UnitState.ofBasis (ZBasis 2) (0 : Fin 2)
local notation "v₁" => UnitState.ofBasis (ZBasis 2) (1 : Fin 2)
local notation "ρ₀" => Density.pure v₀
local notation "ρ₁" => Density.pure v₁
local notation "E₀" => Operator.outer (ZBasis 2 0) (ZBasis 2 0)

-- A pure density operator is permitted to have a nontrivial kernel.
example : (ρ₀).op (ZBasis 2 1) = 0 := by
  simp

example : (ρ₀).expectation E₀ = 1 := by
  simp [Operator.outer_apply]

example : (ρ₁).expectation E₀ = 0 := by
  simp [Operator.outer_apply]

-- A classical fair mixture yields probability 1/2 for computational outcome zero.
example : (Density.mix (1 / 2) (by norm_num) (by norm_num) ρ₀ ρ₁).expectation E₀ = 1 / 2 := by
  rw [Density.expectation_mix]
  simp [Operator.outer_apply]

-- Reconstruction also works in a different orthonormal coordinate system.
example (ρ : Density Qubit) (b : OrthonormalBasis (Fin 2) ℂ Qubit.state) :
    Density.ofMatrix b (ρ.toMatrix b) (ρ.posSemidef_toMatrix b) (ρ.trace_toMatrix b) = ρ := by
  simp

-- Hadamard evolution agrees on unit vectors and their pure density operators.
example : (ρ₀).map Qubit.H.asHom = Density.pure ((v₀).map Qubit.H.asHom) := by
  rw [Density.map_pure]

-- The new mixed-state interface recovers the existing pure-state Born scalar.
example {H : Qudit} (v : UnitState H) (w : H.state) :
    (Density.pure v).expectation (Operator.outer w w) =
      (scalarRingEquiv (CategoryTheory.MonoidalCategory.probability
        (ketArrow v.val) (braArrow w))).re := by
  rw [scalarRingEquiv_probability_ketArrow_braArrow, Density.expectation_pure]
  simp only [Operator.outer_apply, inner_smul_right]
  rw [← inner_conj_symm v.val w, Complex.mul_conj']

end
