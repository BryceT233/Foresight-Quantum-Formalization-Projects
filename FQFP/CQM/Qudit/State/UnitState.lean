/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Basic

/-!
# Unit vectors in a qudit

`Qudit.UnitState` bundles a vector with the existing normalization predicate.
It does not identify vectors differing by a global phase. Isometric morphisms act on
unit states, and every orthonormal basis supplies unit states.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DaggerCategory

namespace Qudit

/-- The existing inner-product normalization is equivalent to unit norm. -/
lemma state.normalized_iff_norm_eq_one {H : Qudit} (v : H.state) :
    state.Normalized v ↔ ‖v‖ = 1 := by
  constructor
  · intro h
    have hsq : ‖v‖ ^ 2 = 1 := (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm.trans
      (congrArg Complex.re h)
    nlinarith [norm_nonneg v]
  · exact inner_self_eq_one_of_norm_eq_one

/-- A unit vector, before quotienting by global phase. -/
abbrev UnitState (H : Qudit) := {v : H.state // state.Normalized v}

namespace UnitState

variable {H K : Qudit}

/-- A bundled unit state has inner square one. -/
lemma inner_self (v : UnitState H) : inner ℂ (v : H.state) v = 1 := v.property

/-- A bundled unit state has norm one. -/
@[simp]
lemma norm_eq_one (v : UnitState H) : ‖(v : H.state)‖ = 1 :=
  (state.normalized_iff_norm_eq_one (H := H) v.val).mp v.property

/-- A unit state is nonzero. -/
lemma ne_zero (v : UnitState H) : (v : H.state) ≠ 0 := by
  intro h
  have := v.norm_eq_one
  simp [h] at this

/-- An isometric process sends a unit state to a unit state. -/
def map (f : H ⟶ K) [IsIsometry f] (v : UnitState H) : UnitState K :=
  ⟨f v, by simpa only [state.Normalized, inner_map_map_of_isIsometry] using v.property⟩

/-- The underlying vector of the image of a unit state. -/
@[simp]
lemma coe_map (f : H ⟶ K) [IsIsometry f] (v : UnitState H) :
    (map f v : K.state) = f v := rfl

/-- Multiplication by a scalar of modulus one preserves normalization. -/
def phase (c : ℂ) (hc : ‖c‖ = 1) (v : UnitState H) : UnitState H :=
  ⟨c • v.val, (state.normalized_iff_norm_eq_one (H := H) _).mpr (by
    rw [norm_smul, hc, v.norm_eq_one, mul_one])⟩

/-- The vector underlying a change of global phase. -/
@[simp]
lemma coe_phase (c : ℂ) (hc : ‖c‖ = 1) (v : UnitState H) :
    (phase c hc v : H.state) = c • v.val := rfl

/-- An orthonormal basis vector as a unit state. -/
noncomputable def ofBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H.state) (i : ι) : UnitState H :=
  ⟨b i, inner_self_eq_one_of_norm_eq_one (b.norm_eq_one i)⟩

/-- The vector underlying a basis state. -/
@[simp]
lemma coe_ofBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H.state) (i : ι) :
    (ofBasis b i : H.state) = b i := rfl

/-- A zero-dimensional state space has no unit states. -/
instance [Subsingleton H.state] : IsEmpty (UnitState H) :=
  ⟨fun v => v.ne_zero (Subsingleton.elim _ _)⟩

end UnitState

end Qudit
