/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.CQM.Qudit.Channel.Superoperator
public import FQFP.CQM.Qudit.Measurement.Basic

/-!
# Outer products and single Kraus branches

Conjugating an outer product evolves its ket and bra. Conversely, using an outer
product as the Kraus operator tests one vector and prepares another, as in the
measurement and preparation formula (0.42) of *Categorical Quantum Mechanics*.
Both identities hold for unnormalized vectors and rectangular processes.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace Qudit.Superoperator

variable {H K : Qudit}

/-- Conjugating an outer product applies the process to both vectors. -/
lemma conjugate_outer (f : H.state →ₗ[ℂ] K.state) (x y : H.state) :
    conjugate f (Operator.outer x y) = Operator.outer (f x) (f y) := by
  have h := congrArg Hom.hom
    (State.dagger_comp_outerHom_comp (ketArrow x) (ketArrow y) (ofHom f) (ofHom f))
  simpa only [hom_dagger_comp_comp, ketArrow_comp, hom_ofHom, ofHom_apply,
    Operator.hom_outerHom_ketArrow, Operator.outer_eq_ket_comp_bra] using h

/-- A single Kraus operator `|u⟩⟨v|` extracts the matrix coefficient at `v` and prepares
the outer square of `u`. The input operator is arbitrary. -/
lemma conjugate_ket_comp_bra_apply (u : K.state) (v : H.state) (A : Operator H) :
    conjugate (ket u ∘ₗ bra v) A = inner ℂ v (A v) • Operator.outer u u := by
  have h := congrArg Hom.hom
    (CQM.conjugate_by_outerHom (ketArrow u) (ketArrow v) (ofHom A))
  simpa only [hom_dagger_comp_comp, hom_scalar_smul, ketArrow_comp, scalarRingEquiv_overlap,
    Operator.hom_outerHom_ketArrow, hom_ofHom, ofHom_apply, Operator.outer_eq_ket_comp_bra] using h

/-- The coefficient in a rank-one branch is the trace pairing with its input effect. -/
lemma conjugate_ket_comp_bra (u : K.state) (v : H.state) (A : Operator H) :
    conjugate (ket u ∘ₗ bra v) A = (Operator.outer v v * A).trace • Operator.outer u u := by
  rw [conjugate_ket_comp_bra_apply, Operator.trace, LinearMap.trace_mul_comm,
    ← Operator.trace, Operator.trace_mul_outer]

end Qudit.Superoperator
