/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for unitary source rules under a classical precondition.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/BasicDerived.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.SourceRules

/-!
# Source unitary rules on a classical condition

The register and its unitary may depend on the store. Distinctness and transport of
the quantum predicate are only required on the input's classical support.
-/

@[expose] public section

open Qudit CategoryTheory DaggerCategory

namespace QuantumProgram.SourceDerivTot

variable {Store Cell : Type*} {H : Qudit} {k : ℕ}
variable (r : Store → Fin k → Cell) (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H)

/-- Apply a unitary under a classical condition and compare the pulled-back effect there. -/
theorem unitary_of_le {A B : Assertion Store H} {φ χ : Store → Prop}
    (hc : ∀ σ, φ σ → χ σ) (hr : ∀ σ, φ σ → Function.Injective (r σ))
    (hq : ∀ σ, φ σ → A σ ≤ B.unitaryPre r U σ) :
    SourceDerivTot (.ofEffect A φ) (.unitary r U) (.ofEffect B χ) := by
  apply SourceDerivTot.conseq _ (.unitary r U B φ hr) _
  · exact fun σ h => ⟨h, hq σ h⟩
  · exact fun σ h => ⟨hc σ h, le_rfl⟩

/-- A unitary transporting a family of unit vectors transports their sharp assertions. -/
theorem unitary_pure {φ : Store → Prop} (v w : Store → UnitState H)
    (hr : ∀ σ, φ σ → Function.Injective (r σ))
    (hU : ∀ σ (h : φ σ), (U σ (hr σ h)).toOperator (v σ) = w σ) :
    SourceDerivTot (.ofEffect (fun σ => Assertion.pure (v σ) σ) φ) (.unitary r U)
      (.ofEffect (fun σ => Assertion.pure (w σ) σ) φ) := by
  apply unitary_of_le r U (fun _ h => h) hr
  intro σ h
  apply le_of_eq
  apply Subtype.ext
  simp only [Assertion.unitaryPre, dite_eq_left (hr σ h)]
  let f := (U σ (hr σ h)).denoteHom
  change Operator.outer (v σ).val (v σ).val =
    (CPQudit.pure.map f)†.toSuperoperator (Operator.outer (w σ).val (w σ).val)
  rw [CPQudit.dagger_pure]
  change _ = Superoperator.conjugate (H := H) (K := H) f.hom.adjoint
    (Operator.outer (H := H) (w σ).val (w σ).val)
  have hw : f.hom (v σ) = w σ := hU σ h
  rw [← hw, Superoperator.conjugate_outer, hom_adjoint_apply_of_isIsometry]

/-- On a defined register a unitary preserves the identity and the classical condition. -/
theorem unitary_identity (φ : Store → Prop) (hr : ∀ σ, φ σ → Function.Injective (r σ)) :
    SourceDerivTot (.ofEffect Assertion.identity φ) (.unitary r U)
      (.ofEffect Assertion.identity φ) := by
  apply unitary_of_le r U (fun _ h => h) hr
  intro σ h
  simp only [Assertion.unitaryPre, dite_eq_left (hr σ h)]
  let Φ := (U σ (hr σ h)).toChannel
  exact (Φ.toCPMap.isTracePreserving_iff_dual_one.mp Φ.tracePreserving).ge

end QuantumProgram.SourceDerivTot
