/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
import FQFP.QuantumProgram.Command.Measurement
import Qhl.Program.Spec

/-!
# Comparison with the Qhl small-step interpreter

This integration theorem imports Qhl revision `3dfe80b893e2ab949a0428a2e18c06153b310bd0`
with its dependencies built against FQFP's Mathlib. It lives outside the library so that
ordinary FQFP users can use measurement semantics without installing Qhl.
After building FQFP, run `lake env python tools/qhl/check_measurement.py <commit.zip>`
with the GitHub source archive for this revision.
-/

namespace QuantumProgram

open Qhl

variable {Store : Type*} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
  {D : Cell → Type} [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] {m k : ℕ}

/-- The instrument on the whole Qhl memory for a measurement on a chosen register. -/
noncomputable def registerInstrument (r : Reg Cell k) (M : QMeasure m (TSpace D r.toFun)) :
    Qudit.Instrument (Qudit.of (HS D Finset.univ)) (Qudit.of (HS D Finset.univ)) (Fin m) :=
  Qudit.Instrument.ofOperators (fun i => regLift r (M.M i)) (isQMeasure_regLift r M)

/-- Encoding the FQFP successors as terminal configurations gives exactly the output of
Qhl's interpreter, with the same control, classical store, quantum state and list order. -/
theorem map_done_measurementSuccessors_eq_stepProg [∀ j, Inhabited (D j)]
    (r : RegExpr Store Cell k) (M : ∀ σ, QMeasure m (TSpace D (r σ)))
    (upd : Fin m → Store → Store) (σ : Store) (ρ : PDensity D) :
    ((measurementSuccessors r (fun t h => registerInstrument ⟨r t, h⟩ (M t))
      upd ⟨σ, ρ.op, ρ.pos⟩).map fun s => (⟨.done, s.store, ⟨s.op, s.positive⟩⟩ : Config Store D)) =
      stepProg (.measure m k r M upd) σ ρ := by
  by_cases h : Function.Injective (r σ)
  · rw [measurementSuccessors_of_injective _ _ _ _ h, stepProg_measure _ _ _ _ _ h, List.map_map]
    rfl
  · rw [measurementSuccessors_of_not_injective _ _ _ _ h, stepProg_measure_of_not_dist _ _ _ _ _ h]
    rfl

end QuantumProgram

#print axioms QuantumProgram.map_done_measurementSuccessors_eq_stepProg
