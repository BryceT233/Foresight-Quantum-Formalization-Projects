/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for pure-state invariants for counted unitary circuits.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/CountedStateChain.lean
Qhl/Examples/QFTArbitrary.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.Source.Counted
public import FQFP.QuantumProgram.Logic.Source.Unitary

/-!
# Counted circuits on arbitrary pure inputs

The invariant after each pass is the input vector acted on by the preceding gates.
The body may itself be a command with loops.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

variable {H : Qudit}

/-- For a single unitary body, register injectivity on active stores certifies every rank layer. -/
theorem SourceDerivTot.countedGateFamily {Store Cell : Type*} {arity : ℕ} (c : CounterLens Store)
    (bound : Store → ℕ) (P : Store → Prop) (hP : ∀ σ k, P (c.set σ k) ↔ P σ)
    (hb : ∀ σ k, bound (c.set σ k) = bound σ) (J : ℕ → Assertion Store H)
    (hJ : ∀ k σ t, J k (c.set σ t) = J k σ) (r : Store → Fin arity → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H)
    (hr : ∀ σ, P σ → c.get σ < bound σ → Function.Injective (r σ))
    (step : let active := fun σ => P σ ∧ c.get σ < bound σ
      SourceDerivTot (.ofEffect (fun σ => J (c.get σ) σ) active) (.unitary r U)
        (.ofEffect (fun σ => J (c.get σ + 1) σ) active)) :
    SourceDerivTot (.ofEffect (J 0) P) (.counted c bound (.unitary r U))
      (.ofEffect (fun σ => J (bound σ) σ) fun σ => P σ ∧ c.get σ = bound σ) :=
  countedFamily c bound P hP hb J hJ _ step fun _ =>
    unitary_identity _ _ _ (fun σ h => hr σ h.1 h.2.1)

/-- Evolve a unit input through the first `m` gates. -/
noncomputable def UnitaryProgram.prefixState (g : ℕ → UnitaryProgram H) (v : UnitState H)
    (m : ℕ) : UnitState H := UnitState.map (gatePrefix g m).denoteHom v

/-- One more pass advances the prefix vector by its exact gate operator. -/
theorem UnitaryProgram.prefixState_step (g : ℕ → UnitaryProgram H) (v : UnitState H) (m : ℕ) :
    (g m).toOperator (prefixState g v m).val = (prefixState g v (m + 1)).val :=
  (LinearMap.congr_fun (toOperator_gatePrefix_succ g m) v.val).symm

/-- A certified counted body transports any unit input by the ordered product of its gates. -/
theorem SourceDerivTot.countedUnitary {Store Cell : Type*} (c : CounterLens Store) (N : ℕ)
    (body : Command Store Cell H) (g : ℕ → UnitaryProgram H) (v : UnitState H)
    (step : ∀ w : ℕ → UnitState H, let active := fun σ => c.get σ < N
      SourceDerivTot (.ofEffect (fun σ => Assertion.pure (w (c.get σ)) σ) active) body
        (.ofEffect (fun σ => Assertion.pure
          (UnitState.map (g (c.get σ)).denoteHom (w (c.get σ))) σ) active))
    (rank : ∀ z : ℤ, let layer := fun σ => c.get σ < N ∧ ((N - c.get σ : ℕ) : ℤ) = z
      SourceDerivTot (.ofEffect Assertion.identity layer) body
        (.ofEffect Assertion.identity layer)) :
    SourceDerivTot (.ofEffect (Assertion.pure v) fun _ => True) (.counted c (fun _ => N) body)
      (.ofEffect (Assertion.pure (UnitaryProgram.prefixState g v N)) fun _ => True) := by
  let w := UnitaryProgram.prefixState g v
  have advance (m : ℕ) : UnitState.map (g m).denoteHom (w m) = w (m + 1) :=
    Subtype.ext (UnitaryProgram.prefixState_step g v m)
  have pass := step w
  simp only [advance] at pass
  have d := countedFamily c (fun _ => N) (fun _ => True) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (fun k => Assertion.pure (w k)) (fun _ _ _ => rfl) body
    (by simpa only [true_and] using pass) (by simpa only [true_and] using rank)
  exact .conseq (fun _ h => ⟨h, le_rfl⟩) d (fun _ _ => ⟨trivial, le_rfl⟩)

end QuantumProgram
