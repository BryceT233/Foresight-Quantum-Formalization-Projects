/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for lifting a command to an extended classical store.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/StoreLens.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.CountedLoop
public import FQFP.QuantumProgram.Logic.For

/-!
# Commands on an extended classical store

Reads pass through a projection and writes replace the selected part of the store.
The quantum actions, register checks and control flow are those of the original command.
-/

@[expose] public section

open Qudit

namespace QuantumProgram

/-- Read and replace a component of a classical store. -/
structure StoreLens (Large Small : Type*) where
  /-- Read the component. -/
  get : Large → Small
  /-- Replace the component in the enclosing store. -/
  put : Large → Small → Large

variable {S T R Cell : Type*} {H : Qudit}

/-- The first component is writable and the second is read-only. -/
def StoreLens.fst : StoreLens (S × R) S := ⟨Prod.fst, fun σ s => (s, σ.2)⟩

/-- Run a command through a store lens, including measurement write-backs. -/
def Command.mapStore (l : StoreLens T S) : Command S Cell H → Command T Cell H
  | .skip => .skip
  | .assign f => .assign fun σ => l.put σ (f (l.get σ))
  | .channel f => .channel (f ∘ l.get)
  | .unitary r U => .unitary (r ∘ l.get) fun σ => U (l.get σ)
  | .measure r I upd => .measure (r ∘ l.get) (fun σ => I (l.get σ))
      fun i σ => l.put σ (upd i (l.get σ))
  | .seq p q => (p.mapStore l).seq (q.mapStore l)
  | .ite b p q => .ite (b ∘ l.get) (p.mapStore l) (q.mapStore l)
  | .whileDo b p => .whileDo (b ∘ l.get) (p.mapStore l)

/-- Every classical write in the transported command preserves any parameter fixed by the lens. -/
theorem Command.preservesParameters_mapStore (p : Command S Cell H) (l : StoreLens T S)
    (read : T → R) (h : ∀ σ s, read (l.put σ s) = read σ) :
    (p.mapStore l).PreservesParameters read := by
  induction p <;> simp_all [mapStore, PreservesParameters]

/-- Transport commutes with iteration over a list. -/
theorem Command.mapStore_forList {ι : Type*} (l : StoreLens T S) (xs : List ι)
    (body : ι → Command S Cell H) :
    (forList xs body).mapStore l = forList xs fun i => (body i).mapStore l := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [forList_cons, mapStore, ih]

/-- A counter on a component can be used in the larger store if writes can be read back. -/
def CounterLens.pullback (c : CounterLens S) (l : StoreLens T S)
    (h : ∀ σ s, l.get (l.put σ s) = s) : CounterLens T where
  get := c.get ∘ l.get
  set σ k := l.put σ (c.set (l.get σ) k)
  get_set σ k := by simp only [Function.comp_apply, h, c.get_set]

/-- Transport the reset, guard, body and increment of a counted command. -/
theorem Command.mapStore_counted (c : CounterLens S) (l : StoreLens T S)
    (h : ∀ σ s, l.get (l.put σ s) = s) (bound : S → ℕ) (body : Command S Cell H) :
    (counted c bound body).mapStore l = counted (c.pullback l h) (bound ∘ l.get)
      (body.mapStore l) := rfl

end QuantumProgram
