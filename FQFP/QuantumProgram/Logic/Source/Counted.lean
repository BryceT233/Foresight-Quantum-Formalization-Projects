/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for source rules for counted loops and indexed predicate families.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/CountedWhile.lean
Qhl/Logic/Source/CountedFamily.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Command.CountedLoop
public import FQFP.QuantumProgram.Logic.PredicateGuard

/-!
# Source derivations for counted iteration

The quantum invariant and the classical rank of the loop body have independent source
derivations. The bound can depend on the classical store, and the exit counter is exact.
-/

@[expose] public section

open Qudit

namespace QuantumProgram.SourceDerivTot

variable {Store Cell : Type*} {H : Qudit}

/-- Reset a counter, iterate a source-certified body, and exit at the current bound. -/
theorem countedWhile (c : CounterLens Store) (bound : Store → ℕ) (φ : Store → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ) (hbound : ∀ σ k, bound (c.set σ k) = bound σ)
    (A : Assertion Store H) (body : Command Store Cell H)
    (hbody : SourceDerivTot (.ofEffect A fun σ => φ σ ∧ c.get σ < bound σ) body
      (.ofEffect (A ∘ fun σ => c.set σ (c.get σ + 1)) fun σ => φ σ ∧ c.get σ < bound σ))
    (hrank : ∀ z : ℤ, let layer := fun σ => φ σ ∧ c.get σ < bound σ ∧
        ((bound σ - c.get σ : ℕ) : ℤ) = z
      SourceDerivTot (.ofEffect Assertion.identity layer) body
        (.ofEffect Assertion.identity layer)) :
    SourceDerivTot (.ofEffect (A ∘ fun σ => c.set σ 0) φ) (.counted c bound body)
      (.ofEffect A fun σ => φ σ ∧ c.get σ = bound σ) := by
  let inv := fun σ => φ σ ∧ c.get σ ≤ bound σ
  let guard := fun σ => c.get σ < bound σ
  let inc := fun σ => c.set σ (c.get σ + 1)
  let rank := fun σ => ((bound σ - c.get σ : ℕ) : ℤ)
  have step : SourceDerivTot (.ofEffect A fun σ => inv σ ∧ guard σ)
      (body.seq (.assign inc)) (.ofEffect A inv) := by
    refine .conseq ?_ (.seq hbody (.conseq ?_ (.assign inc A inv) (fun _ h => ⟨h, le_rfl⟩)))
      (fun _ h => ⟨h, le_rfl⟩)
    · exact fun _ h => ⟨⟨h.1.1, h.2⟩, le_rfl⟩
    · intro σ h
      exact ⟨⟨(hφ σ _).mpr h.1, by simpa only [inc, c.get_set, hbound] using Nat.succ_le_of_lt h.2⟩,
        le_rfl⟩
  have decrease (z : ℤ) : SourceDerivTot
      (.ofEffect Assertion.identity fun σ => inv σ ∧ guard σ ∧ rank σ = z)
      (body.seq (.assign inc)) (.ofEffect Assertion.identity fun σ => rank σ < z) := by
    refine .conseq ?_ (.seq (hrank z) (.conseq ?_ (.assign inc _ _) (fun _ h => ⟨h, le_rfl⟩)))
      (fun _ h => ⟨h, le_rfl⟩)
    · exact fun _ h => ⟨⟨h.1.1, h.2⟩, le_rfl⟩
    · intro σ h
      refine ⟨?_, le_rfl⟩
      change ((bound (c.set σ _) - c.get (c.set σ _) : ℕ) : ℤ) < z
      rw [c.get_set, hbound]
      obtain ⟨_, hlt, hz⟩ := h
      lia
  have loop := SourceDerivTot.whileLoop_decide guard rank (fun _ _ => Int.natCast_nonneg _)
    step decrease
  refine .conseq ?_ (.seq (.assign (fun σ => c.set σ 0) A inv) loop) ?_
  · exact fun σ h => ⟨⟨(hφ σ 0).mpr h, by rw [c.get_set]; exact Nat.zero_le _⟩, le_rfl⟩
  · intro σ h
    exact ⟨⟨h.1.1, le_antisymm h.1.2 (Nat.le_of_not_gt h.2)⟩, le_rfl⟩

/-- Iterate a counter-indexed family of effects whose individual members ignore counter writes.
At exit the family index is the bound read from the final store. -/
theorem countedFamily (c : CounterLens Store) (bound : Store → ℕ) (φ : Store → Prop)
    (hφ : ∀ σ k, φ (c.set σ k) ↔ φ σ) (hbound : ∀ σ k, bound (c.set σ k) = bound σ)
    (J : ℕ → Assertion Store H) (hJ : ∀ k σ v, J k (c.set σ v) = J k σ)
    (body : Command Store Cell H)
    (hbody : SourceDerivTot (.ofEffect (fun σ => J (c.get σ) σ) fun σ => φ σ ∧ c.get σ < bound σ)
      body (.ofEffect (fun σ => J (c.get σ + 1) σ) fun σ => φ σ ∧ c.get σ < bound σ))
    (hrank : ∀ z : ℤ, let layer := fun σ => φ σ ∧ c.get σ < bound σ ∧
        ((bound σ - c.get σ : ℕ) : ℤ) = z
      SourceDerivTot (.ofEffect Assertion.identity layer) body
        (.ofEffect Assertion.identity layer)) :
    SourceDerivTot (.ofEffect (J 0) φ) (.counted c bound body)
      (.ofEffect (fun σ => J (bound σ) σ) fun σ => φ σ ∧ c.get σ = bound σ) := by
  let A := fun σ => J (c.get σ) σ
  apply SourceDerivTot.conseq _ (countedWhile c bound φ hφ hbound A body _ hrank) _
  · intro σ h
    refine ⟨h, le_of_eq (congrArg Subtype.val ?_)⟩
    simp only [Function.comp_apply, A, c.get_set, hJ]
  · refine .conseq (fun _ h => ⟨h, le_rfl⟩) hbody ?_
    intro σ h
    refine ⟨h, le_of_eq (congrArg Subtype.val ?_)⟩
    simp only [Function.comp_apply, A, c.get_set, hJ]
  · intro σ h
    exact ⟨h, le_of_eq (congrArg (fun k => (J k σ).val) h.2)⟩

end QuantumProgram.SourceDerivTot
