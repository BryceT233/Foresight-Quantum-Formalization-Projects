/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for Kraus frames on evaluated quantum operations.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/KrausFrame.lean (closure and covariance of a step)
Qhl/History/KrausFrame.lean (transport of frontiers and terminal weights)

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Approximation

/-!
# Kraus conjugation through an untouched program

The local instruction set supplies evaluated whole-memory actions. A frame checks commutation
with those actions, branch by branch, and stability of the operator under classical writes.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {S Cell : Type*} {H : Qudit}

/-- Conjugate the positive operator at the current store, retaining its unnormalized weight. -/
noncomputable def CQState.krausMap (s : CQState S H) (K : S → Operator H) : CQState S H :=
  ⟨s.store, Superoperator.conjugate (K s.store) s.op, s.positive.conj_adjoint _⟩

/-- Apply a Kraus operator without changing the configuration's store or control. -/
noncomputable def Configuration.krausMap (c : Configuration S Cell H) (K : S → Operator H) :
    Configuration S Cell H := ⟨c.control, c.state.krausMap K⟩

/-- Each quantum action commutes with conjugation and each classical write preserves the frame. -/
def Command.KrausFrame (K : S → Operator H) : Command S Cell H → Prop
  | .skip => True
  | .assign f => ∀ σ, K (f σ) = K σ
  | .channel f => ∀ σ, Function.Commute (f σ).toSuperoperator (Superoperator.conjugate (K σ))
  | .unitary r U => ∀ σ (h : Function.Injective (r σ)),
      Function.Commute (U σ h).toChannel.toSuperoperator (Superoperator.conjugate (K σ))
  | .measure r I upd =>
      (∀ σ (h : Function.Injective (r σ)) i,
        Function.Commute ((I σ h).branch i) (Superoperator.conjugate (K σ))) ∧
      (∀ i σ, K (upd i σ) = K σ)
  | .seq p q | .ite _ p q => p.KrausFrame K ∧ q.KrausFrame K
  | .whileDo _ p => p.KrausFrame K

/-- Commuting whole-memory operators have commuting conjugation actions. -/
theorem commute_conjugate_of_commute {U K : Operator H} (h : Commute U K) :
    Function.Commute (Superoperator.conjugate U) (Superoperator.conjugate K) := by
  intro ρ
  have he := congrArg (fun f : Operator H => Superoperator.conjugate f) h.eq
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, Superoperator.conjugate_comp,
    Superoperator.conjugate_comp] at he
  exact LinearMap.congr_fun he ρ

/-- In particular, a disjoint-site commutation proof supplies the unitary frame. -/
theorem Command.KrausFrame.unitary_of_commute {k : ℕ} (r : S → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (K : S → Operator H)
    (h : ∀ σ hi, Commute (U σ hi).toOperator (K σ)) : (Command.unitary r U).KrausFrame K :=
  fun σ hi => commute_conjugate_of_commute (h σ hi)

/-- For a single-Kraus instrument, check the commutation of each measurement operator and
the stability of the frame under outcome write-back. -/
theorem Command.KrausFrame.measure_of_commute {k m : ℕ} (r : S → Fin k → Cell)
    (M : ∀ σ, Function.Injective (r σ) → Fin m → Operator H)
    (hM : ∀ σ hi, ∑ i, (M σ hi i).adjoint ∘ₗ M σ hi i = 1) (upd : Fin m → S → S)
    (K : S → Operator H) (hc : ∀ σ hi i, Commute (M σ hi i) (K σ))
    (hw : ∀ i σ, K (upd i σ) = K σ) :
    (Command.measure r (fun σ hi => Instrument.ofOperators (M σ hi) (hM σ hi)) upd).KrausFrame K :=
  ⟨fun σ hi i => commute_conjugate_of_commute (hc σ hi i), hw⟩

/-- A terminated control has no frame obligations. -/
def Configuration.KrausFrame (c : Configuration S Cell H) (K : S → Operator H) : Prop :=
  ∀ p ∈ c.control, p.KrausFrame K

/-- The frame obligation of a running configuration is that of its command. -/
theorem Configuration.frame_running (p : Command S Cell H) (s : CQState S H)
    (K : S → Operator H) : (Configuration.mk (some p) s).KrausFrame K ↔ p.KrausFrame K := by
  simp [KrausFrame]

/-- Each successor retains the frame on the remaining control. -/
theorem Command.KrausFrame.step_closed {K : S → Operator H} {p : Command S Cell H}
    (hp : p.KrausFrame K) (s : CQState S H) {d : Configuration S Cell H} (hd : d ∈ p.step s) :
    d.KrausFrame K := by
  induction p generalizing d with
  | skip | assign | channel =>
    simp only [step, List.mem_singleton] at hd
    subst d
    simp [Configuration.KrausFrame]
  | unitary r U =>
    simp only [step] at hd
    split at hd <;> simp_all [Configuration.KrausFrame]
  | measure r I upd =>
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hd
    simp [Configuration.KrausFrame]
  | seq p q ih _ =>
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hd
    obtain ⟨pc, t⟩ := v
    have hf := ih hp.1 hv
    cases pc with
    | none => exact (Configuration.frame_running _ _ _).2 hp.2
    | some r =>
      exact (Configuration.frame_running _ _ _).2 ⟨(Configuration.frame_running _ _ _).1 hf, hp.2⟩
  | ite b p q _ _ =>
    simp only [step, List.mem_singleton] at hd
    subst d
    apply (Configuration.frame_running _ _ _).2
    split <;> first | exact hp.1 | exact hp.2
  | whileDo b p _ =>
    cases hb : b s.store <;>
      simp only [step, hb, Bool.false_eq_true, ite_false, ite_true, List.mem_singleton] at hd <;>
      subst d
    · simp [Configuration.KrausFrame]
    · exact (Configuration.frame_running _ _ _).2 ⟨hp, hp⟩

/-- One step on the conjugated state maps the original successor list occurrence by occurrence. -/
theorem Command.KrausFrame.step_map {K : S → Operator H} {p : Command S Cell H}
    (hp : p.KrausFrame K) (s : CQState S H) :
    p.step (s.krausMap K) = (p.step s).map (·.krausMap K) := by
  induction p with
  | skip => rfl
  | assign f => simp [step, Configuration.krausMap, CQState.krausMap, hp s.store]
  | channel f =>
    simp [step, Configuration.krausMap, CQState.krausMap, CQState.map, hp s.store s.op]
  | unitary r U =>
    by_cases h : Function.Injective (r s.store)
    · simp [step, Configuration.krausMap, CQState.krausMap, CQState.map, h, hp s.store h s.op]
    · simp [step, CQState.krausMap, h]
  | measure r I upd =>
    by_cases h : Function.Injective (r s.store)
    · simp [step, measurementSuccessors, List.map_ofFn, Function.comp_def, measurementBranch,
        CQState.krausMap, Configuration.krausMap, h, hp.2, hp.1 s.store h _ s.op]
    · simp [step, measurementSuccessors, CQState.krausMap, h]
  | seq p q ih _ =>
    simp only [step, ih hp.1, List.map_map]
    rfl
  | ite => rfl
  | whileDo b p _ =>
    cases hb : b s.store <;> simp [step, CQState.krausMap, hb, Configuration.krausMap]

namespace Configuration.KrausFrame

variable {K : S → Operator H} {c d : Configuration S Cell H}

/-- The frame persists at every immediate successor of a configuration. -/
theorem next_closed (hc : c.KrausFrame K) (hd : d ∈ c.next) : d.KrausFrame K := by
  obtain ⟨_ | p, s⟩ := c
  · exact (List.not_mem_nil hd).elim
  · exact ((frame_running _ _ _).1 hc).step_closed s hd

/-- Configuration successors commute with the framed conjugation. -/
theorem next_map (hc : c.KrausFrame K) : (c.krausMap K).next = c.next.map (·.krausMap K) := by
  obtain ⟨_ | p, s⟩ := c
  · rfl
  · exact ((frame_running _ _ _).1 hc).step_map s

/-- The frame holds on the remaining commands at every finite depth. -/
theorem frontier_closed (hc : c.KrausFrame K) (n : ℕ) (hd : d ∈ c.frontier n) : d.KrausFrame K := by
  induction n generalizing d with
  | zero =>
    obtain rfl : d = c := List.mem_singleton.mp hd
    exact hc
  | succ n ih =>
    obtain ⟨v, hv, hd⟩ := List.mem_flatMap.mp hd
    exact (ih hv).next_closed hd

/-- Transport of the whole frontier preserves branch order and multiplicities. -/
theorem frontier_map (hc : c.KrausFrame K) (n : ℕ) :
    (c.krausMap K).frontier n = (c.frontier n).map (·.krausMap K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [frontier, ih, List.flatMap_map, frontier, List.map_flatMap]
    simp only [List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun d hd => (hc.frontier_closed n hd).next_map)

/-- Pull a terminal weight back along the framed conjugation at any finite depth. -/
theorem terminalWeightAt_map (hc : c.KrausFrame K) (n : ℕ) (w : CQState S H → ℝ≥0∞) :
    (c.krausMap K).terminalWeightAt n w = c.terminalWeightAt n (fun s => w (s.krausMap K)) := by
  simp only [terminalWeightAt, hc.frontier_map, List.filter_map, List.map_map, Function.comp_def]
  rfl

end Configuration.KrausFrame

end QuantumProgram
