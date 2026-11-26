/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for step mass and the terminating and nonterminating traces.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Program/Spec.lean
Qhl/History/Denotation.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.ControlFlow
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Mass bounds for small-step execution

Following `Qhl/Program/Spec.lean`, the mass carried by a configuration is the trace of its
positive operator. A valid measurement redistributes this mass among its branches. A blocked
or terminal configuration contributes no successors to the next exact-depth frontier.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal ComplexOrder

namespace QuantumProgram

variable {Store Cell : Type*} {H K : Qudit}

/-- The nonnegative trace of a weighted classical–quantum state. -/
noncomputable def CQState.mass (s : CQState Store H) : ℝ≥0 :=
  ⟨s.op.trace.re, (Complex.nonneg_iff.mp s.positive.trace_nonneg).1⟩

/-- Channels preserve the mass of an unnormalized state. -/
theorem CQState.mass_map (s : CQState Store H) (Φ : QuantumChannel H K) :
    (s.map Φ).mass = s.mass := NNReal.eq (congrArg Complex.re (Φ.tracePreserving s.op))

/-- The weights of all valid measurement successors sum to the initial weight. -/
theorem sum_mass_measurementSuccessors {m k : ℕ} (r : Store → Fin k → Cell)
    (inst : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) (s : CQState Store H) (h : Function.Injective (r s.store)) :
    ((measurementSuccessors r inst upd s).map CQState.mass).sum = s.mass := by
  rw [measurementSuccessors, dite_eq_left h, List.map_ofFn, List.sum_ofFn]
  apply NNReal.eq
  rw [NNReal.coe_sum]
  exact (Complex.re_sum ..).symm.trans
    (congrArg Complex.re ((inst s.store h).sum_trace_branch s.op))

/-- The total successor mass of any running command is bounded by the input mass. -/
theorem Command.sum_mass_step_le (p : Command Store Cell H) (s : CQState Store H) :
    ((p.step s).map (fun c => c.state.mass)).sum ≤ s.mass := by
  induction p with
  | skip | assign => simp only [step, List.map_cons, List.map_nil, List.sum_singleton]; rfl
  | channel => simp [step, CQState.mass_map]
  | unitary r gate =>
    by_cases h : Function.Injective (r s.store) <;> simp [step, h, CQState.mass_map]
  | measure r inst upd =>
    by_cases h : Function.Injective (r s.store)
    · simpa [step, List.map_map, Function.comp_def] using
        (sum_mass_measurementSuccessors r inst upd s h).le
    · simp [step, measurementSuccessors_of_not_injective r inst upd s h]
  | seq p q ih _ => simpa [step, List.map_map, Function.comp_def, Configuration.seqWith] using ih
  | ite => simp [step]
  | whileDo b body _ => cases h : b s.store <;> simp [step, h]

/-- Including terminal configurations, one step never increases the total branch mass. -/
theorem Configuration.sum_mass_next_le (c : Configuration Store Cell H) :
    (c.next.map (fun d => d.state.mass)).sum ≤ c.state.mass := by
  obtain ⟨_ | p, s⟩ := c
  · simp [next]
  · exact p.sum_mass_step_le s

namespace Configuration

/-- Mass of branches that terminate at exactly depth `n`. -/
noncomputable def terminalMassAt (c : Configuration Store Cell H) (n : ℕ) : ℝ≥0 :=
  (((c.frontier n).filter (·.control.isNone)).map (·.state.mass)).sum

/-- Branches that have already terminated and the current frontier together fit within the
initial mass. In particular, a terminal branch is counted at only one depth. -/
theorem sum_terminalMassAt_add_frontier_le (c : Configuration Store Cell H) (n : ℕ) :
    ∑ k ∈ Finset.range n, c.terminalMassAt k + ((c.frontier n).map (·.state.mass)).sum ≤
      c.state.mass := by
  induction n with
  | zero => simp [frontier]
  | succ n ih =>
    rw [Finset.sum_range_succ, add_assoc]
    apply le_trans _ ih
    apply add_le_add_right
    rw [terminalMassAt, frontier, List.map_flatMap, List.flatMap_def, List.sum_flatten,
      List.map_map]
    induction c.frontier n with
    | nil => simp
    | cons d ds hd =>
      obtain ⟨_ | p, s⟩ := d
      · simpa [next, add_assoc] using add_le_add_right hd s.mass
      · simpa [next, add_left_comm, add_assoc] using add_le_add (p.sum_mass_step_le s) hd

/-- At every depth, the sum over all branch occurrences is bounded by the root's mass. -/
theorem sum_mass_frontier_le (c : Configuration Store Cell H) (n : ℕ) :
    ((c.frontier n).map (fun d => d.state.mass)).sum ≤ c.state.mass :=
  (le_add_of_nonneg_left zero_le).trans (c.sum_terminalMassAt_add_frontier_le n)

/-- The total terminating trace over all finite depths (QHL⁺ equation (7)). -/
noncomputable def terminatingMass (c : Configuration Store Cell H) : ℝ≥0∞ :=
  ∑' n, (c.terminalMassAt n : ℝ≥0∞)

/-- The mass of all terminating histories is bounded by the input trace. -/
theorem terminatingMass_le (c : Configuration Store Cell H) :
    c.terminatingMass ≤ c.state.mass := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_le_coe]
  exact (le_add_of_nonneg_right zero_le).trans (c.sum_terminalMassAt_add_frontier_le n)

/-- The nontermination quantity of QHL⁺ equation (8), including blocked mass. -/
noncomputable def nonterminatingMass (c : Configuration Store Cell H) : ℝ≥0∞ :=
  (c.state.mass : ℝ≥0∞) - c.terminatingMass

/-- Terminating mass and the residual mass sum to the original unnormalized trace. -/
theorem terminatingMass_add_nonterminatingMass (c : Configuration Store Cell H) :
    c.terminatingMass + c.nonterminatingMass = c.state.mass :=
  add_tsub_cancel_of_le c.terminatingMass_le

/-- A single terminal frontier carrying the whole input mass accounts for all terminating mass. -/
theorem terminatingMass_eq_of_frontier {c : Configuration Store Cell H} {n : ℕ}
    {s : CQState Store H} (h : c.frontier n = [⟨none, s⟩]) (hm : s.mass = c.state.mass) :
    c.terminatingMass = c.state.mass := by
  apply le_antisymm c.terminatingMass_le
  have hn : c.terminalMassAt n = c.state.mass := by simp [terminalMassAt, h, hm]
  exact (congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hn).symm.le.trans
    (le_tsum (fun k => (c.terminalMassAt k : ℝ≥0∞)) n)

end Configuration

end QuantumProgram
