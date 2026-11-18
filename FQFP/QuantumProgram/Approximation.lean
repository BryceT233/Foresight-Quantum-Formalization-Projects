/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Correctness

/-!
# Finite-depth values for partial correctness

Following `Qhl/History/Approx.lean`, a horizon `N` includes terminal occurrences at depths
strictly below `N`. Each such branch contributes its post-expectation; all remaining mass
receives full credit. For effects these upper bounds decrease to `PostH + nonterminatingMass`.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal NNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

namespace Configuration

variable (c : Configuration Store Cell H)

/-- Sum a nonnegative weight over terminal occurrences at one exact depth. -/
noncomputable def terminalWeightAt (n : ℕ) (w : CQState Store H → ℝ≥0∞) : ℝ≥0∞ :=
  (((c.frontier n).filter (·.control.isNone)).map (fun d => w d.state)).sum

/-- Pointwise bounds on branch weights pass to the terminal frontier. -/
theorem terminalWeightAt_mono (n : ℕ) {f g : CQState Store H → ℝ≥0∞} (h : ∀ s, f s ≤ g s) :
    c.terminalWeightAt n f ≤ c.terminalWeightAt n g :=
  List.sum_le_sum fun d _ => h d.state

/-- Two contributions at each terminal occurrence can be summed separately. -/
theorem terminalWeightAt_add (n : ℕ) (f g : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => f s + g s) = c.terminalWeightAt n f + c.terminalWeightAt n g :=
  List.sum_map_add

/-- Using the trace as the branch weight recovers the exact-depth terminating mass. -/
theorem terminalWeightAt_mass (n : ℕ) :
    c.terminalWeightAt n (fun s => s.mass) = c.terminalMassAt n := by
  change _ = ENNReal.ofNNRealHom _
  unfold terminalMassAt
  rw [map_list_sum, List.map_map]
  rfl

/-- Each terminal branch contributes its expectation in the extended nonnegative reals. -/
noncomputable def postAtE (n : ℕ) (A : Store → Operator H) : ℝ≥0∞ :=
  c.terminalWeightAt n (fun s => ENNReal.ofReal (s.expectation (A s.store)))

/-- For positive observables the conversion to extended nonnegative reals commutes with
the sum over terminal branches. -/
theorem postAtE_eq_ofReal_postAt (n : ℕ) {A : Store → Operator H}
    (hA : ∀ σ, (A σ).IsPositive) : c.postAtE n A = ENNReal.ofReal (c.postAt n A) := by
  rw [postAtE, terminalWeightAt, postAt_eq_sum_frontier]
  simp only [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact (ENNReal.ofReal_sum_of_nonneg fun i _ => CQState.expectation_nonneg _ (hA _)).symm

/-- The post-weight at each depth is at most the trace terminating there for tests below one. -/
theorem postAtE_le_terminalMassAt (n : ℕ) {A : Store → Operator H} (hA : ∀ σ, A σ ≤ 1) :
    c.postAtE n A ≤ c.terminalMassAt n := by
  rw [← terminalWeightAt_mass]
  apply c.terminalWeightAt_mono
  intro s
  exact (ENNReal.ofReal_le_ofReal ((s.expectation_mono (hA _)).trans_eq
    s.expectation_one)).trans_eq ENNReal.ofReal_coe_nnreal

/-- The post-expectation collected before depth `N`. -/
noncomputable def postUpTo (N : ℕ) (A : Store → Operator H) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, c.postAtE n A

/-- The trace of all branches terminating before depth `N`. -/
noncomputable def terminalMassUpTo (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, (c.terminalMassAt n : ℝ≥0∞)

/-- The trace accumulated before a finite horizon fits within the input trace. -/
theorem terminalMassUpTo_le_mass (N : ℕ) : c.terminalMassUpTo N ≤ c.state.mass :=
  (ENNReal.sum_le_tsum _).trans c.terminatingMass_le

/-- Finite-depth partial-correctness value, including all mass still unaccounted for. -/
noncomputable def Val (N : ℕ) (A : Store → Operator H) : ℝ≥0∞ :=
  c.postUpTo N A + ((c.state.mass : ℝ≥0∞) - c.terminalMassUpTo N)

/-- At horizon zero the whole trace is outstanding. -/
theorem Val_zero (A : Store → Operator H) : c.Val 0 A = c.state.mass := by
  simp [Val, postUpTo, terminalMassUpTo]

/-- For a running command, no mass has terminated strictly before depth one. -/
theorem Val_one_of_running (p : Command Store Cell H) (s : CQState Store H)
    (A : Store → Operator H) : (Configuration.mk (some p) s).Val 1 A = s.mass := by
  simp [Val, postUpTo, terminalMassUpTo, postAtE, terminalWeightAt, terminalMassAt, frontier]

/-- A deterministic, mass-preserving step consumes one unit of the finite horizon. -/
theorem Val_succ_singleton {c d : Configuration Store Cell H} (hnext : c.next = [d])
    (hm : c.state.mass = d.state.mass) (N : ℕ) (A : Store → Operator H) :
    c.Val (N + 1) A = d.Val N A := by
  have hrun : c.control.isNone = false := by
    obtain ⟨_ | p, s⟩ := c
    · simp [next] at hnext
    · rfl
  have hfront : c.frontier 1 = [d] := by simpa [frontier] using hnext
  have shift (w : CQState Store H → ℝ≥0∞) :
      ∑ i ∈ Finset.range (N + 1), c.terminalWeightAt i w =
        ∑ i ∈ Finset.range N, d.terminalWeightAt i w := by
    have hs (i : ℕ) : c.terminalWeightAt (i + 1) w = d.terminalWeightAt i w := by
      rw [terminalWeightAt, Nat.add_comm i 1, frontier_add_of_singleton hfront]
      rfl
    simp only [Finset.sum_range_succ', hs]
    simp [terminalWeightAt, frontier, hrun]
  simp only [Val, postUpTo, terminalMassUpTo, postAtE, ← terminalWeightAt_mass, shift, hm]

/-- A positive horizon sees the whole post-weight of an already terminated configuration. -/
theorem Val_succ_terminal (s : CQState Store H) (N : ℕ) (A : Store → Operator H) :
    (Configuration.mk (Cell := Cell) none s).Val (N + 1) A =
      ENNReal.ofReal (s.expectation (A s.store)) := by
  let c := Configuration.mk (Cell := Cell) none s
  have hf (n : ℕ) : c.frontier (n + 1) = [] := by
    induction n with
    | zero => simp [c, frontier, next]
    | succ n ih => exact congrArg (List.flatMap Configuration.next) ih
  change c.Val (N + 1) A = _
  simp only [Val, postUpTo, terminalMassUpTo, Finset.sum_range_succ', postAtE,
    terminalWeightAt, terminalMassAt, hf]
  simp [frontier, c]

/-- Extending the horizon decreases the upper bound for observables bounded by one. -/
theorem antitone_Val {A : Store → Operator H} (hA : ∀ σ, A σ ≤ 1) :
    Antitone (fun N => c.Val N A) := by
  apply antitone_nat_of_succ_le
  intro N
  have hnext : c.terminalMassUpTo N + c.terminalMassAt N ≤ c.state.mass := by
    simpa only [terminalMassUpTo, Finset.sum_range_succ] using c.terminalMassUpTo_le_mass (N + 1)
  have hroom := ENNReal.le_sub_of_add_le_left
    ((c.terminalMassUpTo_le_mass N).trans_lt ENNReal.coe_lt_top).ne hnext
  simp only [Val, postUpTo, terminalMassUpTo, Finset.sum_range_succ, add_assoc,
    tsub_add_eq_tsub_tsub]
  exact add_le_add le_rfl ((add_le_add (c.postAtE_le_terminalMassAt N hA) le_rfl).trans_eq
    (add_tsub_cancel_of_le hroom))

/-- The finite-depth values converge to the post-expectation plus residual trace. -/
theorem tendsto_Val {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    Tendsto (fun N => c.Val N A) atTop (𝓝 (c.PostH A + c.nonterminatingMass)) := by
  have hp : Tendsto (fun N => c.postUpTo N A) atTop (𝓝 (c.PostH A)) := by
    simpa only [postUpTo, PostH, c.postAtE_eq_ofReal_postAt _ hA] using
      ENNReal.tendsto_nat_tsum (fun n => c.postAtE n A)
  exact hp.add (ENNReal.Tendsto.sub tendsto_const_nhds
    (ENNReal.tendsto_nat_tsum (fun n => (c.terminalMassAt n : ℝ≥0∞))) (Or.inl ENNReal.coe_ne_top))

/-- Every finite horizon bounds the limiting yield for an assertion. -/
theorem PostH_add_nonterminatingMass_le_Val (B : Assertion Store H) (N : ℕ) :
    c.PostH (fun σ => B σ) + c.nonterminatingMass ≤ c.Val N (fun σ => B σ) :=
  (c.antitone_Val (fun σ => (B σ).2.2)).le_of_tendsto
    (c.tendsto_Val (fun σ => LinearMap.nonneg_iff_isPositive.mp (B σ).2.1)) N

/-- A lower bound at every horizon passes to the limit for any positive post-observable. -/
theorem le_PostH_add_nonterminatingMass_of_forall_le_Val {A : Store → Operator H}
    (hA : ∀ σ, (A σ).IsPositive) {x : ℝ≥0∞} (h : ∀ N, x ≤ c.Val N A) :
    x ≤ c.PostH A + c.nonterminatingMass := ge_of_tendsto' (c.tendsto_Val hA) h

/-- For an assertion, the infimum over finite horizons equals the partial-correctness yield. -/
theorem iInf_Val (B : Assertion Store H) :
    (⨅ N, c.Val N (fun σ => B σ)) = c.PostH (fun σ => B σ) + c.nonterminatingMass :=
  le_antisymm (c.le_PostH_add_nonterminatingMass_of_forall_le_Val
    (fun σ => LinearMap.nonneg_iff_isPositive.mp (B σ).2.1) (iInf_le _))
    (le_iInf (c.PostH_add_nonterminatingMass_le_Val B))

end Configuration

/-- Partial validity is equivalent to bounding the initial expectation at every finite horizon. -/
theorem validPar_iff_forall_le_Val {A B : Assertion Store H} {p : Command Store Cell H} :
    validPar A p B ↔ ∀ (s : CQState Store H) (N : ℕ), ENNReal.ofReal (s.expectation (A s.store)) ≤
      (Configuration.mk (some p) s).Val N (fun σ => B σ) := by
  unfold validPar
  exact forall_congr' fun s => by rw [← Configuration.iInf_Val _ B, le_iInf_iff]

end QuantumProgram
