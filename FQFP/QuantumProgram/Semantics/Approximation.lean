/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for finite-depth values and the criterion for partial correctness.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/History/Approx.lean
Qhl/History/SeqDecomp.lean
Qhl/Logic/Assertion.lean

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Correctness
import FQFP.Algebra.BigOperators.Group.List.Fin

/-!
# Finite-depth values for partial correctness

Following `Qhl/History/Approx.lean`, a horizon `N` includes terminal occurrences at depths
strictly below `N`. Each such branch contributes its post-expectation; all remaining mass
receives full credit. For effects these upper bounds decrease to `PostH + nonterminatingMass`.
Summing terminal weights over all depths also gives a common form for full execution statistics.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal NNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

private theorem tsum_sum_map {α ι : Type*} (l : List α) (f : α → ι → ℝ≥0∞) :
    (∑' i, (l.map fun a => f a i).sum) = (l.map fun a => ∑' i, f a i).sum := by
  simp only [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

namespace Configuration

variable (c : Configuration Store Cell H)

/-- Sum a nonnegative weight over terminal occurrences at one exact depth. -/
noncomputable def terminalWeightAt (n : ℕ) (w : CQState Store H → ℝ≥0∞) : ℝ≥0∞ :=
  (((c.frontier n).filter (·.control.isNone)).map (fun d => w d.state)).sum

/-- At depth zero only an already terminal configuration contributes a weight. -/
theorem terminalWeightAt_zero (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt 0 w = if c.control.isNone then w c.state else 0 := by
  by_cases h : c.control.isNone <;> simp [terminalWeightAt, frontier, h]

/-- Exact-depth terminal weights after one step sum over all one-step successors. -/
theorem terminalWeightAt_succ (n : ℕ) (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt (n + 1) w = (c.next.map (·.terminalWeightAt n w)).sum := by
  unfold terminalWeightAt
  rw [frontier_succ, List.filter_flatMap, List.map_flatMap, List.flatMap_def,
    List.sum_flatten, List.map_map, Function.comp_def]

/-- A positive horizon counts the root and sums each successor's contribution at the shorter
horizon. -/
theorem sum_terminalWeightAt_succ (N : ℕ) (w : CQState Store H → ℝ≥0∞) :
    ∑ i ∈ Finset.range (N + 1), c.terminalWeightAt i w =
      c.terminalWeightAt 0 w + (c.next.map fun d => ∑ i ∈ Finset.range N,
        d.terminalWeightAt i w).sum := by
  rw [Finset.sum_range_succ', add_comm]
  simp only [terminalWeightAt_succ, TrotterError.List.sum_map_sum]

/-- A single successor consumes one unit of the horizon for any terminal weight. -/
theorem sum_terminalWeightAt_succ_of_next_eq_singleton {c d : Configuration Store Cell H}
    (h : c.next = [d]) (N : ℕ) (w : CQState Store H → ℝ≥0∞) :
    ∑ i ∈ Finset.range (N + 1), c.terminalWeightAt i w =
      ∑ i ∈ Finset.range N, d.terminalWeightAt i w := by
  obtain ⟨_ | p, s⟩ := c
  · simp [next] at h
  · simp [sum_terminalWeightAt_succ, terminalWeightAt_zero, h]

/-- Total terminal weight splits into the root's contribution and the sums for each successor. -/
theorem tsum_terminalWeightAt_eq_zero_add_sum_next (w : CQState Store H → ℝ≥0∞) :
    (∑' n, c.terminalWeightAt n w) =
      c.terminalWeightAt 0 w + (c.next.map fun d => ∑' n, d.terminalWeightAt n w).sum := by
  rw [tsum_eq_zero_add' CompleteLattice.summable]
  simp only [terminalWeightAt_succ, tsum_sum_map]

/-- Pointwise bounds on branch weights pass to the terminal frontier. -/
theorem terminalWeightAt_mono (n : ℕ) {f g : CQState Store H → ℝ≥0∞} (h : ∀ s, f s ≤ g s) :
    c.terminalWeightAt n f ≤ c.terminalWeightAt n g :=
  List.sum_le_sum fun d _ => h d.state

/-- Two contributions at each terminal occurrence can be summed separately. -/
theorem terminalWeightAt_add (n : ℕ) (f g : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => f s + g s) = c.terminalWeightAt n f + c.terminalWeightAt n g :=
  List.sum_map_add

/-- Sum a finite family of weights before or after summing over terminal occurrences. -/
theorem terminalWeightAt_finsetSum {ι : Type*} (n : ℕ) (u : Finset ι)
    (f : ι → CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => ∑ i ∈ u, f i s) = ∑ i ∈ u, c.terminalWeightAt n (f i) :=
  TrotterError.List.sum_map_sum _ u (fun d i => f i (Configuration.state d))

/-- Nonnegative series commute with the finite sum over terminal occurrences at any depth. -/
theorem terminalWeightAt_tsum {ι : Type*} (n : ℕ) (f : ι → CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => ∑' i, f i s) = ∑' i, c.terminalWeightAt n (f i) := by
  unfold terminalWeightAt
  exact (tsum_sum_map _ (fun (d : Configuration Store Cell H) i => f i d.state)).symm

/-- A constant factor can be pulled out of the sum over a terminal frontier. -/
theorem terminalWeightAt_const_mul (n : ℕ) (a : ℝ≥0∞) (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => a * w s) = a * c.terminalWeightAt n w :=
  List.sum_map_mul_left _ (w ∘ Configuration.state) a

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

/-- Accumulate a positive observable by summing its nonnegative branch weights at each depth. -/
theorem PostH_eq_tsum_terminalWeightAt {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    c.PostH A = ∑' n, c.terminalWeightAt n (fun s => ENNReal.ofReal (s.expectation (A s.store))) :=
  tsum_congr fun n => (c.postAtE_eq_ofReal_postAt n hA).symm

/-- Sum a continuation weight over all terminal occurrences of the configuration. -/
noncomputable def terminalWeight (w : CQState Store H → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, c.terminalWeightAt n w

/-- The root's contribution and its successors' weights account for every terminal occurrence. -/
theorem terminalWeight_eq_zero_add_sum_next (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeight w = c.terminalWeightAt 0 w + (c.next.map (·.terminalWeight w)).sum :=
  c.tsum_terminalWeightAt_eq_zero_add_sum_next w

/-- A running configuration with one successor has that successor's total terminal weight. -/
theorem terminalWeight_singleton {p : Command Store Cell H} {s : CQState Store H}
    {d : Configuration Store Cell H} (h : (Configuration.mk (some p) s).next = [d])
    (w : CQState Store H → ℝ≥0∞) : (Configuration.mk (some p) s).terminalWeight w =
      d.terminalWeight w := by
  rw [terminalWeight_eq_zero_add_sum_next, h]
  simp [terminalWeightAt_zero]

/-- Comparing weights at reachable terminal states suffices to compare their sums. -/
theorem terminalWeight_le_of_mem_frontier {v w : CQState Store H → ℝ≥0∞}
    (h : ∀ n t, ⟨none, t⟩ ∈ c.frontier n → v t ≤ w t) :
    c.terminalWeight v ≤ c.terminalWeight w := by
  refine tsum_le_tsum fun n => List.sum_le_sum ?_
  rintro ⟨control, t⟩ ht
  obtain ⟨hmem, hnone⟩ := List.mem_filter.mp ht
  cases control with
  | none => exact h n t hmem
  | some q => contradiction

/-- Weights that agree at reachable terminal states have the same total terminal weight. -/
theorem terminalWeight_congr_of_mem_frontier {v w : CQState Store H → ℝ≥0∞}
    (h : ∀ n t, ⟨none, t⟩ ∈ c.frontier n → v t = w t) :
    c.terminalWeight v = c.terminalWeight w :=
  le_antisymm (c.terminalWeight_le_of_mem_frontier fun n t ht => (h n t ht).le)
    (c.terminalWeight_le_of_mem_frontier fun n t ht => (h n t ht).ge)

/-- Pointwise comparison of weights passes to the total terminal weight. -/
theorem terminalWeight_mono : Monotone c.terminalWeight :=
  fun _ _ h => tsum_le_tsum fun n => c.terminalWeightAt_mono n h

/-- Adding two weights adds their total terminal weights. -/
theorem terminalWeight_add (v w : CQState Store H → ℝ≥0∞) :
    c.terminalWeight (fun t => v t + w t) = c.terminalWeight v + c.terminalWeight w := by
  simp only [terminalWeight, terminalWeightAt_add, tsum_add]

/-- A constant factor can be pulled out of the total terminal weight. -/
theorem terminalWeight_const_mul (a : ℝ≥0∞) (w : CQState Store H → ℝ≥0∞) :
    c.terminalWeight (fun t => a * w t) = a * c.terminalWeight w := by
  simp only [terminalWeight, terminalWeightAt_const_mul, ENNReal.tsum_mul_left]

/-- Total terminal weight commutes with a finite sum of weights. -/
theorem terminalWeight_finsetSum {ι : Type*} (u : Finset ι) (w : ι → CQState Store H → ℝ≥0∞) :
    c.terminalWeight (fun t => ∑ i ∈ u, w i t) = ∑ i ∈ u, c.terminalWeight (w i) := by
  simp only [terminalWeight, terminalWeightAt_finsetSum]
  exact Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable

/-- Total terminal weight commutes with a nonnegative series of weights. -/
theorem terminalWeight_tsum {ι : Type*} (w : ι → CQState Store H → ℝ≥0∞) :
    c.terminalWeight (fun t => ∑' i, w i t) = ∑' i, c.terminalWeight (w i) := by
  simp only [terminalWeight, terminalWeightAt_tsum]
  exact tsum_comm

/-- Weighting each terminal occurrence by its trace gives the terminating mass. -/
theorem terminalWeight_mass : c.terminalWeight (fun t => t.mass) = c.terminatingMass := by
  simp only [terminalWeight, terminalWeightAt_mass, terminatingMass]

/-- Weighting terminal occurrences by expectations of a positive observable gives its
post-expectation. -/
theorem terminalWeight_expectation {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    c.terminalWeight (fun t => ENNReal.ofReal (t.expectation (A t.store))) = c.PostH A :=
  (c.PostH_eq_tsum_terminalWeightAt hA).symm

/-- The post-weight at each depth is at most the trace terminating there for tests below one. -/
theorem postAtE_le_terminalMassAt (n : ℕ) {A : Store → Operator H} (hA : ∀ σ, A σ ≤ 1) :
    c.postAtE n A ≤ c.terminalMassAt n := by
  rw [← terminalWeightAt_mass]
  exact c.terminalWeightAt_mono n fun s => s.ofReal_expectation_le_mass (hA _)

/-- The post-expectation collected before depth `N`. -/
noncomputable def postUpTo (N : ℕ) (A : Store → Operator H) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, c.postAtE n A

/-- At a positive horizon, add the root's post-weight to those of the one-step successors. -/
theorem postUpTo_succ (N : ℕ) (A : Store → Operator H) :
    c.postUpTo (N + 1) A = c.postAtE 0 A + (c.next.map (·.postUpTo N A)).sum :=
  c.sum_terminalWeightAt_succ N _

/-- With one successor, the post-expectation before the horizon resumes one step later. -/
theorem postUpTo_succ_singleton {c d : Configuration Store Cell H} (h : c.next = [d])
    (N : ℕ) (A : Store → Operator H) : c.postUpTo (N + 1) A = d.postUpTo N A :=
  sum_terminalWeightAt_succ_of_next_eq_singleton h N _

/-- The trace of all branches terminating before depth `N`. -/
noncomputable def terminalMassUpTo (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, (c.terminalMassAt n : ℝ≥0∞)

/-- The trace accumulated before a finite horizon fits within the input trace. -/
theorem terminalMassUpTo_le_mass (N : ℕ) : c.terminalMassUpTo N ≤ c.state.mass :=
  (sum_le_tsum _).trans c.terminatingMass_le

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
  simp only [Val, postUpTo, terminalMassUpTo, postAtE, ← terminalWeightAt_mass,
    sum_terminalWeightAt_succ_of_next_eq_singleton hnext, hm]

/-- A positive horizon sees the whole post-weight of an already terminated configuration. -/
theorem Val_succ_terminal (s : CQState Store H) (N : ℕ) (A : Store → Operator H) :
    (Configuration.mk (Cell := Cell) none s).Val (N + 1) A =
      ENNReal.ofReal (s.expectation (A s.store)) := by
  simp [Val, postUpTo, terminalMassUpTo, postAtE, ← terminalWeightAt_mass,
    sum_terminalWeightAt_succ, terminalWeightAt_zero, next]

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

/-- Terminal post-expectations accumulated before a finite horizon converge to the full sum. -/
theorem tendsto_postUpTo {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    Tendsto (fun N => c.postUpTo N A) atTop (𝓝 (c.PostH A)) := by
  simpa only [postUpTo, PostH, c.postAtE_eq_ofReal_postAt _ hA] using
    ENNReal.tendsto_nat_tsum (fun n => c.postAtE n A)

/-- A finite horizon collects at most the full terminal expectation of a positive observable. -/
theorem postUpTo_le_PostH (N : ℕ) {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    c.postUpTo N A ≤ c.PostH A := by
  simp only [postUpTo, PostH, c.postAtE_eq_ofReal_postAt _ hA]
  exact sum_le_tsum _

/-- The finite-depth values converge to the post-expectation plus residual trace. -/
theorem tendsto_Val {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    Tendsto (fun N => c.Val N A) atTop (𝓝 (c.PostH A + c.nonterminatingMass)) :=
  (c.tendsto_postUpTo hA).add (ENNReal.Tendsto.sub tendsto_const_nhds
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
