/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.CQM.Qudit.State.OperatorNorm
public import FQFP.QuantumProgram.Semantics.Approximation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Quantum output at each terminal classical store

The exact-depth outputs at a fixed store form an absolutely summable series of positive
operators. Its sum is the unnormalized quantum output at that store. Pairing these outputs
with store-dependent positive observables recovers the sum over terminating histories,
including when different histories reach the same store.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal Topology ComplexOrder

namespace QuantumProgram.Configuration

variable {Store Cell : Type*} {H : Qudit} [DecidableEq Store] (c : Configuration Store Cell H)

/-- Pairing an exact-depth output with an observable selects exactly the histories at its store. -/
theorem ofReal_trace_mul_terminalOpAt (n : ℕ) (σ : Store) {A : Operator H} (hA : A.IsPositive) :
    ENNReal.ofReal (A * c.terminalOpAt n σ).trace.re = c.terminalWeightAt n
      (fun s => if s.store = σ then ENNReal.ofReal (s.expectation A) else 0) := by
  let B (τ : Store) : Operator H := if τ = σ then A else 0
  have hB (τ) : (B τ).IsPositive := by
    by_cases h : τ = σ <;> simp [B, h, hA, LinearMap.isPositive_zero]
  have htrace : c.postAt n B = (A * c.terminalOpAt n σ).trace.re := by
    rw [postAt_eq_sum_frontier, terminalOpAt]
    induction c.frontier n with
    | nil => simp [Operator.trace]
    | cons d ds ih =>
      by_cases hd : d.control.isNone <;> by_cases hs : d.state.store = σ <;>
        simpa [hd, hs, B, CQState.expectation, mul_add, Operator.trace] using ih
  rw [← htrace, ← c.postAtE_eq_ofReal_postAt n hB]
  apply congrArg (c.terminalWeightAt n)
  funext s
  by_cases hs : s.store = σ <;> simp [B, hs, CQState.expectation_zero]

/-- The sum over depths of the norms of the output at a given store is finite. -/
theorem summable_norm_terminalOpAt (σ : Store) : Summable fun n => ‖c.terminalOpAt n σ‖ := by
  have hm : Summable fun n => (c.terminalMassAt n : ℝ) := by
    simpa only [ENNReal.coe_toReal] using
      (ENNReal.summable_toReal (f := fun n => (c.terminalMassAt n : ℝ≥0∞))
        (c.terminatingMass_le.trans_lt ENNReal.coe_lt_top).ne)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hm
  intro n
  apply (Operator.norm_le_re_trace_of_isPositive (c.isPositive_terminalOpAt n σ)).trans
  apply (ENNReal.ofReal_le_ofReal_iff (c.terminalMassAt n).coe_nonneg).mp
  rw [ENNReal.ofReal_coe_nnreal, ← c.terminalWeightAt_mass]
  have h := c.ofReal_trace_mul_terminalOpAt n σ LinearMap.isPositive_one
  rw [one_mul] at h
  rw [h]
  apply c.terminalWeightAt_mono
  intro s
  split <;> simp [CQState.expectation_one]

/-- The unnormalized output at a classical store, summed over all terminating depths. -/
noncomputable def terminalOp (σ : Store) : Operator H := ∑' n, c.terminalOpAt n σ

/-- Summing the endpoints of the terminating histories counts each path to the store once. -/
theorem terminalOp_eq_tsum_terminalHistories (σ : Store) :
    c.terminalOp σ = ∑' n, (((c.terminalHistories n).filter
      (fun h => decide (h.1.state.store = σ))).map (fun h => h.1.state.op)).sum := by
  apply tsum_congr
  intro n
  have h := congrArg (fun l : List (Configuration Store Cell H) =>
    ((l.filter (fun d => decide (d.state.store = σ))).map (·.state.op)).sum)
    (c.terminalHistories_map_fst n)
  simpa only [terminalOpAt, List.filter_map, List.map_map, Function.comp_def, List.filter_filter,
    Bool.and_comm] using h.symm

/-- The exact-depth outputs sum unconditionally to the output operator. -/
theorem hasSum_terminalOpAt (σ : Store) : HasSum (fun n => c.terminalOpAt n σ) (c.terminalOp σ) :=
  (c.summable_norm_terminalOpAt σ).of_norm.hasSum

/-- A terminal configuration contributes its input operator exactly at its own store. -/
theorem terminalOp_terminal (s : CQState Store H) (τ : Store) :
    (Configuration.mk (Cell := Cell) none s).terminalOp τ = if s.store = τ then s.op else 0 := by
  rw [terminalOp, tsum_eq_single 0]
  · by_cases h : s.store = τ <;> simp [terminalOpAt, frontier, h]
  · rintro (_ | n) hn
    · exact (hn rfl).elim
    · simp [terminalOpAt, frontier_succ_terminal]

/-- A running configuration with a single successor has the same output as that successor. -/
theorem terminalOp_singleton {p : Command Store Cell H} {s : CQState Store H}
    {d : Configuration Store Cell H} (h : (Configuration.mk (some p) s).next = [d]) (τ : Store) :
    (Configuration.mk (some p) s).terminalOp τ = d.terminalOp τ := by
  let c := Configuration.mk (some p) s
  rw [terminalOp, (c.hasSum_terminalOpAt τ).summable.tsum_eq_zero_add]
  have hz : c.terminalOpAt 0 τ = 0 := by simp [c, terminalOpAt, frontier]
  rw [hz, zero_add]
  exact tsum_congr fun n => by simp [terminalOpAt, frontier_succ, c, h]

/-- Increasing finite horizons recover the output in operator norm. -/
theorem tendsto_terminalOpUpTo (σ : Store) :
    Tendsto (fun N => c.terminalOpUpTo N σ) atTop (𝓝 (c.terminalOp σ)) :=
  (c.hasSum_terminalOpAt σ).tendsto_sum_nat

/-- The all-depth output is positive at every final store. -/
theorem isPositive_terminalOp (σ : Store) : (c.terminalOp σ).IsPositive :=
  LinearMap.nonneg_iff_isPositive.mp (tsum_nonneg fun n =>
    LinearMap.nonneg_iff_isPositive.mpr (c.isPositive_terminalOpAt n σ))

/-- The unnormalized output at a given store, bundled as input for a subsequent command. -/
noncomputable def terminalState (σ : Store) : CQState Store H :=
  ⟨σ, c.terminalOp σ, c.isPositive_terminalOp σ⟩

/-- The output at a given store represents the expectation from all histories ending there. -/
theorem ofReal_trace_mul_terminalOp (σ : Store) {A : Operator H} (hA : A.IsPositive) :
    ENNReal.ofReal (A * c.terminalOp σ).trace.re = ∑' n, c.terminalWeightAt n
      (fun s => if s.store = σ then ENNReal.ofReal (s.expectation A) else 0) := by
  let φ := LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ H.state) ∘ₗ LinearMap.mulLeft ℂ A)
  have h : HasSum (fun n => (A * c.terminalOpAt n σ).trace.re) (A * c.terminalOp σ).trace.re :=
    Complex.reCLM.hasSum (φ.hasSum (c.hasSum_terminalOpAt σ))
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg _ h.summable]
  · exact tsum_congr fun n => c.ofReal_trace_mul_terminalOpAt n σ hA
  · exact fun n => (Complex.nonneg_iff.mp (hA.trace_mul_nonneg (c.isPositive_terminalOpAt n σ))).1

/-- Pairing the output at each store with its positive post-observable gives the history-based
post-expectation. The classical store type may be infinite. -/
theorem PostH_eq_tsum_trace_mul_terminalOp {A : Store → Operator H} (hA : ∀ σ, (A σ).IsPositive) :
    c.PostH A = ∑' σ, ENNReal.ofReal (A σ * c.terminalOp σ).trace.re := by
  simp_rw [c.ofReal_trace_mul_terminalOp _ (hA _)]
  rw [tsum_comm, c.PostH_eq_tsum_terminalWeightAt hA]
  apply tsum_congr
  intro n
  rw [← c.terminalWeightAt_tsum]
  apply congrArg (c.terminalWeightAt n)
  funext s
  rw [tsum_ite_eq']

/-- The sum of the output traces over all final stores is exactly the terminating mass. -/
theorem terminatingMass_eq_tsum_trace_terminalOp :
    c.terminatingMass = ∑' σ, ENNReal.ofReal (c.terminalOp σ).trace.re := by
  simpa only [PostH_one, one_mul] using
    c.PostH_eq_tsum_trace_mul_terminalOp (A := fun _ => 1) (fun _ => LinearMap.isPositive_one)

/-- An assertion supported at a single store tests precisely the output at that store. -/
theorem PostH_mask_singleton (B : Assertion Store H) (σ : Store) :
    c.PostH (fun τ => B.mask (· = σ) τ) = ENNReal.ofReal ((B σ : Operator H) *
      c.terminalOp σ).trace.re := by
  rw [c.PostH_eq_tsum_trace_mul_terminalOp (B.mask (· = σ)).isPositive, tsum_eq_single σ]
  · rw [B.mask_of_pos (φ := (· = σ)) rfl]
  · intro τ hτ
    simp [B.mask_of_neg (φ := (· = σ)) hτ, Operator.trace]

end QuantumProgram.Configuration
