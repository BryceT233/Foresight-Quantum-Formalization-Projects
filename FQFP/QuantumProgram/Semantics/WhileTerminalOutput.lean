/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.TerminalOutputSeq
public import FQFP.QuantumProgram.Semantics.WhileWeakestPrecondition
import FQFP.QuantumProgram.Logic.Iteration.While
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Terminal output of a guarded loop

A true guard runs the whole body and hands its output at each intermediate store back to
the loop. Finite unrollings count outer guard tests, including the final false test.
At each final store the remaining output is positive, so its trace bounds the norm error.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal ComplexOrder Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} [DecidableEq Store]
variable (b : Store → Bool) (p : Command Store Cell H)

/-- Unfold the loop once at its input store, summing the residual loop over the body's outputs. -/
theorem Configuration.terminalOp_whileDo (s : CQState Store H) (τ : Store) :
    (Configuration.mk (some (.whileDo b p)) s).terminalOp τ = if b s.store then
      ∑' σ, (Configuration.mk (some (.whileDo b p))
        ((Configuration.mk (some p) s).terminalState σ)).terminalOp τ
    else if s.store = τ then s.op else 0 := by
  cases hb : b s.store with
  | false =>
    exact (terminalOp_singleton (next_whileDo_of_false p hb) τ).trans (terminalOp_terminal s τ)
  | true =>
    exact (terminalOp_singleton (next_whileDo_of_true p hb) τ).trans
      (terminalOp_seq p (.whileDo b p) s τ)

/-- Output at `τ` from executions allowed at most `n` outer guard tests. -/
noncomputable def whileOpApprox : ℕ → CQState Store H → Store → Operator H
  | 0, _, _ => 0
  | n + 1, s, τ => if b s.store then
      ∑' σ, whileOpApprox n ((Configuration.mk (some p) s).terminalState σ) τ
    else if s.store = τ then s.op else 0

private theorem summable_of_mem_Icc {ι : Type*} {f g : ι → Operator H} (hg : Summable g)
    (h : ∀ i, f i ∈ Set.Icc 0 (g i)) : Summable f := by
  have : FiniteDimensional ℝ (Operator H) := FiniteDimensional.trans ℝ ℂ _
  exact hg.norm.of_norm_bounded fun i => CStarAlgebra.norm_le_norm_of_le_of_nonneg (h i).2 (h i).1

/-- Every guard-bounded output is positive and lies below the full output in Löwner order. -/
theorem whileOpApprox_mem_Icc (n : ℕ) (s : CQState Store H) (τ : Store) :
    whileOpApprox b p n s τ ∈
      Set.Icc 0 ((Configuration.mk (some (.whileDo b p)) s).terminalOp τ) := by
  induction n generalizing s with
  | zero =>
    exact ⟨le_rfl, LinearMap.nonneg_iff_isPositive.mpr (Configuration.isPositive_terminalOp _ _)⟩
  | succ n ih =>
    rw [whileOpApprox, Configuration.terminalOp_whileDo]
    cases hb : b s.store with
    | false =>
      by_cases he : s.store = τ <;> simp [he, LinearMap.nonneg_iff_isPositive.mpr s.positive]
    | true =>
      let c := Configuration.mk (some p) s
      have h := fun σ => ih (c.terminalState σ)
      have hs := (c.hasSum_terminalOp_seqWith (.whileDo b p) τ).summable
      exact ⟨tsum_nonneg fun σ => (h σ).1,
        (summable_of_mem_Icc hs h).tsum_le_tsum (fun σ => (h σ).2) hs⟩

/-- The mass of the finite output at a store agrees with the guard-bounded weakest
precondition testing for termination at that store. -/
theorem ofReal_trace_whileOpApprox (n : ℕ) (s : CQState Store H) (τ : Store) :
    ENNReal.ofReal (whileOpApprox b p n s τ).trace.re = ENNReal.ofReal
      (s.expectation (whileWpApprox b p (Assertion.identity.mask (· = τ)) n s.store)) := by
  let B : Assertion Store H := Assertion.identity.mask (· = τ)
  induction n generalizing s with
  | zero => simp [whileOpApprox, whileWpApprox, Assertion.zero, CQState.expectation_zero,
      Operator.trace]
  | succ n ih =>
    cases hb : b s.store with
    | false =>
      simp only [whileOpApprox, whileWpApprox, whileWpStep, OrderHom.coe_mk, hb, Bool.false_eq_true,
        ite_false]
      by_cases he : s.store = τ <;>
        simp [he, Assertion.mask, Assertion.identity, CQState.expectation, Operator.trace]
    | true =>
      let c := Configuration.mk (some p) s
      let f (σ : Store) := whileOpApprox b p n (c.terminalState σ) τ
      have hf (σ) := whileOpApprox_mem_Icc b p n (c.terminalState σ) τ
      have hs : Summable f := summable_of_mem_Icc
        (c.hasSum_terminalOp_seqWith (.whileDo b p) τ).summable hf
      have ht : HasSum (fun σ => (f σ).trace.re) (∑' σ, f σ).trace.re :=
        Complex.reCLM.hasSum ((LinearMap.toContinuousLinearMap (LinearMap.trace ℂ H.state)).hasSum
          hs.hasSum)
      simp only [whileOpApprox, whileWpApprox, whileWpStep, OrderHom.coe_mk, hb, ite_true]
      change ENNReal.ofReal (∑' σ, f σ).trace.re = ENNReal.ofReal
        (s.expectation (wp p (whileWpApprox b p B n) s.store))
      rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg _ ht.summable, expectation_wp,
        c.PostH_eq_tsum_trace_mul_terminalOp (whileWpApprox b p B n).isPositive]
      · exact tsum_congr fun σ => ih (c.terminalState σ)
      · exact fun σ => (Complex.nonneg_iff.mp
          (LinearMap.nonneg_iff_isPositive.mp (hf σ).1).trace_nonneg).1

/-- At a fixed final store the uncollected trace bounds the error in operator norm. -/
theorem norm_whileOpApprox_sub_terminalOp_le (n : ℕ) (s : CQState Store H) (τ : Store) :
    let A := (Configuration.mk (some (.whileDo b p)) s).terminalOp τ
    ‖whileOpApprox b p n s τ - A‖ ≤ A.trace.re - (whileOpApprox b p n s τ).trace.re := by
  dsimp only
  rw [norm_sub_rev]
  simpa only [Operator.trace, map_sub, Complex.sub_re] using Operator.norm_le_re_trace_of_isPositive
    (LinearMap.le_def.mp (whileOpApprox_mem_Icc b p n s τ).2)

/-- At every final store the finite guard unrollings converge in operator norm to the
terminal output of the loop. -/
theorem tendsto_whileOpApprox (s : CQState Store H) (τ : Store) :
    Tendsto (fun n => whileOpApprox b p n s τ) atTop
      (𝓝 ((Configuration.mk (some (.whileDo b p)) s).terminalOp τ)) := by
  let c := Configuration.mk (some (.whileDo b p)) s
  let f := fun n => whileOpApprox b p n s τ
  have h : Tendsto (fun n => ENNReal.ofReal (f n).trace.re) atTop
      (𝓝 (ENNReal.ofReal (c.terminalOp τ).trace.re)) := by
    simpa only [f, c, ofReal_trace_whileOpApprox, Configuration.PostH_mask_singleton,
      Assertion.identity, one_mul] using
      tendsto_expectation_whileWpApprox b p (Assertion.identity.mask (· = τ)) s
  have hf (n) := whileOpApprox_mem_Icc b p n s τ
  have ht : Tendsto (fun n => (f n).trace.re) atTop (𝓝 (c.terminalOp τ).trace.re) := by
    have hn (n) : 0 ≤ (f n).trace.re := (Complex.nonneg_iff.mp
      (LinearMap.nonneg_iff_isPositive.mp (hf n).1).trace_nonneg).1
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hn _), ENNReal.toReal_ofReal
      (Complex.nonneg_iff.mp (c.isPositive_terminalOp τ).trace_nonneg).1] using
      (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_whileOpApprox_sub_terminalOp_le b p n s τ)
  simpa only [sub_self] using (tendsto_const_nhds (x := (c.terminalOp τ).trace.re)).sub ht

end QuantumProgram
