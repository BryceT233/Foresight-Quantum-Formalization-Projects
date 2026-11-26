/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.WhileTerminalOutput
public import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The least fixed point of loop output unfolding

Output kernels are ordered pointwise in the Löwner order. Their total trace bound guarantees
summability when the loop body hands its outputs to a candidate continuation. Iterating the
guard step from zero gives the finite guard unrollings.
-/

@[expose] public section

open Qudit
open scoped ENNReal ComplexOrder

namespace QuantumProgram

/-- A positive output at each final store, with total output trace bounded by the input mass. -/
abbrev OutputKernel (Store : Type*) (H : Qudit) :=
  {F : CQState Store H → Store → Operator H // ∀ s, (∀ τ, 0 ≤ F s τ) ∧
    (∑' τ, ENNReal.ofReal (F s τ).trace.re) ≤ s.mass}

variable {Store Cell : Type*} {H : Qudit}

instance : OrderBot (OutputKernel Store H) where
  bot := ⟨0, fun s => by simp [Operator.trace]⟩
  bot_le F s := (F.property s).1

variable [DecidableEq Store]

/-- The terminal output of a command as a kernel on all inputs. -/
noncomputable def Command.outputKernel (p : Command Store Cell H) : OutputKernel Store H :=
  ⟨fun s => (Configuration.mk (some p) s).terminalOp, fun s =>
    let c := Configuration.mk (some p) s
    ⟨fun τ => LinearMap.nonneg_iff_isPositive.mpr (c.isPositive_terminalOp τ),
      c.terminatingMass_eq_tsum_trace_terminalOp ▸ c.terminatingMass_le⟩⟩

namespace OutputKernel

variable (F : OutputKernel Store H) (c : Configuration Store Cell H)

private theorem sum_trace_le :
    (∑' σ, ∑' τ, ENNReal.ofReal (F.val (c.terminalState σ) τ).trace.re) ≤ c.state.mass := by
  calc
    _ ≤ ∑' σ, (↑(c.terminalState σ).mass : ℝ≥0∞) := tsum_le_tsum fun σ => (F.property _).2
    _ = c.terminatingMass := by
      rw [c.terminatingMass_eq_tsum_trace_terminalOp]
      exact tsum_congr fun σ => ENNReal.ofReal_coe_nnreal.symm
    _ ≤ _ := c.terminatingMass_le

/-- At a fixed final store, the continuation outputs on all intermediate stores are summable. -/
theorem summable_terminalState (τ : Store) : Summable fun σ => F.val (c.terminalState σ) τ := by
  let w (σ : Store) := (F.val (c.terminalState σ) τ).trace.re
  have hp σ := LinearMap.nonneg_iff_isPositive.mp ((F.property (c.terminalState σ)).1 τ)
  have hw (σ) : 0 ≤ w σ := (Complex.nonneg_iff.mp (hp σ).trace_nonneg).1
  have h : (∑' σ, ENNReal.ofReal (w σ)) ≤ c.state.mass :=
    (tsum_le_tsum fun σ => le_tsum (fun t =>
      ENNReal.ofReal (F.val (c.terminalState σ) t).trace.re) τ).trans (F.sum_trace_le c)
  have hs : Summable w := by
    simpa only [ENNReal.toReal_ofReal (hw _)] using
      ENNReal.summable_toReal (h.trans_lt ENNReal.coe_lt_top).ne
  exact hs.of_norm_bounded fun σ => Operator.norm_le_re_trace_of_isPositive (hp σ)

private theorem trace_tsum_terminalState (τ : Store) :
    ENNReal.ofReal (∑' σ, F.val (c.terminalState σ) τ).trace.re =
      ∑' σ, ENNReal.ofReal (F.val (c.terminalState σ) τ).trace.re := by
  let f (σ : Store) := F.val (c.terminalState σ) τ
  have h : HasSum (fun σ => (f σ).trace.re) (∑' σ, f σ).trace.re :=
    Complex.reCLM.hasSum ((LinearMap.toContinuousLinearMap (LinearMap.trace ℂ H.state)).hasSum
      (F.summable_terminalState c τ).hasSum)
  change ENNReal.ofReal (∑' σ, f σ).trace.re = ∑' σ, ENNReal.ofReal (f σ).trace.re
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg _ h.summable]
  exact fun σ => (Complex.nonneg_iff.mp
    (LinearMap.nonneg_iff_isPositive.mp ((F.property (c.terminalState σ)).1 τ)).trace_nonneg).1

end OutputKernel

variable (b : Store → Bool) (p : Command Store Cell H)

/-- One guard test, running the body and then the given continuation when the guard holds. -/
noncomputable def whileOpStep : OutputKernel Store H →o OutputKernel Store H where
  toFun F := ⟨fun s τ => if b s.store then
      ∑' σ, F.val ((Configuration.mk (some p) s).terminalState σ) τ
    else if s.store = τ then s.op else 0, by
      intro s
      let c := Configuration.mk (some p) s
      dsimp only
      cases hb : b s.store with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        refine ⟨fun τ => ?_, ?_⟩
        · split <;> simp [LinearMap.nonneg_iff_isPositive.mpr s.positive]
        · rw [tsum_eq_single s.store]
          · simp only [ite_true]
            exact (ENNReal.ofReal_coe_nnreal (p := s.mass)).le
          · intro τ hτ
            simp [Ne.symm hτ, Operator.trace]
      | true =>
        refine ⟨fun τ => tsum_nonneg fun σ => (F.property _).1 τ, ?_⟩
        change (∑' τ, ENNReal.ofReal (∑' σ, F.val (c.terminalState σ) τ).trace.re) ≤ _
        simp_rw [F.trace_tsum_terminalState c]
        rw [tsum_comm]
        exact F.sum_trace_le c⟩
  monotone' := by
    intro F G h s τ
    dsimp only
    cases hb : b s.store with
    | false => exact le_rfl
    | true =>
      exact (F.summable_terminalState _ τ).tsum_le_tsum (fun σ => h _ τ)
        (G.summable_terminalState _ τ)

/-- Evaluating one unfolding either sums the continuation or returns the initial state. -/
theorem whileOpStep_apply (F : OutputKernel Store H) (s : CQState Store H) (τ : Store) :
    (whileOpStep b p F).val s τ = if b s.store then
      ∑' σ, F.val ((Configuration.mk (some p) s).terminalState σ) τ
    else if s.store = τ then s.op else 0 := rfl

/-- Starting the unfolding operator at zero counts exactly the allowed outer guard tests. -/
theorem iterate_whileOpStep_bot (n : ℕ) :
    ((whileOpStep b p)^[n] ⊥).val = whileOpApprox b p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    funext s τ
    rw [whileOpStep_apply, ih, whileOpApprox]

/-- Increasing the guard budget increases the output in the pointwise Löwner order. -/
theorem monotone_whileOpApprox : Monotone (whileOpApprox b p) := by
  intro m n h
  rw [← iterate_whileOpStep_bot, ← iterate_whileOpStep_bot]
  exact (whileOpStep b p).monotone.monotone_iterate_of_le_map (bot_le : ⊥ ≤ whileOpStep b p ⊥) h

/-- At each input and final store the loop output is the least upper bound of the finite outputs. -/
theorem isLUB_whileOpApprox_apply (s : CQState Store H) (τ : Store) :
    IsLUB (Set.range fun n => whileOpApprox b p n s τ)
      ((Configuration.mk (some (.whileDo b p)) s).terminalOp τ) :=
  isLUB_of_tendsto_atTop (fun _ _ h => monotone_whileOpApprox b p h s τ)
    (tendsto_whileOpApprox b p s τ)

/-- In the pointwise order on output families, the unrollings have the loop kernel as their
least upper bound. -/
theorem isLUB_whileOpApprox :
    IsLUB (Set.range (whileOpApprox b p)) (Command.whileDo b p).outputKernel.val :=
  isLUB_of_tendsto_atTop (monotone_whileOpApprox b p) <| tendsto_pi_nhds.mpr fun s =>
    tendsto_pi_nhds.mpr fun τ => tendsto_whileOpApprox b p s τ

/-- The terminal-output kernel of a loop is fixed by one guard unfolding. -/
theorem isFixedPt_whileOpStep :
    Function.IsFixedPt (whileOpStep b p) (Command.whileDo b p).outputKernel :=
  Subtype.ext (funext fun s => funext fun τ => (Configuration.terminalOp_whileDo b p s τ).symm)

/-- Any output kernel closed under one unfolding bounds the operational loop output. -/
theorem outputKernel_whileDo_le {F : OutputKernel Store H} (hF : whileOpStep b p F ≤ F) :
    (Command.whileDo b p).outputKernel ≤ F := by
  apply (isLUB_whileOpApprox b p).2
  rintro _ ⟨n, rfl⟩
  rw [← iterate_whileOpStep_bot]
  change (whileOpStep b p)^[n] ⊥ ≤ F
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ((whileOpStep b p).monotone ih).trans hF

/-- The operational loop output is the least fixed point of the monotone guard step. -/
theorem isLeast_fixedPoints_whileOpStep :
    IsLeast (Function.fixedPoints (whileOpStep b p)) (Command.whileDo b p).outputKernel :=
  ⟨isFixedPt_whileOpStep b p, fun _ h => outputKernel_whileDo_le b p h.le⟩

end QuantumProgram
