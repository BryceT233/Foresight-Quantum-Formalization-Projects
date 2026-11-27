/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.Output.Terminal
import FQFP.QuantumProgram.Semantics.Precondition.Weakest
import FQFP.CQM.Qudit.Channel.Process.Tomography

/-!
# Sequential composition of terminal output operators

Each intermediate classical store supplies one unnormalized input for the continuation.
Testing a final output with an effect at a single store reduces composition to the
weakest-precondition identity. The identity effect controls convergence, and pure-state
expectations determine the resulting operator.
-/

@[expose] public section

open Qudit
open scoped ENNReal ComplexOrder

namespace QuantumProgram.Configuration

variable {Store Cell : Type*} {H : Qudit} [DecidableEq Store]
variable (c : Configuration Store Cell H) (q : Command Store Cell H)

/-- Run the continuation on the aggregated input from each store and sum its post-expectations. -/
theorem PostH_seqWith_eq_tsum_terminalState (B : Assertion Store H) :
    (c.seqWith q).PostH (fun τ => B τ) =
      ∑' σ, (Configuration.mk (some q) (c.terminalState σ)).PostH (fun τ => B τ) := by
  calc
    (c.seqWith q).PostH (fun τ => B τ) = c.PostH (fun σ => wp q B σ) :=
      c.PostH_seqWith_wp q B
    _ = _ := by
      rw [c.PostH_eq_tsum_trace_mul_terminalOp (wp q B).isPositive]
      exact tsum_congr fun σ => expectation_wp q B (c.terminalState σ)

private theorem hasSum_re_trace_mul_terminalOp_seqWith (τ : Store)
    (E : Set.Icc (0 : Operator H) 1) :
    HasSum (fun σ => ((E : Operator H) *
      (Configuration.mk (some q) (c.terminalState σ)).terminalOp τ).trace.re)
      ((E : Operator H) * (c.seqWith q).terminalOp τ).trace.re := by
  let B : Assertion Store H := fun _ => E
  let w (d : Configuration Store Cell H) := ((E : Operator H) * d.terminalOp τ).trace.re
  have hw (d) : 0 ≤ w d :=
    (Complex.nonneg_iff.mp ((B.isPositive τ).trace_mul_nonneg (d.isPositive_terminalOp τ))).1
  have he : ENNReal.ofReal (w (c.seqWith q)) =
      ∑' σ, ENNReal.ofReal (w ⟨some q, c.terminalState σ⟩) := by
    simpa only [PostH_mask_singleton] using c.PostH_seqWith_eq_tsum_terminalState q (B.mask (· = τ))
  have hs := ENNReal.hasSum_toReal (he.symm ▸ ENNReal.ofReal_ne_top)
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ← he] at hs
  simpa only [ENNReal.toReal_ofReal (hw _)] using hs

/-- Summing the continuation outputs over all intermediate stores gives the sequential output
at the chosen final store, with unconditional convergence in operator norm. -/
theorem hasSum_terminalOp_seqWith (τ : Store) :
    HasSum (fun σ => (Configuration.mk (some q) (c.terminalState σ)).terminalOp τ)
      ((c.seqWith q).terminalOp τ) := by
  let f (σ : Store) := (Configuration.mk (some q) (c.terminalState σ)).terminalOp τ
  have hf (σ : Store) : (f σ).IsPositive := isPositive_terminalOp _ _
  have hmass : Summable fun σ => (f σ).trace.re := by
    simpa only [Assertion.identity, one_mul] using
      (c.hasSum_re_trace_mul_terminalOp_seqWith q τ (Assertion.identity (H := H) τ)).summable
  have hs : Summable f := hmass.of_norm_bounded fun σ =>
    Operator.norm_le_re_trace_of_isPositive (hf σ)
  suffices (c.seqWith q).terminalOp τ = ∑' σ, f σ by exact this ▸ hs.hasSum
  apply Operator.ext_expectationComplex_pure
  intro v
  let E := (Density.pure v).op
  let φ := LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ H.state) ∘ₗ LinearMap.mulRight ℂ E)
  have hcast (d : Configuration Store Cell H) :
      (((E * d.terminalOp τ).trace.re : ℝ) : ℂ) = (d.terminalOp τ * E).trace := by
    rw [show (d.terminalOp τ * E).trace = (E * d.terminalOp τ).trace from
      LinearMap.trace_mul_comm ℂ _ _]
    exact Complex.ext rfl (Complex.nonneg_iff.mp
      ((Density.pure v).positive.trace_mul_nonneg (d.isPositive_terminalOp τ))).2
  have he : HasSum (fun σ => (f σ * E).trace) ((c.seqWith q).terminalOp τ * E).trace := by
    have hr := c.hasSum_re_trace_mul_terminalOp_seqWith q τ ((Assertion.pure v) τ)
    change HasSum (fun σ => (E * f σ).trace.re) (E * (c.seqWith q).terminalOp τ).trace.re at hr
    simpa only [f, hcast] using Complex.hasSum_ofReal.mpr hr
  exact he.unique (φ.hasSum hs.hasSum)

/-- The output of `p.seq q` is the sum of the outputs of `q` on the store-indexed outputs of `p`. -/
theorem terminalOp_seq (p q : Command Store Cell H) (s : CQState Store H) (τ : Store) :
    (Configuration.mk (some (p.seq q)) s).terminalOp τ =
      ∑' σ, (Configuration.mk (some q)
        ((Configuration.mk (some p) s).terminalState σ)).terminalOp τ :=
  ((Configuration.mk (some p) s).hasSum_terminalOp_seqWith q τ).tsum_eq.symm

end QuantumProgram.Configuration
