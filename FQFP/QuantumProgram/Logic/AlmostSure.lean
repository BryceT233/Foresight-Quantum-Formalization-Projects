/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors, Foresight Quantum
-/

/-
Qhl source for the contracting-loop rule for total correctness.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/AlmostSure.lean

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Logic.ExactExpectation
public import FQFP.QuantumProgram.Logic.Soundness
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Total correctness of a uniformly contracting loop

Following `Qhl/Logic/AlmostSure.lean`, the contraction controls the expectation of the
guarded invariant on the body's terminal histories. After `n` iterations the resulting
error bound is geometric, so taking its limit gives the total-correctness rule.
-/

@[expose] public section

open Filter Qudit
open scoped NNReal ENNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- A body returns at most a fixed fraction of the input invariant expectation to the guard. -/
def LoopBodyContraction (b : Store → Bool) (p : Command Store Cell H) (J : Assertion Store H)
    (a : ℝ≥0) : Prop := ∀ s : CQState Store H, b s.store = true →
  (Configuration.mk (some p) s).PostH (fun σ => J.mand b σ) ≤
    (a : ℝ≥0∞) * ENNReal.ofReal (s.expectation (J s.store))

/-- A lower bound on the complementary post-expectation bounds the mass returning to the guard. -/
theorem LoopBodyContraction.of_complement {b : Store → Bool} {p : Command Store Cell H}
    {J A : Assertion Store H} {a : ℝ≥0} (h : validTot A p (J.mand b).compl)
    (hA : ∀ s : CQState Store H, b s.store = true →
      (s.mass : ℝ≥0∞) - a * ENNReal.ofReal (s.expectation (J s.store)) ≤
        ENNReal.ofReal (s.expectation (A s.store))) : LoopBodyContraction b p J a := by
  intro s hb
  let c := Configuration.mk (some p) s
  let bound := (a : ℝ≥0∞) * ENNReal.ofReal (s.expectation (J s.store))
  have hfin : (s.mass : ℝ≥0∞) - bound ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top tsub_le_self
  apply ENNReal.le_of_add_le_add_right hfin
  calc c.PostH _ + ((s.mass : ℝ≥0∞) - bound)
      ≤ c.PostH _ + c.PostH (fun σ => (J.mand b).compl σ) :=
        add_le_add le_rfl ((hA s hb).trans (h s))
    _ = c.terminatingMass := c.PostH_add_PostH_compl (J.mand b)
    _ ≤ s.mass := c.terminatingMass_le
    _ ≤ bound + ((s.mass : ℝ≥0∞) - bound) := by rw [add_comm]; exact le_tsub_add

/-- A totally valid invariant and a uniform contraction factor below one give a totally valid
loop triple, including when the number of iterations has no deterministic bound. -/
theorem validTot_while_of_contraction {b : Store → Bool} {p : Command Store Cell H}
    {J : Assertion Store H} {a : ℝ≥0} (ha : a < 1) (hbody : validTot (J.mand b) p J)
    (hcontract : LoopBodyContraction b p J a) : validTot J (.whileDo b p) (J.mandNot b) := by
  let retry (s : CQState Store H) := ENNReal.ofReal (s.expectation (J.mand b s.store))
  let exitWeight (s : CQState Store H) :=
    (Configuration.mk (some (.whileDo b p)) s).PostH (fun σ => J.mandNot b σ)
  have exitBound (s : CQState Store H) (hb : b s.store = false) :
      ENNReal.ofReal (s.expectation (J s.store)) ≤ exitWeight s := by
    have hf : (Configuration.mk (some (.whileDo b p)) s).frontier 1 = [⟨none, s⟩] := by
      simpa [Configuration.frontier] using next_whileDo_of_false p hb
    simpa only [exitWeight, J.mandNot_of_false hb] using
      Configuration.ofReal_expectation_le_PostH_of_frontier hf (fun σ => J.mandNot b σ)
  have stage (n : ℕ) (s : CQState Store H) :
      ENNReal.ofReal (s.expectation (J s.store)) ≤ exitWeight s + (a : ℝ≥0∞) ^ n * retry s := by
    induction n generalizing s with
    | zero =>
      cases hb : b s.store with
      | false => exact (exitBound s hb).trans le_self_add
      | true => simp [retry, J.mand_of_true hb]
    | succ n ih =>
      cases hb : b s.store with
      | false => exact (exitBound s hb).trans le_self_add
      | true =>
        let c := Configuration.mk (some p) s
        have step : exitWeight s = ∑' j, c.terminalWeightAt j exitWeight := by
          change (Configuration.mk (some (.whileDo b p)) s).PostH _ = _
          rw [Configuration.PostH_singleton (next_whileDo_of_true p hb),
            Configuration.PostH_seqWith _ _ (J.mandNot b).isPositive]
        have body := hbody s
        rw [J.mand_of_true hb, Configuration.PostH_eq_tsum_terminalWeightAt _ J.isPositive] at body
        apply body.trans
        calc (∑' j, c.terminalWeightAt j (fun t => ENNReal.ofReal (t.expectation (J t.store))))
            ≤ ∑' j, c.terminalWeightAt j (fun t => exitWeight t + (a : ℝ≥0∞) ^ n * retry t) :=
              tsum_le_tsum fun j => c.terminalWeightAt_mono j ih
          _ = exitWeight s + (a : ℝ≥0∞) ^ n * c.PostH (fun σ => J.mand b σ) := by
              simp only [Configuration.terminalWeightAt_add,
                Configuration.terminalWeightAt_const_mul, tsum_add, ENNReal.tsum_mul_left,
                ← step]
              rw [c.PostH_eq_tsum_terminalWeightAt (J.mand b).isPositive]
          _ ≤ exitWeight s + (a : ℝ≥0∞) ^ n *
              ((a : ℝ≥0∞) * ENNReal.ofReal (s.expectation (J s.store))) :=
            add_le_add le_rfl (mul_le_mul' le_rfl (hcontract s hb))
          _ = exitWeight s + (a : ℝ≥0∞) ^ (n + 1) * retry s := by
              simp only [pow_succ, mul_assoc, retry, J.mand_of_true hb]
  intro s
  have ha' : (a : ℝ≥0∞) < 1 := by exact_mod_cast ha
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ha'
  have hzero : Tendsto (fun n : ℕ => (a : ℝ≥0∞) ^ n * retry s) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hpow (b := retry s) (Or.inr ENNReal.ofReal_ne_top)
  exact ge_of_tendsto' (by simpa using hzero.const_add (exitWeight s)) (fun n => stage n s)

/-- A total derivation for the body supplies the invariant premise of the contraction rule. -/
theorem DerivTot.validTot_while_of_contraction {b : Store → Bool} {p : Command Store Cell H}
    {J : Assertion Store H} {a : ℝ≥0} (h : DerivTot (J.mand b) p J) (ha : a < 1)
    (hc : LoopBodyContraction b p J a) : validTot J (.whileDo b p) (J.mandNot b) :=
  QuantumProgram.validTot_while_of_contraction ha h.sound hc

end QuantumProgram
