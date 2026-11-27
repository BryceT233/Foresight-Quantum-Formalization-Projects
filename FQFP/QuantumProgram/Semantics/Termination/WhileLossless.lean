/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/WP.lean: whileActiveWP.
QuantumComputation/QuantumHoareLogic/ResourceCounting/Loops.lean: activeIter, expectedIterations,
expect_whileActiveWP, antitone_trace_activeIter, expectedIterations_eq_sum,
trace_eq_whileRec_add_activeIter, trace_qWhile_of_tendsto_zero,
trace_qWhile_of_expectedIterations_ne_top and Lossless.qWhile.
Here the active trace is summed over terminal histories of each body invocation.

Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/AlmostSure.lean: validTot_while_ast, specialized to the identity invariant.
Copyright 2026 Qedia contributors.

Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Termination.Lossless
public import FQFP.QuantumProgram.Logic.Iteration.AlmostSure
public import FQFP.QuantumProgram.Semantics.Execution.While

/-!
# Losslessness of unbounded loops

`whileActiveMass b p n s` is the trace entering the body for the `(n + 1)`st time.
If the body returns the full trace on guarded inputs, this mass and the trace collected
in at most `n + 1` guard tests partition the input. The limiting active mass then measures
nontermination. A uniform one-step contraction also gives losslessness directly by the
almost-sure termination rule.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal NNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit} (b : Store → Bool) (p : Command Store Cell H)

/-- Input mass entering the body for the `(n + 1)`st time, after `n` completed iterations. -/
noncomputable def whileActiveMass : ℕ → CQState Store H → ℝ≥0∞ :=
  whileEntryWeight b p fun t => t.mass

/-- The first entry carries all of the input trace if the guard is true. -/
theorem whileActiveMass_zero (s : CQState Store H) :
    whileActiveMass b p 0 s = if b s.store then (s.mass : ℝ≥0∞) else 0 := rfl

/-- A later entry is counted by pulling its mass back through one guarded body execution. -/
theorem whileActiveMass_succ (n : ℕ) (s : CQState Store H) :
    whileActiveMass b p (n + 1) s =
      if b s.store then p.outputWeight (whileActiveMass b p n) s else 0 := rfl

/-- Sum of body-entry masses, equal to the expected iteration count on a unit-trace input. -/
noncomputable def expectedIterations (s : CQState Store H) : ℝ≥0∞ :=
  ∑' n, whileActiveMass b p n s

/-- The effect testing entry into iteration `n + 1`, pulled back to the initial store. -/
noncomputable def whileActivePre : ℕ → Assertion Store H
  | 0 => Assertion.identity.mand b
  | n + 1 => (wp p (whileActivePre n)).mand b

/-- Backward evaluation of the entry effect counts exactly the histories entering that iteration. -/
theorem expectation_whileActivePre (n : ℕ) (s : CQState Store H) :
    ENNReal.ofReal (s.expectation (whileActivePre b p n s.store)) = whileActiveMass b p n s := by
  induction n generalizing s with
  | zero =>
    cases hb : b s.store <;> simp [whileActivePre, whileActiveMass_zero, hb,
      Assertion.mand_of_true, Assertion.mand_of_false, Assertion.identity,
      CQState.expectation_one, CQState.expectation_zero]
  | succ n ih =>
    rw [whileActivePre, whileActiveMass_succ]
    cases hb : b s.store with
    | false => simp [Assertion.mand_of_false _ hb, CQState.expectation_zero]
    | true =>
      rw [Assertion.mand_of_true _ hb, expectation_wp,
        ← p.outputWeight_expectation s (whileActivePre b p n).isPositive]
      simp only [ite_true, ih]

/-- The trace reaching any single iteration is bounded by the input trace. -/
theorem whileActiveMass_le_mass (n : ℕ) (s : CQState Store H) :
    whileActiveMass b p n s ≤ s.mass := by
  rw [← expectation_whileActivePre]
  exact s.ofReal_expectation_le_mass ((whileActivePre b p n s.store).2.2)

/-- Entering a later iteration is a stronger test in the pointwise Löwner order. -/
theorem antitone_whileActivePre : Antitone (whileActivePre b p) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact Assertion.mask_mono (fun σ => (wp p (whileActivePre b p 0) σ).2.2) (fun _ => id)
  | succ n ih => exact Assertion.mask_mono (wp_mono p ih) (fun _ => id)

/-- The mass entering successive iterations decreases, including for bodies that lose trace. -/
theorem antitone_whileActiveMass (s : CQState Store H) :
    Antitone fun n => whileActiveMass b p n s := by
  intro i j hij
  simpa only [expectation_whileActivePre] using
    ENNReal.ofReal_le_ofReal (s.expectation_mono (antitone_whileActivePre b p hij s.store))

/-- If no mass enters iteration `k + 1`, the first `k` entries give the entire expected count. -/
theorem expectedIterations_eq_sum_of_whileActiveMass_eq_zero {s : CQState Store H} {k : ℕ}
    (h : whileActiveMass b p k s = 0) :
    expectedIterations b p s = ∑ i ∈ Finset.range k, whileActiveMass b p i s := by
  apply tsum_eq_sum
  intro n hn
  exact le_zero_iff.mp ((antitone_whileActiveMass b p s (by simpa using hn)).trans_eq h)

/-- Total validity for the guarded identity means full trace return on every guarded input. -/
theorem validTot_mand_identity_iff :
    validTot (Assertion.identity.mand b) p Assertion.identity ↔
      ∀ s : CQState Store H, b s.store = true →
        (Configuration.mk (some p) s).terminatingMass = s.mass := by
  refine ⟨fun h s hb => le_antisymm (Configuration.terminatingMass_le _) ?_, fun h s => ?_⟩
  · simpa only [Assertion.mand_of_true _ hb, Assertion.identity, CQState.expectation_one,
      ENNReal.ofReal_coe_nnreal, Configuration.PostH_one] using h s
  · cases hb : b s.store with
    | false => simp [Assertion.mand_of_false _ hb, CQState.expectation_zero]
    | true =>
      simpa only [Assertion.mand_of_true _ hb, Assertion.identity, CQState.expectation_one,
        ENNReal.ofReal_coe_nnreal, Configuration.PostH_one] using (h s hb).ge

variable {b p}

/-- A uniform contraction of the guarded trace suffices for losslessness when the body
returns all mass on inputs that enter it. -/
theorem lossless_whileDo_of_contraction {a : ℝ≥0} (ha : a < 1)
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (hc : LoopBodyContraction b p Assertion.identity a) : Lossless (.whileDo b p) :=
  (validTot_identity_iff _).mp <| validTot_conseq le_rfl
    (validTot_while_of_contraction ha hbody hc) (fun σ => (Assertion.identity.mandNot b σ).2.2)

/-- At each guard budget the trace already exited and the trace entering the next iteration
account for all input mass, provided each guarded body invocation is lossless. -/
theorem expectation_whileWpApprox_add_whileActiveMass
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (n : ℕ) (s : CQState Store H) :
    ENNReal.ofReal (s.expectation (whileWpApprox b p Assertion.identity (n + 1) s.store).val) +
      whileActiveMass b p n s = s.mass := by
  induction n generalizing s with
  | zero =>
    cases hb : b s.store <;>
      simp [whileWpApprox, whileWpStep, whileActiveMass_zero, hb, Assertion.zero,
        Assertion.identity, CQState.expectation_zero, CQState.expectation_one]
  | succ n ih =>
    cases hb : b s.store with
    | false => simp [whileWpApprox, whileWpStep, whileActiveMass_succ, hb, Assertion.identity,
        CQState.expectation_one]
    | true =>
      let A := whileWpApprox b p Assertion.identity (n + 1)
      rw [whileWpApprox, whileActiveMass_succ]
      simp only [whileWpStep, OrderHom.coe_mk, hb, ite_true]
      rw [expectation_wp, ← p.outputWeight_expectation s A.isPositive, ← p.outputWeight_add,
        funext ih, p.outputWeight_mass]
      exact (validTot_mand_identity_iff b p).mp hbody s hb

/-- The mass entering later iterations converges to the residual mass of the loop. -/
theorem tendsto_whileActiveMass (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (s : CQState Store H) :
    Tendsto (fun n => whileActiveMass b p n s) atTop
      (𝓝 (Configuration.mk (some (.whileDo b p)) s).nonterminatingMass) := by
  have ht := (tendsto_expectation_whileWpApprox b p Assertion.identity s).comp
    (tendsto_add_atTop_nat 1)
  have he (n : ℕ) := ENNReal.sub_eq_of_eq_add_rev ENNReal.ofReal_ne_top
    (expectation_whileWpApprox_add_whileActiveMass hbody n s).symm
  simpa only [Function.comp_def, he, Assertion.identity, Configuration.PostH_one,
    Configuration.nonterminatingMass] using
    ENNReal.Tendsto.sub (tendsto_const_nhds (x := (s.mass : ℝ≥0∞))) ht (Or.inl ENNReal.coe_ne_top)

/-- For a single input, the loop returns its full trace exactly when the active tail vanishes. -/
theorem terminatingMass_whileDo_eq_iff
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity) (s : CQState Store H) :
    (Configuration.mk (some (.whileDo b p)) s).terminatingMass = s.mass ↔
      Tendsto (fun n => whileActiveMass b p n s) atTop (𝓝 0) := by
  have ht := tendsto_whileActiveMass hbody s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [Configuration.nonterminatingMass, h, tsub_self] using ht
  · have hz := tendsto_nhds_unique ht h
    simpa only [hz, add_zero] using
      (Configuration.mk (some (.whileDo b p)) s).terminatingMass_add_nonterminatingMass

/-- A loop is lossless exactly when its body preserves trace on guarded inputs and the
mass entering later iterations tends to zero on every input. -/
theorem lossless_whileDo_iff :
    Lossless (.whileDo b p) ↔ validTot (Assertion.identity.mand b) p Assertion.identity ∧
      ∀ s : CQState Store H, Tendsto (fun n => whileActiveMass b p n s) atTop (𝓝 0) := by
  constructor
  · intro h
    have hw := lossless_iff_wp_identity.mp h
    have hbody : validTot (Assertion.identity.mand b) p Assertion.identity := by
      apply validTot_iff_le_wp.mpr
      intro σ
      cases hb : b σ with
      | false =>
        change ((Assertion.identity (H := H)).mand b σ : Operator H) ≤ _
        rw [Assertion.mand_of_false _ hb]
        exact (wp p Assertion.identity σ).2.1
      | true =>
        have hs := congrFun hw σ
        rw [wp_whileDo, ite_eq_left hb, hw] at hs
        simpa only [Assertion.mand_of_true _ hb] using hs.ge
    exact ⟨hbody, fun s => (terminatingMass_whileDo_eq_iff hbody s).mp (h s)⟩
  · exact fun ⟨hbody, ht⟩ s => (terminatingMass_whileDo_eq_iff hbody s).mpr (ht s)

/-- An input with finite expected entry count returns all its trace when guarded bodies do. -/
theorem terminatingMass_whileDo_eq_of_expectedIterations_ne_top
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity) {s : CQState Store H}
    (h : expectedIterations b p s ≠ ∞) :
    (Configuration.mk (some (.whileDo b p)) s).terminatingMass = s.mass :=
  (terminatingMass_whileDo_eq_iff hbody s).mpr (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h)

/-- Finite expected iteration count on every input suffices for a loop to be lossless. -/
theorem lossless_whileDo_of_expectedIterations_ne_top
    (hbody : validTot (Assertion.identity.mand b) p Assertion.identity)
    (h : ∀ s : CQState Store H, expectedIterations b p s ≠ ∞) : Lossless (.whileDo b p) :=
  fun s => terminatingMass_whileDo_eq_of_expectedIterations_ne_top hbody (h s)

/-- A lossless body and finite expected iteration counts give a lossless loop. -/
theorem Lossless.whileDo (hp : Lossless p)
    (h : ∀ s : CQState Store H, expectedIterations b p s ≠ ∞) : Lossless (.whileDo b p) :=
  lossless_whileDo_of_expectedIterations_ne_top ((validTot_mand_identity_iff b p).mpr
    fun s _ => hp s) h

end QuantumProgram
