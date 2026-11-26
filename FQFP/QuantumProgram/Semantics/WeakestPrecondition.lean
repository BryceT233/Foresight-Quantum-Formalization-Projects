/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/WP.lean: compositional weakest preconditions and expect_wp.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026

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
-/
module

public import FQFP.QuantumProgram.Logic.PrimitiveRules
public import FQFP.QuantumProgram.Semantics.SeqDecomp
import FQFP.CQM.Qudit.State.OperatorNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Weakest preconditions for total correctness

Pulling effects back through finitely many execution steps represents the terminal
post-expectation up to that horizon. Compactness of the finite-dimensional effect interval
gives an effect representing the limit on every input. The resulting transformer composes
backwards under sequencing.
-/

@[expose] public section

open Filter Qudit
open scoped ENNReal Topology

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- Pull a continuation indexed by the residual control through one small step. -/
private noncomputable def stepPre (p : Command Store Cell H)
    (K : Option (Command Store Cell H) → Assertion Store H) : Assertion Store H :=
  match p with
  | .skip => K none
  | .assign f => K none ∘ f
  | .channel f => (K none).channelPre f
  | .unitary r U => (K none).unitaryPre r U
  | .measure r I upd => (K none).measurePre r I upd
  | .seq p q => stepPre p (fun c => K (some (c.elim q (·.seq q))))
  | .ite b p q => fun σ => K (some (if b σ then p else q)) σ
  | .whileDo b p => fun σ => if b σ then K (some (p.seq (.whileDo b p))) σ else K none σ

private theorem expectation_stepPre (p : Command Store Cell H)
    (K : Option (Command Store Cell H) → Assertion Store H) (s : CQState Store H) :
    s.expectation (stepPre p K s.store) =
      ((p.step s).map fun c => c.state.expectation (K c.control c.state.store)).sum := by
  induction p generalizing K with
  | skip => simp [stepPre, Command.step]
  | assign f => simp [stepPre, Command.step, CQState.expectation]
  | channel f =>
    simpa [stepPre, Command.step, Assertion.channelPre, channelEffect, CQState.map] using
      s.expectation_pullbackEffect (f s.store) (K none s.store)
  | unitary r U =>
    by_cases h : Function.Injective (r s.store)
    · simpa [stepPre, Command.step, Assertion.unitaryPre, h, channelEffect, CQState.map] using
        s.expectation_pullbackEffect (U s.store h).toChannel (K none s.store)
    · simp [stepPre, Command.step, Assertion.unitaryPre, h, CQState.expectation_zero]
  | measure r I upd =>
    simpa [stepPre, Command.step, List.map_map, Function.comp_def] using
      s.expectation_measurePre r I upd (K none)
  | seq p q ih _ =>
    simpa [stepPre, Command.step, Configuration.seqWith, List.map_map, Function.comp_def] using
      ih (fun c => K (some (c.elim q (·.seq q))))
  | ite => simp [stepPre, Command.step]
  | whileDo b p _ => cases h : b s.store <;> simp [stepPre, Command.step, h]

/-- Backward evaluation of terminal effects at depths strictly below a finite horizon. -/
private noncomputable def preUpTo (B : Assertion Store H) :
    ℕ → Option (Command Store Cell H) → Assertion Store H
  | 0, _ => Assertion.zero
  | _ + 1, none => B
  | n + 1, some p => stepPre p (preUpTo B n)

private theorem ofReal_expectation_stepPre (p : Command Store Cell H)
    (K : Option (Command Store Cell H) → Assertion Store H) (s : CQState Store H) :
    ENNReal.ofReal (s.expectation (stepPre p K s.store)) =
      ((p.step s).map fun c =>
        ENNReal.ofReal (c.state.expectation (K c.control c.state.store))).sum := by
  rw [expectation_stepPre]
  simp only [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  exact ENNReal.ofReal_sum_of_nonneg fun _ _ => CQState.expectation_nonneg _ ((K _).isPositive _)

private theorem expectation_preUpTo (B : Assertion Store H) (n : ℕ)
    (c : Configuration Store Cell H) :
    ENNReal.ofReal (c.state.expectation (preUpTo B n c.control c.state.store)) =
      c.postUpTo n (fun σ => B σ) := by
  induction n generalizing c with
  | zero => simp [preUpTo, Assertion.zero, CQState.expectation_zero, Configuration.postUpTo]
  | succ n ih =>
    obtain ⟨_ | p, s⟩ := c <;>
      simp [preUpTo, Configuration.postUpTo_succ, Configuration.postAtE,
        Configuration.terminalWeightAt_zero, Configuration.next, ofReal_expectation_stepPre, ih]

private theorem exists_wp_effect (p : Command Store Cell H) (B : Assertion Store H) (σ : Store) :
    ∃ E : Set.Icc (0 : Operator H) 1, ∀ (ρ : Operator H) (hρ : ρ.IsPositive),
      let s : CQState Store H := ⟨σ, ρ, hρ⟩
      ENNReal.ofReal (s.expectation E) = (Configuration.mk (some p) s).PostH (fun τ => B τ) := by
  have : ProperSpace (Operator H) := FiniteDimensional.proper ℂ _
  have hc : IsCompact (Set.Icc (0 : Operator H) 1) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_Icc
      (CStarAlgebra.isBounded_of_bddAbove_of_bddBelow ⟨1, fun _ h => h.2⟩ ⟨0, fun _ h => h.1⟩)
  obtain ⟨E, hE, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => (preUpTo B n (some p) σ).property)
  refine ⟨⟨E, hE⟩, fun ρ hρ => ?_⟩
  let s : CQState Store H := ⟨σ, ρ, hρ⟩
  let c := Configuration.mk (some p) s
  have hcont : Continuous (fun A : Operator H => ENNReal.ofReal (s.expectation A)) :=
    ENNReal.continuous_ofReal.comp <| Complex.continuous_re.comp <|
      LinearMap.continuous_of_finiteDimensional ((LinearMap.trace ℂ H.state) ∘ₗ
        LinearMap.mulRight ℂ ρ)
  apply tendsto_nhds_unique (hcont.continuousAt.tendsto.comp hlim)
  simpa only [Function.comp_def, ← expectation_preUpTo] using
    (c.tendsto_postUpTo B.isPositive).comp hφ.tendsto_atTop

/-- Total-correctness weakest precondition, counting only terminal post-expectations. -/
@[no_expose] noncomputable def wp (p : Command Store Cell H) (B : Assertion Store H) :
    Assertion Store H :=
  fun σ => (exists_wp_effect p B σ).choose

/-- Backward evaluation agrees with the sum over all terminal execution histories. -/
theorem expectation_wp (p : Command Store Cell H) (B : Assertion Store H) (s : CQState Store H) :
    ENNReal.ofReal (s.expectation (wp p B s.store)) =
      (Configuration.mk (some p) s).PostH (fun σ => B σ) :=
  (exists_wp_effect p B s.store).choose_spec s.op s.positive

/-- Expectations on positive inputs detect pointwise order on effects. -/
theorem Assertion.le_iff_expectation {A B : Assertion Store H} :
    A ≤ B ↔ ∀ s : CQState Store H, s.expectation (A s.store) ≤ s.expectation (B s.store) := by
  refine ⟨fun h s => s.expectation_mono (h _), fun h σ => ?_⟩
  apply LinearMap.le_def.mpr
  refine ⟨(B.isPositive σ).isSymmetric.sub (A.isPositive σ).isSymmetric, fun x => ?_⟩
  have hx := h ⟨σ, Operator.outer x x, Operator.isPositive_outer x⟩
  simp only [CQState.expectation, Operator.trace_mul_outer] at hx
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x (((B σ : Operator H) - A σ) x)).re
  simpa only [LinearMap.sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hx

/-- A triple is totally valid exactly when its precondition is below the weakest one. -/
theorem validTot_iff_le_wp {A B : Assertion Store H} {p : Command Store Cell H} :
    validTot A p B ↔ A ≤ wp p B := by
  simp only [validTot, ← expectation_wp, Assertion.le_iff_expectation,
    ENNReal.ofReal_le_ofReal_iff (CQState.expectation_nonneg _ ((wp p B).isPositive _))]

/-- A precondition representing all terminal post-expectations is the weakest precondition. -/
theorem wp_eq_of_expectation {p : Command Store Cell H} {A B : Assertion Store H}
    (h : ∀ s : CQState Store H, (Configuration.mk (some p) s).PostH (fun σ => B σ) =
      ENNReal.ofReal (s.expectation (A s.store))) : wp p B = A := by
  apply le_antisymm
  · apply Assertion.le_iff_expectation.mpr
    intro s
    exact (ENNReal.ofReal_le_ofReal_iff (s.expectation_nonneg (A.isPositive _))).mp
      ((expectation_wp p B s).trans (h s)).le
  · exact validTot_iff_le_wp.mp fun s => (h s).ge

/-- The weakest precondition is monotone in the postcondition. -/
theorem wp_mono (p : Command Store Cell H) : Monotone (wp p) := by
  intro A B h
  apply validTot_iff_le_wp.mp
  intro s
  rw [expectation_wp]
  exact Configuration.PostH_mono _ h

/-- Sequential commands pull assertions back in reverse execution order. -/
@[simp] theorem wp_seq (p q : Command Store Cell H) (B : Assertion Store H) :
    wp (p.seq q) B = wp p (wp q B) := by
  apply wp_eq_of_expectation
  intro s
  let c := Configuration.mk (some p) s
  change (c.seqWith q).PostH _ = _
  rw [expectation_wp, c.PostH_seqWith q B.isPositive,
    c.PostH_eq_tsum_terminalWeightAt (wp q B).isPositive]
  simp only [expectation_wp]

private theorem wp_eq_stepPre (p : Command Store Cell H) (B : Assertion Store H) :
    wp p B = stepPre p (fun c => c.elim B (wp · B)) := by
  apply wp_eq_of_expectation
  intro s
  rw [Configuration.PostH_eq_sum_next s B.isPositive, ofReal_expectation_stepPre]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨_ | q, t⟩ _
  · rw [Configuration.PostH, tsum_eq_single 0]
    · simp [Configuration.postAt_eq_sum_frontier, Configuration.frontier]
    · rintro (_ | n) hn
      · exact (hn rfl).elim
      · simp [Configuration.postAt_eq_sum_frontier, Configuration.frontier_succ_terminal]
  · exact (expectation_wp q B t).symm

/-- Skipping preserves the postcondition. -/
@[simp] theorem wp_skip (B : Assertion Store H) : wp (.skip : Command Store Cell H) B = B :=
  wp_eq_stepPre .skip B

/-- Assignment substitutes into the classical argument of the postcondition. -/
@[simp] theorem wp_assign (f : Store → Store) (B : Assertion Store H) :
    wp (.assign f : Command Store Cell H) B = B ∘ f := wp_eq_stepPre _ _

/-- A channel pulls effects back through its dual. -/
@[simp] theorem wp_channel (f : Store → QuantumChannel H H) (B : Assertion Store H) :
    wp (.channel f : Command Store Cell H) B = B.channelPre f := wp_eq_stepPre _ _

/-- A local unitary uses the existing register-aware backward assertion. -/
@[simp] theorem wp_unitary {k : ℕ} (r : Store → Fin k → Cell)
    (U : ∀ σ, Function.Injective (r σ) → UnitaryProgram H) (B : Assertion Store H) :
    wp (.unitary r U) B = B.unitaryPre r U := wp_eq_stepPre _ _

/-- Measurement pulls each updated postcondition through its instrument branch. -/
@[simp] theorem wp_measure {k m : ℕ} (r : Store → Fin k → Cell)
    (I : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) (B : Assertion Store H) :
    wp (.measure r I upd) B = B.measurePre r I upd := wp_eq_stepPre _ _

/-- The classical guard selects the precondition of the corresponding branch. -/
@[simp] theorem wp_ite (b : Store → Bool) (p q : Command Store Cell H) (B : Assertion Store H)
    (σ : Store) : wp (.ite b p q) B σ = if b σ then wp p B σ else wp q B σ := by
  rw [wp_eq_stepPre]
  cases hb : b σ <;> simp [stepPre, hb]

/-- Unfold a loop once, pulling the residual loop precondition through its body. -/
theorem wp_whileDo (b : Store → Bool) (p : Command Store Cell H) (B : Assertion Store H)
    (σ : Store) : wp (.whileDo b p) B σ = if b σ then wp p (wp (.whileDo b p) B) σ else B σ := by
  rw [congrFun (wp_eq_stepPre (.whileDo b p) B) σ]
  cases hb : b σ <;> simp [stepPre, hb]

end QuantumProgram
