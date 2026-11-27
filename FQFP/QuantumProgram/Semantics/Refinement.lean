/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/Syntax.lean (compositional interpretation and loop unrollings)
QuantumComputation/QuantumHoareLogic/WP.lean (matching backward interpretation)
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

qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/WpSuffixCongr.lean (pointwise replacement through finite sequences)
Copyright 2026 Qedia contributors.
-/
module

public import FQFP.QuantumProgram.Semantics.Output.WhileFixedPoint
public import FQFP.QuantumProgram.Semantics.Precondition.Liberal
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Refinement of terminating quantum outputs

A refinement increases the terminal output in Löwner order at each store. Equivalently it
increases every total weakest precondition and decreases every liberal weakest precondition.
Refinement composes through the command language, including unbounded loops.
-/

@[expose] public section

open Qudit
open scoped ENNReal ComplexOrder

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}
variable {p p' q q' : Command Store Cell H} {A B : Assertion Store H}

/-- The replacement `q` has at least the terminating yield of `p` for every postcondition. -/
def Command.Refines (q p : Command Store Cell H) : Prop := ∀ B, wp p B ≤ wp q B

namespace Command.Refines

/-- Every command refines itself. -/
@[refl] theorem refl (p : Command Store Cell H) : p.Refines p := fun _ => le_rfl

/-- Successive refinements compose. -/
theorem trans (hp : p'.Refines p) (hq : q.Refines p') : q.Refines p :=
  fun B => (hp B).trans (hq B)

/-- Both commands of a sequence may be refined. -/
theorem seq (hp : p'.Refines p) (hq : q'.Refines q) : (p'.seq q').Refines (p.seq q) := by
  intro B
  simp only [wp_seq]
  exact (wp_mono p (hq B)).trans (hp (wp q' B))

/-- Both branches may be refined under the same guard. -/
theorem ite (b : Store → Bool) (hp : p'.Refines p) (hq : q'.Refines q) :
    (Command.ite b p' q').Refines (.ite b p q) := by
  intro B σ
  simp only [wp_ite]
  split
  · exact hp B σ
  · exact hq B σ

/-- Refining the body of an unbounded loop refines the loop. -/
theorem whileDo (b : Store → Bool) (hp : p'.Refines p) :
    (Command.whileDo b p').Refines (.whileDo b p) := by
  intro B
  apply (isLeast_whileWpStep b p B).2
  intro σ
  rw [wp_whileDo b p' B σ]
  change (if b σ then wp p (wp (.whileDo b p') B) σ else B σ) ≤ _
  split
  · exact hp _ σ
  · exact le_rfl

/-- Refine each command in a finite sequence of indexed calls. -/
theorem forList {ι : Type*} (xs : List ι) {body body' : ι → Command Store Cell H}
    (h : ∀ i ∈ xs, (body' i).Refines (body i)) :
    (Command.forList xs body').Refines (.forList xs body) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih =>
    exact (h x List.mem_cons_self).seq (ih fun i hi => h i (List.mem_cons_of_mem _ hi))

/-- Total specifications pass from the original command to its refinement. -/
theorem validTot (h : q.Refines p) (hp : QuantumProgram.validTot A p B) :
    QuantumProgram.validTot A q B :=
  validTot_iff_le_wp.mpr ((validTot_iff_le_wp.mp hp).trans (h B))

/-- Liberal preconditions decrease when a refinement increases terminating yield. -/
theorem wlp_le (h : q.Refines p) (B : Assertion Store H) : wlp q B ≤ wlp p B :=
  Assertion.antitone_compl (h B.compl)

/-- A partial specification of the refinement holds for the original command. -/
theorem validPar (h : q.Refines p) (hq : QuantumProgram.validPar A q B) :
    QuantumProgram.validPar A p B :=
  validPar_iff_le_wlp.mpr ((validPar_iff_le_wlp.mp hq).trans (h.wlp_le B))

end Command.Refines

/-- The total triples determine refinement. -/
theorem command_refines_iff_validTot :
    q.Refines p ↔ ∀ A B, validTot A p B → validTot A q B :=
  ⟨fun h _ _ => h.validTot, fun h B =>
    validTot_iff_le_wp.mp (h (wp p B) B (validTot_iff_le_wp.mpr le_rfl))⟩

/-- Partial triples determine the same refinement with implication in reverse order. -/
theorem command_refines_iff_validPar :
    q.Refines p ↔ ∀ A B, validPar A q B → validPar A p B := by
  refine ⟨fun h _ _ => h.validPar, fun h B => ?_⟩
  have hl := validPar_iff_le_wlp.mp
    (h (wlp q B.compl) B.compl (validPar_iff_le_wlp.mpr le_rfl))
  simpa only [wlp, Assertion.compl_compl] using Assertion.antitone_compl hl

private theorem terminalOp_le_of_refines [DecidableEq Store] (h : q.Refines p)
    (s : CQState Store H) (τ : Store) :
    (Configuration.mk (some p) s).terminalOp τ ≤ (Configuration.mk (some q) s).terminalOp τ := by
  let c : Configuration Store Cell H := ⟨some p, s⟩
  let d : Configuration Store Cell H := ⟨some q, s⟩
  apply LinearMap.le_def.mpr
  refine ⟨(d.isPositive_terminalOp τ).isSymmetric.sub (c.isPositive_terminalOp τ).isSymmetric,
    fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  let v : UnitState H := ⟨NormedSpace.normalize x,
    inner_self_eq_one_of_norm_eq_one (NormedSpace.norm_normalize hx)⟩
  let E : Assertion Store H := Assertion.pure v
  have hm := ENNReal.ofReal_le_ofReal (s.expectation_mono (h (E.mask (· = τ)) s.store))
  rw [expectation_wp, expectation_wp, Configuration.PostH_mask_singleton,
    Configuration.PostH_mask_singleton] at hm
  have he := (ENNReal.ofReal_le_ofReal_iff (Complex.nonneg_iff.mp
    ((E.isPositive τ).trace_mul_nonneg (d.isPositive_terminalOp τ))).1).mp hm
  change ((Density.pure v).op * c.terminalOp τ).trace.re ≤
    ((Density.pure v).op * d.terminalOp τ).trace.re at he
  simp only [Operator.trace] at he
  rw [LinearMap.trace_mul_comm ℂ _ (c.terminalOp τ),
    LinearMap.trace_mul_comm ℂ _ (d.terminalOp τ)] at he
  change (c.terminalOp τ * (Density.pure v).op).trace.re ≤
    (d.terminalOp τ * (Density.pure v).op).trace.re at he
  simp only [Density.pure, Operator.trace_mul_outer] at he
  have hv : (‖x‖ : ℂ) • v.val = x := by
    simpa only [Complex.coe_smul] using NormedSpace.norm_smul_normalize x
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x ((d.terminalOp τ - c.terminalOp τ) x)).re
  rw [← hv, map_smul, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.re_ofReal_mul]
  apply mul_nonneg (norm_nonneg x) (mul_nonneg (norm_nonneg x) ?_)
  rw [LinearMap.sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg]
  exact he

/-- Refinement is exactly the pointwise Löwner order of the terminal-output kernels. -/
theorem command_refines_iff_outputKernel_le [DecidableEq Store] :
    q.Refines p ↔ p.outputKernel ≤ q.outputKernel := by
  refine ⟨terminalOp_le_of_refines, fun h B => Assertion.le_iff_expectation.mpr fun s => ?_⟩
  let c : Configuration Store Cell H := ⟨some p, s⟩
  let d : Configuration Store Cell H := ⟨some q, s⟩
  apply (ENNReal.ofReal_le_ofReal_iff (s.expectation_nonneg ((wp q B).isPositive _))).mp
  rw [expectation_wp, expectation_wp]
  change c.PostH (fun σ => B σ) ≤ d.PostH (fun σ => B σ)
  rw [c.PostH_eq_tsum_trace_mul_terminalOp B.isPositive,
    d.PostH_eq_tsum_trace_mul_terminalOp B.isPositive]
  exact tsum_le_tsum fun σ => ENNReal.ofReal_le_ofReal (Complex.re_le_re
    ((B.isPositive σ).trace_mul_le_trace_mul_left (h s σ)))

/-- Commands give the same weakest preconditions exactly when all terminal outputs agree. -/
theorem wp_eq_iff_outputKernel_eq [DecidableEq Store] :
    wp p = wp q ↔ p.outputKernel = q.outputKernel := by
  constructor
  · intro h
    exact le_antisymm (command_refines_iff_outputKernel_le.mp fun B => (congrFun h B).le)
      (command_refines_iff_outputKernel_le.mp fun B => (congrFun h B).ge)
  · intro h
    funext B
    exact le_antisymm (command_refines_iff_outputKernel_le.mpr h.le B)
      (command_refines_iff_outputKernel_le.mpr h.ge B)

end QuantumProgram
