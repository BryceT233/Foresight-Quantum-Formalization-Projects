/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/SharpPost.lean: uniqueness of pure postconditions for total validity and derivations.
The local proof identifies the unnormalized output at each classical store by its support.

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Output.Terminal
public import FQFP.QuantumProgram.Logic.Assertion.ExactExpectation
public import FQFP.QuantumProgram.Logic.Soundness
import FQFP.CQM.Qudit.State.Support

/-!
# Pure postconditions determine the terminal quantum output

When a store-dependent rank-one test accounts for all terminating trace, each terminal store
carries its own trace times the specified pure density. Positive terminating trace then determines
a unique store-independent pure postcondition, even when the program measures or loops.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal ComplexOrder

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

namespace Configuration

variable [DecidableEq Store] (c : Configuration Store Cell H)

/-- An effect collects all terminating trace exactly when its complement has zero expectation
at every final classical store. -/
theorem PostH_eq_terminatingMass_iff (A : Assertion Store H) :
    c.PostH (fun σ => A σ) = c.terminatingMass ↔
      ∀ σ, (c.terminalState σ).expectation (A.compl σ) = 0 := by
  have h := c.PostH_add_PostH_compl A
  have hfin := (c.terminatingMass_le.trans_lt ENNReal.coe_lt_top).ne
  have hz : c.PostH (fun σ => A σ) = c.terminatingMass ↔
      c.PostH (fun σ => A.compl σ) = 0 := by
    constructor
    · intro he
      rw [he] at h
      exact (ENNReal.add_right_inj hfin).mp (h.trans (add_zero _).symm)
    · intro he
      simpa only [he, add_zero] using h
  rw [hz, c.PostH_eq_tsum_trace_mul_terminalOp A.compl.isPositive, tsum_eq_zero_iff]
  exact forall_congr' fun σ => ENNReal.ofReal_eq_zero.trans
    ⟨fun he => le_antisymm he ((c.terminalState σ).expectation_nonneg (A.compl.isPositive σ)),
      fun he => he.le⟩

/-- A sharp postcondition of full terminating expectation fixes the quantum output separately
at every classical store, including stores reached with zero trace. -/
theorem terminalOp_eq_trace_smul_pure (v : Store → UnitState H)
    (h : c.PostH (fun σ => Assertion.pure (v σ) σ) = c.terminatingMass) (σ : Store) :
    c.terminalOp σ = (c.terminalOp σ).trace • (Density.pure (v σ)).op := by
  have hX := c.isPositive_terminalOp σ
  by_cases ht : (c.terminalOp σ).trace = 0
  · rw [ht, zero_smul]
    exact hX.re_trace_eq_zero_iff.mp (congrArg Complex.re ht)
  let ρ := Density.normalize hX rfl ht
  let P := (Density.pure (v σ)).op
  let A : Assertion Store H := fun τ => Assertion.pure (v τ) τ
  have hP := A.compl.isPositive σ
  have hzero : ((1 - P) * c.terminalOp σ).trace = 0 := by
    apply Complex.ext
    · exact (c.PostH_eq_terminatingMass_iff A).mp h σ
    · exact (Complex.nonneg_iff.mp (hP.trace_mul_nonneg hX)).2.symm
  have hexp : ρ.expectation (1 - P) = 0 := by
    change ((1 - P) * ((c.terminalOp σ).trace⁻¹ • c.terminalOp σ)).trace.re = 0
    simp only [mul_smul_comm, Operator.trace, map_smul, smul_eq_mul] at hzero ⊢
    rw [hzero, mul_zero, Complex.zero_re]
  have hs := (ρ.expectation_eq_zero_iff hP).mp hexp
  have he : ρ = Density.pure (v σ) := by
    apply ρ.eq_pure_of_range_le
    rw [← Density.range_pure]
    intro x hx
    have hx' : x - P x = 0 := hs hx
    exact ⟨x, (sub_eq_zero.mp hx').symm⟩
  have hop := congrArg Density.op he
  change (c.terminalOp σ).trace⁻¹ • c.terminalOp σ = _ at hop
  rw [← hop, smul_inv_smul₀ ht]

/-- Testing a pure projector collects all terminal trace exactly when every output is its
trace times that projector. -/
theorem PostH_pure_eq_terminatingMass_iff (v : Store → UnitState H) :
    c.PostH (fun σ => Assertion.pure (v σ) σ) = c.terminatingMass ↔
      ∀ σ, c.terminalOp σ = (c.terminalOp σ).trace • (Density.pure (v σ)).op := by
  refine ⟨c.terminalOp_eq_trace_smul_pure v, fun h => ?_⟩
  apply (c.PostH_eq_terminatingMass_iff _).mpr
  intro σ
  change ((1 - (Density.pure (v σ)).op) * c.terminalOp σ).trace.re = 0
  rw [h σ, mul_smul_comm, sub_mul, one_mul, Density.pure_mul_self, sub_self, smul_zero]
  simp [Operator.trace]

omit [DecidableEq Store] in
/-- With positive terminating trace, two sharp postconditions of full expectation describe the
same pure density. The input may be mixed and some of its trace may diverge. -/
theorem pure_post_unique (hm : c.terminatingMass ≠ 0) {u v : UnitState H}
    (hu : c.PostH (fun σ => Assertion.pure u σ) = c.terminatingMass)
    (hv : c.PostH (fun σ => Assertion.pure v σ) = c.terminatingMass) :
    Density.pure u = Density.pure v := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ, (c.terminalOp σ).trace ≠ 0 := by
    by_contra! hz
    exact hm (by simp [c.terminatingMass_eq_tsum_trace_terminalOp, hz])
  apply Density.ext
  have he := (c.terminalOp_eq_trace_smul_pure (fun _ => u) hu σ).symm.trans
    (c.terminalOp_eq_trace_smul_pure (fun _ => v) hv σ)
  simpa only [inv_smul_smul₀ hσ] using congrArg ((c.terminalOp σ).trace⁻¹ • ·) he

end Configuration

/-- Two total triples from the same normalized pure input identify the same pure output. -/
theorem validTot_pure_post_unique (σ : Store) {p : Command Store Cell H} {w u v : UnitState H}
    (hu : validTot (Assertion.pure w) p (Assertion.pure u))
    (hv : validTot (Assertion.pure w) p (Assertion.pure v)) : Density.pure u = Density.pure v := by
  classical
  let s : CQState Store H := ⟨σ, (Density.pure w).op, (Density.pure w).positive⟩
  let c := Configuration.mk (some p) s
  have hm : (s.mass : ℝ≥0∞) = 1 := by
    apply congrArg ((↑) : ℝ≥0 → ℝ≥0∞)
    exact Subtype.ext (congrArg Complex.re (Density.pure w).trace_one)
  have hw : ENNReal.ofReal (s.expectation (Assertion.pure w σ)) = 1 := by
    change ENNReal.ofReal (((Density.pure w).op * (Density.pure w).op).trace.re) = 1
    simp
  have full (u : UnitState H) (h : validTot (Assertion.pure w) p (Assertion.pure u)) :
      1 ≤ c.PostH (fun τ => Assertion.pure u τ) := hw ▸ h s
  have upper (u : UnitState H) : c.PostH (fun τ => Assertion.pure u τ) ≤ c.terminatingMass :=
    c.PostH_le_terminatingMass fun τ => (Assertion.pure u τ).2.2
  have hc := c.terminatingMass_le.trans_eq hm
  exact c.pure_post_unique (ne_of_gt (zero_lt_one.trans_le ((full u hu).trans (upper u))))
    (le_antisymm (upper u) (hc.trans (full u hu))) (le_antisymm (upper v) (hc.trans (full v hv)))

/-- Sound total derivations from the same pure input determine a unique output projector. -/
theorem DerivTot.pure_post_unique (σ : Store) {p : Command Store Cell H} {w u v : UnitState H}
    (hu : DerivTot (Assertion.pure w) p (Assertion.pure u))
    (hv : DerivTot (Assertion.pure w) p (Assertion.pure v)) : Density.pure u = Density.pure v :=
  validTot_pure_post_unique σ hu.sound hv.sound

end QuantumProgram
