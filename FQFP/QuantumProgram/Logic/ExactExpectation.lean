/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Semantics.Approximation
public import FQFP.QuantumProgram.Logic.PrimitiveRules

/-!
# Exact expectations from complementary effects

An effect and its complement partition the trace at each terminal occurrence. Total triples
for both tests therefore determine the post-expectation on every weighted input.
-/

@[expose] public section

open Qudit
open scoped ENNReal

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- The effect complementary to an assertion at each store. -/
noncomputable def Assertion.compl (A : Assertion Store H) : Assertion Store H := fun σ =>
  ⟨1 - (A σ : Operator H), sub_nonneg.mpr (A σ).2.2, sub_le_self _ (A σ).2.1⟩

/-- The two complementary expectations sum to the input trace. -/
theorem CQState.expectation_add_compl (s : CQState Store H) (A : Assertion Store H) :
    s.expectation (A s.store) + s.expectation (A.compl s.store) = s.mass := by
  rw [← s.expectation_one]
  simp [expectation, Assertion.compl, sub_mul, Operator.trace]

/-- Complementary branch weights partition the trace in the extended nonnegative reals. -/
theorem CQState.ofReal_expectation_add_compl (s : CQState Store H) (A : Assertion Store H) :
    ENNReal.ofReal (s.expectation (A s.store)) + ENNReal.ofReal (s.expectation (A.compl s.store)) =
      s.mass := by
  rw [← ENNReal.ofReal_add (s.expectation_nonneg (A.isPositive _))
    (s.expectation_nonneg (A.compl.isPositive _)), s.expectation_add_compl,
    ENNReal.ofReal_coe_nnreal]

/-- Complementary post-expectations collect exactly the terminating trace. -/
theorem Configuration.PostH_add_PostH_compl (c : Configuration Store Cell H)
    (A : Assertion Store H) :
    c.PostH (fun σ => A σ) + c.PostH (fun σ => A.compl σ) = c.terminatingMass := by
  rw [c.PostH_eq_tsum_terminalWeightAt A.isPositive,
    c.PostH_eq_tsum_terminalWeightAt A.compl.isPositive, ← ENNReal.tsum_add]
  exact tsum_congr fun n => by
    rw [← c.terminalWeightAt_add, ← c.terminalWeightAt_mass]
    exact congrArg (c.terminalWeightAt n) (funext fun s => s.ofReal_expectation_add_compl A)

/-- Complementary total triples determine the post-expectation exactly. -/
theorem PostH_eq_of_complement {A B : Assertion Store H} {p : Command Store Cell H}
    (h : validTot A p B) (hc : validTot A.compl p B.compl) (s : CQState Store H) :
    (Configuration.mk (some p) s).PostH (fun σ => B σ) =
      ENNReal.ofReal (s.expectation (A s.store)) := by
  let c := Configuration.mk (some p) s
  apply le_antisymm _ (h s)
  have hfin := ENNReal.ofReal_ne_top (r := s.expectation (A.compl s.store))
  apply ENNReal.le_of_add_le_add_right hfin
  exact (add_le_add le_rfl (hc s)).trans <| (c.PostH_add_PostH_compl B).le.trans <|
    c.terminatingMass_le.trans_eq (s.ofReal_expectation_add_compl A).symm

/-- The Heisenberg precondition of a trace-preserving channel preserves complements. -/
theorem Assertion.channelPre_compl (A : Assertion Store H) (f : Store → QuantumChannel H H) :
    A.compl.channelPre f = (A.channelPre f).compl := by
  funext σ
  apply Subtype.ext
  change (f σ).toCPMap.dual.toSuperoperator (1 - (A σ : Operator H)) = 1 - _
  rw [map_sub, (f σ).toCPMap.isTracePreserving_iff_dual_one.mp (f σ).tracePreserving]
  rfl

end QuantumProgram
