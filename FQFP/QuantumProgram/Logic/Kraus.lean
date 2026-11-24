/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for effect pullbacks and correctness under finite Kraus accumulation.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Kraus.lean (subnormalized effect bound)
Qhl/History/KrausSum.lean (finite sums, framed terminal expectations and residual mass)
Qhl/Logic/Source/Accumulation.lean (common-postcondition accumulation)

Copyright 2026 Qedia contributors.
Modified by Foresight Quantum in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.KrausFrame
public import FQFP.QuantumProgram.Logic.Convex

/-!
# Finite Kraus accumulation

A complete family splits the trace among conjugated inputs. A frame for every member
transports the same split through execution, including the mass of nonterminating paths.
-/

@[expose] public section

open Qudit Finset
open scoped ENNReal

namespace QuantumProgram

variable {S Cell ι : Type*} {H : Qudit}

/-- Pull each effect back through its Kraus operator and sum. Subnormalization suffices. -/
noncomputable def Assertion.kraus [Fintype ι] (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) (A : ι → Assertion S H) : Assertion S H :=
  fun σ => ⟨∑ i, Superoperator.conjugate (K σ i).adjoint (A i σ), by
    let F (i : ι) : CPMap H H :=
      ⟨_, Superoperator.isCompletelyPositive_conjugate (K σ i).adjoint⟩
    refine ⟨sum_nonneg fun i _ => (F i).map_nonneg (A i σ).2.1, ?_⟩
    refine (sum_le_sum fun i _ => (F i).monotone (A i σ).2.2).trans ?_
    simpa only [F, Superoperator.conjugate_apply, LinearMap.adjoint_adjoint,
      Module.End.one_eq_id, LinearMap.id_comp] using hK σ⟩

/-- A complete family pulls the identity effect back to the identity. -/
theorem Assertion.kraus_identity [Fintype ι] (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1) :
    kraus K (fun σ => (hK σ).le) (fun _ => identity) = identity := by
  funext σ
  apply Subtype.ext
  simpa only [kraus, identity, Superoperator.conjugate_apply, LinearMap.adjoint_adjoint,
    Module.End.one_eq_id, LinearMap.id_comp] using hK σ

/-- An observable pulled back by the adjoint is paired with the conjugated input. -/
theorem CQState.expectation_krausMap (s : CQState S H) (K : S → Operator H) (B : Operator H) :
    (s.krausMap K).expectation B = s.expectation (Superoperator.conjugate (K s.store).adjoint B) :=
  congrArg Complex.re (Superoperator.trace_conjugate_adjoint (K s.store) s.op B).symm

/-- Trace expectation distributes over finite sums of arbitrary operators. -/
theorem CQState.expectation_sum (s : CQState S H) (t : Finset ι) (A : ι → Operator H) :
    s.expectation (∑ i ∈ t, A i) = ∑ i ∈ t, s.expectation (A i) := by
  simp only [expectation, sum_mul, Operator.trace, map_sum, Complex.re_sum]

/-- Extended nonnegative expectation distributes over finite sums of positive operators. -/
theorem CQState.ofReal_expectation_sum (s : CQState S H) (t : Finset ι) (A : ι → Operator H)
    (hA : ∀ i ∈ t, (A i).IsPositive) :
    ENNReal.ofReal (s.expectation (∑ i ∈ t, A i)) =
      ∑ i ∈ t, ENNReal.ofReal (s.expectation (A i)) := by
  rw [s.expectation_sum, ENNReal.ofReal_sum_of_nonneg fun i hi => s.expectation_nonneg (hA i hi)]

/-- Positive observables can be summed before or after taking the full post-expectation. -/
theorem Configuration.PostH_sum (c : Configuration S Cell H) (t : Finset ι)
    (A : ι → S → Operator H) (hA : ∀ i ∈ t, ∀ σ, (A i σ).IsPositive) :
    c.PostH (fun σ => ∑ i ∈ t, A i σ) = ∑ i ∈ t, c.PostH (A i) := by
  rw [c.PostH_eq_tsum_terminalWeightAt
    (fun σ => LinearMap.isPositive_sum t (fun i hi => hA i hi σ))]
  simp_rw [CQState.ofReal_expectation_sum _ t _ (fun i hi => hA i hi _),
    c.terminalWeightAt_finsetSum, Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  exact sum_congr rfl fun i hi => (c.PostH_eq_tsum_terminalWeightAt (hA i hi)).symm

/-- Move one framed conjugation from the input to an arbitrary positive terminal observable. -/
theorem Configuration.KrausFrame.PostH_map {c : Configuration S Cell H} {K : S → Operator H}
    (hc : c.KrausFrame K) (A : S → Operator H) (hA : ∀ σ, (A σ).IsPositive) :
    (c.krausMap K).PostH A = c.PostH (fun σ => Superoperator.conjugate (K σ).adjoint (A σ)) := by
  rw [PostH_eq_tsum_terminalWeightAt _ hA, c.PostH_eq_tsum_terminalWeightAt
    (fun σ => (Superoperator.isCompletelyPositive_conjugate _).isPositive _ (hA σ))]
  simp only [hc.terminalWeightAt_map, CQState.expectation_krausMap]
  rfl

variable [Fintype ι]

/-- Summing the input expectations of a Kraus combination uses the actual branch weights. -/
theorem CQState.ofReal_expectation_kraus (s : CQState S H) (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) (A : ι → Assertion S H) :
    ENNReal.ofReal (s.expectation (Assertion.kraus K hK A s.store)) =
      ∑ i, ENNReal.ofReal ((s.krausMap (fun σ => K σ i)).expectation (A i s.store)) := by
  simp_rw [CQState.expectation_krausMap]
  exact s.ofReal_expectation_sum univ _ fun i _ =>
    (Superoperator.isCompletelyPositive_conjugate _).isPositive _ ((A i).isPositive s.store)

/-- Terminal histories split by conjugating the initial state for each framed operator. -/
theorem Configuration.PostH_kraus (c : Configuration S Cell H) (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) (hc : ∀ i, c.KrausFrame (fun σ => K σ i))
    (A : ι → Assertion S H) :
    c.PostH (fun σ => Assertion.kraus K hK A σ) =
      ∑ i, (c.krausMap (fun σ => K σ i)).PostH (fun σ => A i σ) := by
  simp_rw [(hc _).PostH_map _ (A _).isPositive]
  exact c.PostH_sum univ _ fun i _ σ =>
    (Superoperator.isCompletelyPositive_conjugate _).isPositive _ ((A i).isPositive σ)

/-- Normalization accounts for all input mass, including zero-weight branches. -/
theorem CQState.sum_mass_krausMap (s : CQState S H) (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1) :
    ∑ i, ((s.krausMap (fun σ => K σ i)).mass : ℝ≥0∞) = s.mass := by
  have h := s.ofReal_expectation_kraus K (fun σ => (hK σ).le) (fun _ => Assertion.identity)
  simpa only [Assertion.kraus_identity K hK, Assertion.identity, expectation_one,
    ENNReal.ofReal_coe_nnreal] using h.symm

/-- A complete framed family accounts for the full terminating mass. -/
theorem Configuration.sum_terminatingMass_krausMap (c : Configuration S Cell H)
    (K : S → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1)
    (hc : ∀ i, c.KrausFrame (fun σ => K σ i)) :
    ∑ i, (c.krausMap (fun σ => K σ i)).terminatingMass = c.terminatingMass := by
  simpa only [Assertion.kraus_identity K hK, Assertion.identity, PostH_one] using
    (c.PostH_kraus K (fun σ => (hK σ).le) hc (fun _ => Assertion.identity)).symm

/-- Residual mass splits over the same family even in the presence of blocking or divergence. -/
theorem Configuration.sum_nonterminatingMass_krausMap (c : Configuration S Cell H)
    (K : S → ι → Operator H) (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1)
    (hc : ∀ i, c.KrausFrame (fun σ => K σ i)) :
    ∑ i, (c.krausMap (fun σ => K σ i)).nonterminatingMass = c.nonterminatingMass := by
  apply (ENNReal.add_right_inj (ne_top_of_le_ne_top ENNReal.coe_ne_top c.terminatingMass_le)).mp
  conv_lhs => rw [← c.sum_terminatingMass_krausMap K hK hc, ← sum_add_distrib]
  simpa only [terminatingMass_add_nonterminatingMass, krausMap] using c.state.sum_mass_krausMap K hK

/-- Combine total triples by a subnormalized family whose members frame the program. -/
theorem validTot_kraus (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i ≤ 1) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) {A B : ι → Assertion S H}
    (h : ∀ i, validTot (A i) p (B i)) : validTot (Assertion.kraus K hK A) p
      (Assertion.kraus K hK B) := by
  intro s
  rw [s.ofReal_expectation_kraus, Configuration.PostH_kraus _ K hK
    (fun i => (Configuration.frame_running _ _ _).2 (hp i))]
  exact sum_le_sum fun i _ => h i (s.krausMap (fun σ => K σ i))

/-- Combine partial triples by a complete framed family, splitting nontermination credit. -/
theorem validPar_kraus (K : S → ι → Operator H)
    (hK : ∀ σ, ∑ i, (K σ i).adjoint ∘ₗ K σ i = 1) {p : Command S Cell H}
    (hp : ∀ i, p.KrausFrame (fun σ => K σ i)) {A B : ι → Assertion S H}
    (h : ∀ i, validPar (A i) p (B i)) :
    validPar (Assertion.kraus K (fun σ => (hK σ).le) A) p
      (Assertion.kraus K (fun σ => (hK σ).le) B) := by
  intro s
  let c := Configuration.mk (some p) s
  have hc (i) : c.KrausFrame (fun σ => K σ i) := (Configuration.frame_running _ _ _).2 (hp i)
  rw [s.ofReal_expectation_kraus, c.PostH_kraus _ _ hc, ← c.sum_nonterminatingMass_krausMap K hK hc,
    ← sum_add_distrib]
  exact sum_le_sum fun i _ => h i (s.krausMap (fun σ => K σ i))

end QuantumProgram
