/-
Copyright (c) 2026 Qedia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qedia contributors
-/

/-
Qhl source for weighted sums of effects and validity under subprobability mixtures.
qedia/quantum-formal-verification @ 3dfe80b893e2ab949a0428a2e18c06153b310bd0
Qhl/Logic/Source/Convex.lean
Qhl/Logic/InitBlock.lean: Assn.scaled and its underlying operator.

Copyright 2026 Qedia contributors.
Modified by Shanghai Fuxi Quantum Technology Co., Ltd. in 2026
-/
module

public import FQFP.QuantumProgram.Semantics.Approximation

/-!
# Finite subprobability combinations of quantum assertions

Expectations and terminal post-expectations distribute over the weighted sum. For partial
correctness the sum of the weights bounds the total credit for nontermination.
-/

@[expose] public section

open Qudit Finset
open scoped NNReal ENNReal ComplexOrder

namespace QuantumProgram

variable {Store Cell ι : Type*} {H : Qudit} [Fintype ι]

/-- A finite combination of effects with nonnegative weights of total mass at most one. -/
noncomputable def Assertion.convex (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1)
    (A : ι → Assertion Store H) : Assertion Store H := fun σ =>
  ⟨∑ i, ((w i : ℝ) : ℂ) • (A i σ).val,
    sum_nonneg fun i _ => smul_nonneg (Complex.zero_le_real.mpr (w i).2) (A i σ).2.1, by
      calc
        _ ≤ ∑ i, ((w i : ℝ) : ℂ) • (1 : Operator H) :=
          sum_le_sum fun i _ => smul_le_smul_of_nonneg_left (A i σ).2.2
            (Complex.zero_le_real.mpr (w i).2)
        _ = (((∑ i, w i : ℝ≥0) : ℝ) : ℂ) • (1 : Operator H) := by
          rw [← sum_smul]; push_cast; rfl
        _ ≤ (1 : ℂ) • (1 : Operator H) :=
          smul_le_smul_of_nonneg_right
            (Complex.real_le_real.mpr (show (↑(∑ i, w i) : ℝ) ≤ 1 from hw))
            (Assertion.identity (H := H) ()).2.1
        _ = 1 := one_smul _ _⟩

/-- An empty sum of effects is the zero assertion at every store. -/
theorem Assertion.convex_empty [IsEmpty ι] (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1)
    (A : ι → Assertion Store H) : Assertion.convex w hw A = Assertion.zero := by
  funext σ
  apply Subtype.ext
  simp [Assertion.convex, Assertion.zero]

/-- The expectation of a finite mixture is the mixture of the component expectations. -/
theorem CQState.ofReal_expectation_convex (s : CQState Store H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (A : ι → Assertion Store H) :
    ENNReal.ofReal (s.expectation (Assertion.convex w hw A s.store)) =
      ∑ i, (w i : ℝ≥0∞) * ENNReal.ofReal (s.expectation (A i s.store)) := by
  have he : s.expectation (Assertion.convex w hw A s.store) =
      ∑ i, (w i : ℝ) * s.expectation (A i s.store) := by
    simp [Assertion.convex, CQState.expectation, Finset.sum_mul, Operator.trace]
  rw [he, ENNReal.ofReal_sum_of_nonneg (s := univ)
    (f := fun i => (w i : ℝ) * s.expectation (A i s.store))
    (fun i _ => mul_nonneg (w i).2 (s.expectation_nonneg ((A i).isPositive s.store)))]
  simp [ENNReal.ofReal_mul]

/-- Scale every effect by a probability, as a singleton subprobability mixture. -/
noncomputable def Assertion.scaled (A : Assertion Store H) (r : ℝ≥0) (hr : r ≤ 1) :
    Assertion Store H :=
  Assertion.convex (fun _ : Unit => r) (by simpa using hr) fun _ => A

/-- The operator of a scaled assertion is the scalar multiple of the original operator. -/
theorem Assertion.scaled_apply (A : Assertion Store H) (r : ℝ≥0) (hr : r ≤ 1) (σ : Store) :
    (A.scaled r hr σ).val = ((r : ℝ) : ℂ) • (A σ).val := by
  simp [Assertion.scaled, Assertion.convex]

/-- Scaling an effect scales its expectation on every weighted input. -/
theorem CQState.ofReal_expectation_scaled (s : CQState Store H) (A : Assertion Store H)
    (r : ℝ≥0) (hr : r ≤ 1) :
    ENNReal.ofReal (s.expectation (A.scaled r hr s.store)) =
      r * ENNReal.ofReal (s.expectation (A s.store)) := by
  simp [Assertion.scaled, s.ofReal_expectation_convex]

/-- Finite sums commute with the sum over terminal occurrences at an exact depth. -/
theorem Configuration.terminalWeightAt_sum (c : Configuration Store Cell H) (n : ℕ)
    (f : ι → CQState Store H → ℝ≥0∞) :
    c.terminalWeightAt n (fun s => ∑ i, f i s) = ∑ i, c.terminalWeightAt n (f i) :=
  c.terminalWeightAt_finsetSum n univ f

/-- Terminal history expectations distribute over finite subprobability combinations. -/
theorem Configuration.PostH_convex (c : Configuration Store Cell H) (w : ι → ℝ≥0)
    (hw : ∑ i, w i ≤ 1) (A : ι → Assertion Store H) :
    c.PostH (fun σ => Assertion.convex w hw A σ) =
      ∑ i, (w i : ℝ≥0∞) * c.PostH (fun σ => A i σ) := by
  rw [← c.terminalWeight_expectation (Assertion.convex w hw A).isPositive]
  simp_rw [CQState.ofReal_expectation_convex, c.terminalWeight_finsetSum,
    c.terminalWeight_const_mul, c.terminalWeight_expectation ((A _).isPositive)]

/-- Total validity is closed under finite subprobability combinations. -/
theorem validTot_convex (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) {A B : ι → Assertion Store H}
    {P : Command Store Cell H} (h : ∀ i, validTot (A i) P (B i)) :
    validTot (Assertion.convex w hw A) P (Assertion.convex w hw B) := by
  intro s
  rw [s.ofReal_expectation_convex, Configuration.PostH_convex]
  exact sum_le_sum fun i _ => mul_le_mul le_rfl (h i s) bot_le bot_le

/-- In partial correctness the mixed residual mass is at most one copy of the residual mass. -/
theorem validPar_convex (w : ι → ℝ≥0) (hw : ∑ i, w i ≤ 1) {A B : ι → Assertion Store H}
    {P : Command Store Cell H} (h : ∀ i, validPar (A i) P (B i)) :
    validPar (Assertion.convex w hw A) P (Assertion.convex w hw B) := by
  intro s
  rw [s.ofReal_expectation_convex, Configuration.PostH_convex]
  let c := Configuration.mk (some P) s
  have hi (i : ι) : (w i : ℝ≥0∞) * ENNReal.ofReal (s.expectation (A i s.store)) ≤
      (w i : ℝ≥0∞) * (c.PostH (fun σ => B i σ) + c.nonterminatingMass) :=
    mul_le_mul le_rfl (h i s) bot_le bot_le
  apply (sum_le_sum fun i _ => hi i).trans
  simp only [mul_add, sum_add_distrib]
  rw [← sum_mul]
  have hs : ∑ i, (w i : ℝ≥0∞) ≤ 1 := by exact_mod_cast hw
  exact add_le_add le_rfl (by
    simpa only [one_mul] using mul_le_mul hs (le_refl c.nonterminatingMass) bot_le bot_le)

end QuantumProgram
