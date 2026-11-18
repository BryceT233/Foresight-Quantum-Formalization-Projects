/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.QuantumProgram.Denotation
import FQFP.Analysis.InnerProductSpace.PositiveTrace
import FQFP.CQM.Qudit.Channel.Choi
import FQFP.CQM.Qudit.Channel.Process.Dual

/-!
# Post-expectations and semantic validity

Following `Qhl/History/Correctness.lean`, `Configuration.PostH` sums the real trace
pairings of terminal branches at each depth, then sums over depths in the extended
nonnegative reals. The two judgements of `Qhl/Logic/Assertion.lean` quantify over all
positive input operators. An assertion assigns an effect to each classical store.
-/

@[expose] public section

open CategoryTheory DaggerCategory Qudit
open scoped NNReal ENNReal ComplexOrder

namespace QuantumProgram

variable {Store Cell : Type*} {H : Qudit}

/-- The real trace pairing of an observable with the unnormalized quantum state. -/
noncomputable def CQState.expectation (s : CQState Store H) (A : Operator H) : ℝ :=
  (A * s.op).trace.re

/-- Cyclicity gives the order of factors used in the QHL⁺ formula `Re Tr(ρ A)`. -/
theorem CQState.expectation_eq_re_trace_mul (s : CQState Store H) (A : Operator H) :
    s.expectation A = (s.op * A).trace.re :=
  congrArg Complex.re (LinearMap.trace_mul_comm ℂ A s.op)

/-- A positive observable has nonnegative expectation on every weighted branch. -/
theorem CQState.expectation_nonneg (s : CQState Store H) {A : Operator H} (h : A.IsPositive) :
    0 ≤ s.expectation A := (Complex.nonneg_iff.mp (h.trace_mul_nonneg s.positive)).1

/-- The identity observable reads the whole branch mass. -/
theorem CQState.expectation_one (s : CQState Store H) : s.expectation 1 = s.mass := by
  rw [expectation, one_mul]
  rfl

/-- Expectation respects the Löwner order on observables. -/
theorem CQState.expectation_mono (s : CQState Store H) {A B : Operator H} (h : A ≤ B) :
    s.expectation A ≤ s.expectation B := by
  simpa only [expectation, sub_mul, Operator.trace, map_sub, Complex.sub_re, sub_nonneg] using
    s.expectation_nonneg (LinearMap.le_def.mp h)

/-- Evolving both a branch and its rank-one test by an isometry preserves the expectation. -/
theorem CQState.expectation_outer_map {K : Qudit} (s : CQState Store H) (f : H ⟶ K)
    [IsIsometry f] (v : H.state) :
    (s.map (QuantumChannel.ofIsometry f)).expectation (Operator.outer (f v) (f v)) =
      s.expectation (Operator.outer v v) := by
  apply congrArg Complex.re
  change (Operator.outer (f.hom v) (f.hom v) * Superoperator.conjugate f.hom s.op).trace = _
  rw [← Superoperator.trace_conjugate_adjoint, Superoperator.conjugate_outer,
    hom_adjoint_apply_of_isIsometry]

namespace Configuration

/-- The sum of the post-observable's expectations over all terminal occurrences at depth `n`. -/
noncomputable def postAt (c : Configuration Store Cell H) (n : ℕ) (A : Store → Operator H) : ℝ :=
  ((c.terminalHistories n).map (fun p => p.1.state.expectation (A p.1.state.store))).sum

/-- The filtered configuration frontier gives the same sum, including repeated endpoints. -/
theorem postAt_eq_sum_frontier (c : Configuration Store Cell H) (n : ℕ) (A : Store → Operator H) :
    c.postAt n A = (((c.frontier n).filter (·.control.isNone)).map
      (fun d => d.state.expectation (A d.state.store))).sum := by
  rw [← terminalHistories_map_fst, List.map_map]
  rfl

/-- Positive post-observables contribute a nonnegative sum at each depth. -/
theorem postAt_nonneg (c : Configuration Store Cell H) (n : ℕ) {A : Store → Operator H}
    (hA : ∀ σ, (A σ).IsPositive) : 0 ≤ c.postAt n A := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
  exact p.1.state.expectation_nonneg (hA _)

/-- Post-observables bounded by the identity collect at most the mass terminating at this depth. -/
theorem postAt_le_terminalMassAt (c : Configuration Store Cell H) (n : ℕ) {A : Store → Operator H}
    (hA : ∀ σ, A σ ≤ 1) : c.postAt n A ≤ c.terminalMassAt n := by
  rw [terminalMassAt_eq_sum_terminalHistories, NNReal.coe_list_sum, List.map_map]
  exact List.sum_le_sum fun p _ =>
    (p.1.state.expectation_mono (hA _)).trans_eq p.1.state.expectation_one

/-- The post-expectation across all terminating depths of the run. -/
noncomputable def PostH (c : Configuration Store Cell H) (A : Store → Operator H) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (c.postAt n A)

/-- The post-expectation of an effect family is bounded by the total terminating trace. -/
theorem PostH_le_terminatingMass (c : Configuration Store Cell H) {A : Store → Operator H}
    (hA : ∀ σ, A σ ≤ 1) : c.PostH A ≤ c.terminatingMass := by
  apply ENNReal.tsum_le_tsum
  intro n
  exact (ENNReal.ofReal_le_ofReal (c.postAt_le_terminalMassAt n hA)).trans_eq
    ENNReal.ofReal_coe_nnreal

/-- In particular the post-expectation of an effect is bounded by the initial mass. -/
theorem PostH_le_mass (c : Configuration Store Cell H) {A : Store → Operator H}
    (hA : ∀ σ, A σ ≤ 1) : c.PostH A ≤ c.state.mass :=
  (c.PostH_le_terminatingMass hA).trans c.terminatingMass_le

/-- The identity post-observable collects exactly the terminating mass. -/
theorem PostH_one (c : Configuration Store Cell H) :
    c.PostH (fun _ => 1) = c.terminatingMass := by
  apply tsum_congr
  intro n
  rw [postAt, terminalMassAt_eq_sum_terminalHistories, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_list_sum, List.map_map]
  simp only [CQState.expectation_one, Function.comp_def]

/-- A singleton terminal frontier contributes its endpoint's expectation at that depth. -/
theorem ofReal_expectation_le_PostH_of_frontier {c : Configuration Store Cell H} {n : ℕ}
    {s : CQState Store H} (h : c.frontier n = [⟨none, s⟩]) (A : Store → Operator H) :
    ENNReal.ofReal (s.expectation (A s.store)) ≤ c.PostH A := by
  have hn : c.postAt n A = s.expectation (A s.store) := by simp [postAt_eq_sum_frontier, h]
  rw [← hn]
  exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (c.postAt k A)) n

/-- A running command with one successor has the same post-expectation as that successor. -/
theorem PostH_singleton {p : Command Store Cell H} {s : CQState Store H}
    {d : Configuration Store Cell H} (h : (Configuration.mk (some p) s).next = [d])
    (A : Store → Operator H) : (Configuration.mk (some p) s).PostH A = d.PostH A := by
  let c := Configuration.mk (some p) s
  have h₁ : c.frontier 1 = [d] := by simpa [c, frontier] using h
  have hz : c.postAt 0 A = 0 := by simp [c, postAt_eq_sum_frontier, frontier]
  change (∑' n, ENNReal.ofReal (c.postAt n A)) = _
  rw [tsum_eq_zero_add' ENNReal.summable, hz, ENNReal.ofReal_zero, zero_add]
  apply tsum_congr
  intro n
  rw [postAt_eq_sum_frontier, Nat.add_comm n 1, frontier_add_of_singleton h₁,
    postAt_eq_sum_frontier]

/-- If all one-step successors are terminal, only depth one contributes to the post-expectation. -/
theorem PostH_of_step_terminals {p : Command Store Cell H} {s : CQState Store H}
    {outputs : List (CQState Store H)} (h : p.step s = outputs.map (Configuration.mk none))
    (A : Store → Operator H) :
    (Configuration.mk (some p) s).PostH A =
      ENNReal.ofReal ((outputs.map fun t => t.expectation (A t.store)).sum) := by
  let c := Configuration.mk (some p) s
  have h₁ : c.frontier 1 = outputs.map (Configuration.mk none) := by
    simpa [c, frontier, next] using h
  have h₂ (k : ℕ) : c.frontier (k + 2) = [] := by
    induction k with
    | zero =>
      change (c.frontier 1).flatMap Configuration.next = []
      simp [h₁, List.flatMap_map, next]
    | succ k ih => exact congrArg (List.flatMap Configuration.next) ih
  change (∑' k, ENNReal.ofReal (c.postAt k A)) = _
  rw [tsum_eq_single 1]
  · simp [postAt_eq_sum_frontier, h₁, List.filter_map, List.map_map, Function.comp_def]
  · rintro (_ | _ | k) hk
    · simp [c, postAt_eq_sum_frontier, frontier]
    · exact (hk rfl).elim
    · simp [postAt_eq_sum_frontier, h₂]

/-- A measurement evaluates its postcondition after writing each outcome to the classical store.
The empty successor list of a blocked register contributes zero. -/
theorem PostH_measure {m k : ℕ} (r : Store → Fin k → Cell)
    (inst : ∀ σ, Function.Injective (r σ) → Instrument H H (Fin m))
    (upd : Fin m → Store → Store) (s : CQState Store H) (A : Store → Operator H) :
    (Configuration.mk (some (Command.measure r inst upd)) s).PostH A =
      ENNReal.ofReal (((measurementSuccessors r inst upd s).map
        (fun t => t.expectation (A t.store))).sum) :=
  PostH_of_step_terminals rfl A

end Configuration

/-- A QHL⁺ assertion is an effect on the whole memory for each classical store. -/
abbrev Assertion (Store : Type*) (H : Qudit) := Store → Set.Icc (0 : Operator H) 1

/-- An assertion is a positive observable at every store. -/
theorem Assertion.isPositive (A : Assertion Store H) (σ : Store) : (A σ : Operator H).IsPositive :=
  LinearMap.nonneg_iff_isPositive.mp (A σ).2.1

/-- The assertion collecting the entire trace at every classical store. -/
def Assertion.identity : Assertion Store H := fun _ =>
  ⟨1, LinearMap.nonneg_iff_isPositive.mpr LinearMap.isPositive_one, le_rfl⟩

/-- Restrict an effect to stores satisfying a classical predicate. -/
noncomputable def Assertion.mask (A : Assertion Store H) (φ : Store → Prop) : Assertion Store H :=
  open Classical in fun σ =>
    if φ σ then A σ else ⟨0, le_rfl, LinearMap.nonneg_iff_isPositive.mpr LinearMap.isPositive_one⟩

/-- The part of an assertion on which the Boolean guard holds. -/
noncomputable def Assertion.mand (A : Assertion Store H) (b : Store → Bool) : Assertion Store H :=
  A.mask fun σ => b σ = true

/-- The part of an assertion on which the Boolean guard fails. -/
noncomputable def Assertion.mandNot (A : Assertion Store H) (b : Store → Bool) :
    Assertion Store H := A.mask fun σ => b σ = false

/-- An assertion retains its effect at every store satisfying the mask. -/
theorem Assertion.mask_of_pos (A : Assertion Store H) {φ : Store → Prop} {σ : Store} (h : φ σ) :
    A.mask φ σ = A σ := by simp [mask, h]

/-- The effect vanishes at every store outside the mask. -/
theorem Assertion.mask_of_neg (A : Assertion Store H) {φ : Store → Prop} {σ : Store} (h : ¬ φ σ) :
    (A.mask φ σ : Operator H) = 0 := by simp [mask, h]

/-- A true guard retains the invariant in the body precondition. -/
theorem Assertion.mand_of_true (A : Assertion Store H) {b : Store → Bool} {σ : Store}
    (h : b σ = true) : A.mand b σ = A σ := A.mask_of_pos (φ := fun s => b s = true) h

/-- A false guard gives the zero effect in the body precondition. -/
theorem Assertion.mand_of_false (A : Assertion Store H) {b : Store → Bool} {σ : Store}
    (h : b σ = false) : (A.mand b σ : Operator H) = 0 :=
  A.mask_of_neg (φ := fun s => b s = true) (by simp [h])

/-- A false guard retains the invariant in the exit postcondition. -/
theorem Assertion.mandNot_of_false (A : Assertion Store H) {b : Store → Bool} {σ : Store}
    (h : b σ = false) : A.mandNot b σ = A σ := A.mask_of_pos (φ := fun s => b s = false) h

/-- A true guard gives the zero effect in the exit postcondition. -/
theorem Assertion.mandNot_of_true (A : Assertion Store H) {b : Store → Bool} {σ : Store}
    (h : b σ = true) : (A.mandNot b σ : Operator H) = 0 :=
  A.mask_of_neg (φ := fun s => b s = false) (by simp [h])

/-- The projector onto a unit state, used as a store-independent sharp assertion. -/
noncomputable def Assertion.pure (v : UnitState H) : Assertion Store H := fun _ =>
  let ρ := Density.pure v
  have hp : IsIdempotentElem ρ.op := Density.pure_mul_self v
  ⟨ρ.op, LinearMap.nonneg_iff_isPositive.mpr ρ.positive, LinearMap.le_def.mpr
    (LinearMap.IsSymmetricProjection.isPositive
      ⟨hp.one_sub, LinearMap.IsSymmetric.one.sub ρ.positive.isSymmetric⟩)⟩

/-- Total validity compares the initial expectation with the accumulated terminal expectation. -/
def validTot (A : Assertion Store H) (p : Command Store Cell H) (B : Assertion Store H) : Prop :=
  ∀ s : CQState Store H, ENNReal.ofReal (s.expectation (A s.store)) ≤
    (Configuration.mk (some p) s).PostH (fun σ => B σ)

/-- Partial validity includes the residual mass of the run in the upper bound. -/
def validPar (A : Assertion Store H) (p : Command Store Cell H) (B : Assertion Store H) : Prop :=
  ∀ s : CQState Store H, ENNReal.ofReal (s.expectation (A s.store)) ≤
    (Configuration.mk (some p) s).PostH (fun σ => B σ) +
      (Configuration.mk (some p) s).nonterminatingMass

/-- Every totally valid triple is partially valid. -/
theorem validTot.validPar {A B : Assertion Store H} {p : Command Store Cell H}
    (h : validTot A p B) : validPar A p B := fun s => (h s).trans le_self_add

/-- Total validity of the identity triple means that all input mass terminates. -/
theorem validTot_identity_iff (p : Command Store Cell H) :
    validTot Assertion.identity p Assertion.identity ↔
      ∀ s : CQState Store H, (Configuration.mk (some p) s).terminatingMass = s.mass := by
  simp only [validTot, Assertion.identity, CQState.expectation_one, ENNReal.ofReal_coe_nnreal,
    Configuration.PostH_one]
  exact forall_congr' fun s => ⟨fun h => le_antisymm (Configuration.terminatingMass_le _) h,
    fun h => h.ge⟩

/-- Partial validity of the identity triple accounts for the whole input, including blocked mass. -/
theorem validPar_identity (p : Command Store Cell H) :
    validPar Assertion.identity p Assertion.identity := by
  intro s
  simpa only [Assertion.identity, CQState.expectation_one, ENNReal.ofReal_coe_nnreal,
    Configuration.PostH_one] using
    (Configuration.terminatingMass_add_nonterminatingMass (Configuration.mk (some p) s)).symm.le

end QuantumProgram
