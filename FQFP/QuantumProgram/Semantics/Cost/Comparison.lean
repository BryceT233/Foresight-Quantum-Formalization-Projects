/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/
module

public import FQFP.QuantumProgram.Semantics.Cost.Bounds

/-!
# Comparing prices and computing exact sequential costs

Pointwise comparison of primitive prices passes to expected costs on every execution.
For exact costs, the trace reaching the second command determines how much of its price
is charged. Lossless finite sequences therefore add their exact prices with multiplicity.
-/

@[expose] public section

open Qudit
open scoped NNReal ENNReal

namespace QuantumProgram

variable {H : Qudit} {Store Cell : Type*}

/-- Models are ordered pointwise on the prices for each kind of primitive operation. -/
instance : PartialOrder (CostModel H) where
  le x y := x.assignmentCost ≤ y.assignmentCost ∧ x.channelCost ≤ y.channelCost ∧
    x.unitaryCost ≤ y.unitaryCost ∧ ∀ n, @x.measurementCost n ≤ @y.measurementCost n
  le_refl _ := ⟨le_rfl, le_rfl, le_rfl, fun _ => le_rfl⟩
  le_trans _ _ _ h k := by
    obtain ⟨ha, hc, hu, hm⟩ := h
    obtain ⟨ka, kc, ku, km⟩ := k
    exact ⟨ha.trans ka, hc.trans kc, hu.trans ku, fun n => (hm n).trans (km n)⟩
  le_antisymm x y h k := by
    obtain ⟨ha, hc, hu, hm⟩ := h
    obtain ⟨ha', hc', hu', hm'⟩ := k
    cases x
    cases y
    congr
    · exact le_antisymm ha ha'
    · exact le_antisymm hc hc'
    · exact le_antisymm hu hu'
    · funext n
      exact le_antisymm (hm n) (hm' n)

/-- Raising primitive prices can only increase the expected cost, including on diverging runs. -/
theorem expectedCost_mono {x y : CostModel H} (h : x ≤ y) (p : Command Store Cell H) :
    expectedCost x p ≤ expectedCost y p := by
  obtain ⟨ha, hc, hu, hm⟩ := h
  induction p with
  | skip => exact le_rfl
  | assign f => exact fun _ => mul_le_mul_left (Nat.cast_le.mpr ha) _
  | channel f => exact fun s => mul_le_mul_left (Nat.cast_le.mpr (hc (f s.store))) _
  | unitary r U =>
    intro s
    classical
    by_cases hr : Function.Injective (r s.store)
    · simp only [expectedCost, dite_eq_left hr]
      exact mul_le_mul_left (Nat.cast_le.mpr (hu (U s.store hr))) _
    · simp [expectedCost, hr]
  | measure r I upd =>
    intro s
    classical
    by_cases hr : Function.Injective (r s.store)
    · simp only [expectedCost, dite_eq_left hr]
      exact mul_le_mul_left (Nat.cast_le.mpr (hm _ (I s.store hr))) _
    · simp [expectedCost, hr]
  | seq p q hp hq => exact fun s => add_le_add (hp s) (p.outputWeight_mono hq s)
  | ite b p q hp hq =>
    intro s
    cases hb : b s.store <;> simp [expectedCost_ite, hb, hp s, hq s]
  | whileDo b p hp =>
    exact fun s => tsum_le_tsum fun n => whileEntryWeight_mono b p (fun t _ => hp t) n s

/-- A budget remains valid if the prices charged to the same program are reduced. -/
theorem CostBound.of_model_le {x y : CostModel H} {p : Command Store Cell H} {a : ℝ≥0}
    (hp : CostBound y p a) (h : x ≤ y) : CostBound x p a :=
  fun s => (expectedCost_mono h p s).trans (hp s)

/-- An exact continuation price applies only to trace returned by the first command. -/
theorem expectedCost_seq_of_eq_mul_mass (model : CostModel H) (p : Command Store Cell H)
    {q : Command Store Cell H} {a : ℝ≥0∞}
    (hq : ∀ t : CQState Store H, expectedCost model q t = a * t.mass) (s : CQState Store H) :
    expectedCost model (p.seq q) s = expectedCost model p s +
      a * (Configuration.mk (some p) s).terminatingMass :=
  expectedCost_seq_eq_add_mul_terminatingMass model p s (fun _ t _ => hq t)

/-- A list of lossless commands charges the sum of their exact prices on the full input trace. -/
theorem expectedCost_forList_eq_sum {ι : Type*} (model : CostModel H) (l : List ι)
    (body : ι → Command Store Cell H) (price : ι → ℝ≥0∞)
    (hl : ∀ i ∈ l, Lossless (body i))
    (hc : ∀ i ∈ l, ∀ t : CQState Store H, expectedCost model (body i) t = price i * t.mass)
    (s : CQState Store H) :
    expectedCost model (.forList l body) s = (l.map price).sum * s.mass := by
  induction l generalizing s with
  | nil => simp [expectedCost]
  | cons i l ih =>
    have htail := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      (fun j hj => hc j (List.mem_cons_of_mem _ hj))
    rw [Command.forList_cons, expectedCost_seq_of_eq_mul_mass model _ htail,
      hl i List.mem_cons_self s, hc i List.mem_cons_self s, List.map_cons, List.sum_cons, add_mul]

/-- A lossless finite iteration charges a fixed price once per list occurrence. -/
theorem expectedCost_forList_eq_length_mul {ι : Type*} (model : CostModel H) (l : List ι)
    (body : ι → Command Store Cell H) (a : ℝ≥0∞) (hl : ∀ i ∈ l, Lossless (body i))
    (hc : ∀ i ∈ l, ∀ t : CQState Store H, expectedCost model (body i) t = a * t.mass)
    (s : CQState Store H) :
    expectedCost model (.forList l body) s = (l.length * a) * s.mass := by
  simpa [List.map_const', nsmul_eq_mul] using
    expectedCost_forList_eq_sum model l body (fun _ => a) hl hc s

end QuantumProgram
