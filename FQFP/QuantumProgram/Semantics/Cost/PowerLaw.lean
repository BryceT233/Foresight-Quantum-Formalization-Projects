/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/QuantumHoareLogic/ResourceCounting/PowerLawCost.lean: PowerLawCost,
its lexicographic order and the characterization by eventual comparison of evaluations.
Here sizes and evaluations are nonnegative reals, and sizes can grow along any nontrivial filter.
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

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Order.Lex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power-law cost functions

A power law records both the exponent and its leading coefficient. Eventual order compares
larger exponents first, even when the smaller exponent has the larger coefficient at size one.
-/

@[expose] public section

open Filter
open scoped NNRat NNReal

namespace QuantumProgram

/-- A bound `coefficient * size ^ exponent` with canonical zero and exact rational parameters. -/
@[ext] structure PowerLawCost where
  /-- Exponent of the problem size. -/
  exponent : ℚ≥0
  /-- Leading coefficient. -/
  coefficient : ℚ≥0
  /-- The zero function has exponent zero. -/
  exponent_eq_zero : coefficient = 0 → exponent = 0
  deriving DecidableEq

namespace PowerLawCost

/-- Construct a power law from its coefficient and exponent, normalizing a zero coefficient. -/
def monomial (c a : ℚ≥0) : PowerLawCost :=
  ⟨if c = 0 then 0 else a, c, fun h => ite_eq_left h⟩

/-- Evaluate the bound in the scalar type accepted by `CostBound`. -/
noncomputable def eval (m : PowerLawCost) (size : ℝ≥0) : ℝ≥0 :=
  (m.coefficient : ℝ≥0) * size ^ (m.exponent : ℝ)

/-- Normalizing the coefficient preserves the intended value, including at size zero. -/
theorem eval_monomial (c a : ℚ≥0) (size : ℝ≥0) :
    (monomial c a).eval size = (c : ℝ≥0) * size ^ (a : ℝ) := by
  by_cases hc : c = 0 <;> simp [eval, monomial, hc]

/-- Compare the exponent first and then the leading coefficient. -/
def toLex (m : PowerLawCost) : ℚ≥0 ×ₗ ℚ≥0 := _root_.toLex (m.exponent, m.coefficient)

/-- The lexicographic key retains both parameters. -/
theorem toLex_injective : Function.Injective toLex := by
  rintro ⟨_, _, _⟩ ⟨_, _, _⟩ h
  cases h
  rfl

instance : LinearOrder PowerLawCost := LinearOrder.lift' toLex toLex_injective

/-- Strict comparison of the rational parameters. -/
theorem lt_iff {m k : PowerLawCost} :
    m < k ↔ m.exponent < k.exponent ∨ m.exponent = k.exponent ∧ m.coefficient < k.coefficient :=
  Prod.Lex.lt_iff (x := m.toLex) (y := k.toLex)

/-- Non-strict comparison of the rational parameters. -/
theorem le_iff {m k : PowerLawCost} :
    m ≤ k ↔ m.exponent < k.exponent ∨ m.exponent = k.exponent ∧ m.coefficient ≤ k.coefficient :=
  Prod.Lex.le_iff (x := m.toLex) (y := k.toLex)

/-- Strictly ordered power laws have strictly ordered values at sufficiently large sizes. -/
theorem eventually_eval_lt_of_lt {m k : PowerLawCost} (h : m < k) :
    ∀ᶠ x in atTop, m.eval x < k.eval x := by
  rcases lt_iff.mp h with ha | ⟨ha, hc⟩
  · have hc : 0 < k.coefficient :=
      pos_iff_ne_zero.mpr fun hz => (k.exponent_eq_zero hz ▸ ha).not_ge zero_le
    have hd : 0 < (k.exponent : ℝ) - (m.exponent : ℝ) := sub_pos.mpr (by exact_mod_cast ha)
    have hc' : 0 < (k.coefficient : ℝ≥0) := by exact_mod_cast hc
    filter_upwards [(NNReal.tendsto_rpow_atTop hd).eventually_gt_atTop
      ((m.coefficient : ℝ≥0) / k.coefficient), eventually_gt_atTop (0 : ℝ≥0)] with x hx hx₀
    have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hc').mp hx)
      (NNReal.rpow_pos (p := (m.exponent : ℝ)) hx₀)
    simpa only [eval, mul_comm (x ^ ((k.exponent : ℝ) - (m.exponent : ℝ))), mul_assoc,
      ← NNReal.rpow_add hx₀.ne', add_sub_cancel] using hh
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with x hx
    simp only [eval, ha]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hc) (NNReal.rpow_pos hx)

variable {ι : Type*} {l : Filter ι} [NeBot l] {size : ι → ℝ≥0} {m k : PowerLawCost}

/-- Strict comparison is equivalent to eventual strict inequality along any sizes tending to
infinity, including natural problem sizes. -/
theorem lt_iff_eventually_eval_lt (hs : Tendsto size l atTop) :
    m < k ↔ ∀ᶠ i in l, m.eval (size i) < k.eval (size i) := by
  refine ⟨fun h => hs.eventually (eventually_eval_lt_of_lt h), fun h => ?_⟩
  rcases lt_trichotomy m k with hlt | rfl | hgt
  · exact hlt
  · obtain ⟨i, hi⟩ := h.exists
    exact (lt_irrefl _ hi).elim
  · obtain ⟨i, hi, hi'⟩ := (h.and (hs.eventually (eventually_eval_lt_of_lt hgt))).exists
    exact (lt_asymm hi hi').elim

/-- The lexicographic order is exactly eventual domination along sizes tending to infinity. -/
theorem le_iff_eventually_eval_le (hs : Tendsto size l atTop) :
    m ≤ k ↔ ∀ᶠ i in l, m.eval (size i) ≤ k.eval (size i) := by
  refine ⟨fun h => ?_, fun h => le_of_not_gt fun hgt => ?_⟩
  · rcases h.lt_or_eq with hlt | rfl
    · exact ((lt_iff_eventually_eval_lt hs).mp hlt).mono fun _ hi => hi.le
    · exact .of_forall fun _ => le_rfl
  · obtain ⟨i, hi, hi'⟩ := (h.and ((lt_iff_eventually_eval_lt hs).mp hgt)).exists
    exact hi.not_gt hi'

/-- A single power law bounding the sum at sizes at least one. -/
def sumBound (m k : PowerLawCost) : PowerLawCost :=
  monomial (m.coefficient + k.coefficient) (max m.exponent k.exponent)

/-- The sum of the leading coefficients bounds both terms at the larger exponent. -/
theorem add_eval_le_sumBound (m k : PowerLawCost) {x : ℝ≥0} (hx : 1 ≤ x) :
    m.eval x + k.eval x ≤ (m.sumBound k).eval x := by
  rw [sumBound, eval_monomial, NNRat.cast_add, add_mul]
  apply add_le_add <;> apply mul_le_mul_right <;> apply NNReal.rpow_le_rpow_of_exponent_le hx
  · exact_mod_cast le_max_left m.exponent k.exponent
  · exact_mod_cast le_max_right m.exponent k.exponent

/-- The pointwise product of two power laws. -/
def product (m k : PowerLawCost) : PowerLawCost :=
  monomial (m.coefficient * k.coefficient) (m.exponent + k.exponent)

/-- Products evaluate exactly, including at size zero. -/
theorem eval_product (m k : PowerLawCost) (x : ℝ≥0) :
    (m.product k).eval x = m.eval x * k.eval x := by
  rw [product, eval_monomial, NNRat.cast_mul, NNRat.cast_add,
    NNReal.rpow_add_of_nonneg x (by positivity) (by positivity)]
  simp only [eval]
  ac_rfl

end PowerLawCost

end QuantumProgram
