/-
Copyright (c) 2026 Shanghai Fuxi Quantum Technology Co., Ltd.. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FQFP authors
-/

/-
google-deepmind/formal-quantum-computation @ 489edc7039aa4cdded53724b39ea90e33d2c88b4
QuantumComputation/Maths/Tsum.lean: ENNReal.tsum_eq_mul_inv_of_succ and its power formula.
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

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric bounds from one-step ratios in the extended nonnegative reals
-/

public section

namespace ENNReal

variable {f : ℕ → ℝ≥0∞} {q : ℝ≥0∞}

/-- Iterating a one-step ratio bound gives a geometric bound at every index. -/
theorem le_pow_mul_of_succ_le (h : ∀ n, f (n + 1) ≤ q * f n) (n : ℕ) :
    f n ≤ q ^ n * f 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ', mul_assoc] using (h n).trans (mul_le_mul_right ih q)

/-- A sequence with fixed successive ratio is geometric from its initial value. -/
theorem eq_pow_mul_of_succ_eq (h : ∀ n, f (n + 1) = q * f n) (n : ℕ) :
    f n = q ^ n * f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [h n, ih, pow_succ', mul_assoc]

/-- Sum bound for a sequence whose successive terms contract by at most the given factor. -/
theorem tsum_le_mul_inv_of_succ_le (h : ∀ n, f (n + 1) ≤ q * f n) :
    ∑' n, f n ≤ f 0 * (1 - q)⁻¹ := by
  simpa only [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm (1 - q)⁻¹] using
    _root_.tsum_le_tsum (le_pow_mul_of_succ_le h)

/-- Geometric sum for a fixed successive ratio, including zero initial mass and ratio one. -/
theorem tsum_eq_mul_inv_of_succ (h : ∀ n, f (n + 1) = q * f n) :
    ∑' n, f n = f 0 * (1 - q)⁻¹ := by
  rw [tsum_congr (eq_pow_mul_of_succ_eq h), ENNReal.tsum_mul_right,
    ENNReal.tsum_geometric, mul_comm]

end ENNReal
