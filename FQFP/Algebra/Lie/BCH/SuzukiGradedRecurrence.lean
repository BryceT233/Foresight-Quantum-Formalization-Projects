/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.SuzukiCubicArithmetic

/-!
# The graded five-coordinate Suzuki recurrence

This file records the paper's BCH update as finite scalar arithmetic. Its
five-step result is checked exactly at the canonical cubic parameter.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- Coefficients of `G`, `C₃`, `[G,C₃]`, `D₅`, and `[G,[G,C₃]]`. -/
structure SuzukiGradedCoeff where
  /-- Coefficient of `G`. -/
  a : ℝ
  /-- Coefficient of `C₃`. -/
  b : ℝ
  /-- Coefficient of `[G,C₃]`. -/
  c : ℝ
  /-- Coefficient of `D₅`. -/
  d : ℝ
  /-- Coefficient of `[G,[G,C₃]]`. -/
  e : ℝ

namespace SuzukiGradedCoeff

@[ext] theorem ext {s t : SuzukiGradedCoeff} (ha : s.a = t.a)
    (hb : s.b = t.b) (hc : s.c = t.c) (hd : s.d = t.d)
    (he : s.e = t.e) : s = t := by
  cases s
  cases t
  simp_all

/-- The paper's graded update on appending a Strang stage of weight `q`. -/
def append (s : SuzukiGradedCoeff) (q : ℝ) : SuzukiGradedCoeff :=
  let delta := s.a * q ^ 3 - s.b * q
  ⟨s.a + q, s.b + q ^ 3, s.c + delta / 2, s.d + q ^ 5,
    s.e - s.c * q / 2 + (s.a - q) * delta / 12⟩

/-- The zero initial coefficient state. -/
def zero : SuzukiGradedCoeff := ⟨0, 0, 0, 0, 0⟩

/-- The five symmetric Suzuki stage weights, evaluated by the scalar recurrence. -/
def fiveStages (u : ℝ) : SuzukiGradedCoeff :=
  (((((zero.append u).append u).append (1 - 4 * u)).append u).append u)

/-- The two rational functions that multiply `D₅` and `[G,[G,C₃]]`. -/
def target (u : ℝ) : SuzukiGradedCoeff :=
  ⟨1, 0, 0, (-6 + 52 * u - 123 * u ^ 2) / 75,
    (-3 + 26 * u - 24 * u ^ 2) / 900⟩

/-- Exact five-stage recurrence at any root of the Suzuki cubic. -/
theorem fiveStages_eq_target (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) :
    fiveStages u = target u := by
  have h4 := congrArg (fun z : ℝ ↦ z * u) hu
  have h5 := congrArg (fun z : ℝ ↦ z * u ^ 2) hu
  have h6 := congrArg (fun z : ℝ ↦ z * u ^ 3) hu
  ext
  · dsimp [fiveStages, target, append, zero]
    ring
  · dsimp [fiveStages, target, append, zero]
    nlinarith only [hu]
  · dsimp [fiveStages, target, append, zero]
    nlinarith only [hu, h4]
  · dsimp [fiveStages, target, append, zero]
    nlinarith only [hu, h4, h5]
  · dsimp [fiveStages, target, append, zero]
    nlinarith only [hu, h4, h5, h6]

/-- The canonical real Suzuki parameter yields exactly the paper's five coordinates. -/
theorem fiveStages_suzukiP_eq_target :
    fiveStages suzukiP = target suzukiP :=
  fiveStages_eq_target suzukiP suzukiP_cubic_relation

end SuzukiGradedCoeff

end FQFP.BCH
