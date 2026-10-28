/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Analysis.Normed.Algebra.ProductFormula.SuzukiParameter

/-!
# Finite arithmetic modulo the Suzuki cubic

The three coordinates represent `c₀ + c₁ u + c₂ u²`. Multiplication reduces
the cubic and quartic terms using `60u³ - 48u² + 12u - 1 = 0`.
The evaluation theorem makes the finite calculation valid for the canonical
real parameter; no field structure on the quotient is asserted.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

/-- Three rational coordinates for a polynomial reduced modulo the Suzuki cubic. -/
structure SuzukiCubicCoord where
  /-- Constant coordinate. -/
  c0 : ℚ
  /-- Coefficient of `u`. -/
  c1 : ℚ
  /-- Coefficient of `u²`. -/
  c2 : ℚ
  deriving DecidableEq, Repr

namespace SuzukiCubicCoord

/-- Evaluate a reduced coordinate triple at a real parameter. -/
def eval (x : SuzukiCubicCoord) (u : ℝ) : ℝ :=
  x.c0 + x.c1 * u + x.c2 * u ^ 2

/-- Coordinatewise addition. -/
def add (x y : SuzukiCubicCoord) : SuzukiCubicCoord :=
  ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩

/-- Rational scalar multiplication of the three coordinates. -/
def scale (q : ℚ) (x : SuzukiCubicCoord) : SuzukiCubicCoord :=
  ⟨q * x.c0, q * x.c1, q * x.c2⟩

/-- Multiplication followed by reduction of `u³` and `u⁴`. -/
def mul (x y : SuzukiCubicCoord) : SuzukiCubicCoord :=
  let z0 := x.c0 * y.c0
  let z1 := x.c0 * y.c1 + x.c1 * y.c0
  let z2 := x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0
  let z3 := x.c1 * y.c2 + x.c2 * y.c1
  let z4 := x.c2 * y.c2
  ⟨z0 + z3 / 60 + z4 / 75,
    z1 - z3 / 5 - 43 * z4 / 300,
    z2 + 4 * z3 / 5 + 11 * z4 / 25⟩

/-- Evaluation preserves coordinate addition. -/
theorem eval_add (x y : SuzukiCubicCoord) (u : ℝ) :
    eval (add x y) u = eval x u + eval y u := by
  simp only [eval, add, Rat.cast_add]
  ring

/-- Evaluation preserves rational scalar multiplication. -/
theorem eval_scale (q : ℚ) (x : SuzukiCubicCoord) (u : ℝ) :
    eval (scale q x) u = (q : ℝ) * eval x u := by
  simp only [eval, scale, Rat.cast_mul]
  ring

/-- Reduction of the cubic monomial at a root of the Suzuki relation. -/
private theorem cube_reduce (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) :
    u ^ 3 = (1 : ℝ) / 60 - u / 5 + 4 * u ^ 2 / 5 := by
  linarith only [hu]

/-- Reduction of the quartic monomial at a root of the Suzuki relation. -/
private theorem fourth_reduce (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) :
    u ^ 4 = (1 : ℝ) / 75 - 43 * u / 300 + 11 * u ^ 2 / 25 := by
  have h := congrArg (fun z : ℝ ↦ z * u) (cube_reduce u hu)
  linear_combination h + (4 / 5 : ℝ) * cube_reduce u hu

/-- Finite multiplication evaluates to ordinary multiplication at any cubic root. -/
theorem eval_mul (x y : SuzukiCubicCoord) (u : ℝ)
    (hu : 60 * u ^ 3 - 48 * u ^ 2 + 12 * u - 1 = 0) :
    eval (mul x y) u = eval x u * eval y u := by
  have h3 := cube_reduce u hu
  have h4 := fourth_reduce u hu
  simp only [eval, mul, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat]
  -- The remaining identity is polynomial arithmetic in the five raw products.
  linear_combination
    -((x.c1 : ℝ) * y.c2 + (x.c2 : ℝ) * y.c1) * h3 -
      (x.c2 : ℝ) * y.c2 * h4

/-- Multiplication in the finite coordinates is sound at `suzukiP`. -/
theorem eval_mul_suzukiP (x y : SuzukiCubicCoord) :
    eval (mul x y) suzukiP = eval x suzukiP * eval y suzukiP :=
  eval_mul x y suzukiP suzukiP_cubic_relation

end SuzukiCubicCoord

end FQFP.BCH
