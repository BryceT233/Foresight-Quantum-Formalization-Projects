/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/
module

public import FQFP.Algebra.Lie.BCH.Compatibility.SymmetricTerms
public import FQFP.Algebra.Lie.BCH.SuzukiTerms
public import FQFP.Algebra.Lie.BCH.SuzukiGradedRecurrence

/-!
# Hall and right-nested presentations of the Suzuki quintic

The coefficients here use the paper's `E₃ = [b,a]` convention. The identity
is a polynomial identity in every real associative algebra.
-/

@[expose] public noncomputable section

namespace FQFP.BCH

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The paper's cubic Strang Hall term over a real associative algebra. -/
def suzukiStrangCubic {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) : A :=
  let c := ⁅b, a⁆
  (-1 / 24 : ℝ) • ⁅c, a⁆ + (-1 / 12 : ℝ) • ⁅c, b⁆

/-- The paper's six-element quintic Strang Hall term over a real associative algebra. -/
def suzukiStrangQuintic {A : Type*} [Ring A] [Algebra ℝ A] (a b : A) : A :=
  let c := ⁅b, a⁆
  let cx := ⁅c, a⁆
  let cy := ⁅c, b⁆
  let cxx := ⁅cx, a⁆
  let cxy := ⁅cx, b⁆
  let cyy := ⁅cy, b⁆
  (1 / 5760 : ℝ) •
    (7 • ⁅cxx, a⁆ + 28 • ⁅cxx, b⁆ + 32 • ⁅cxy, b⁆ +
      8 • ⁅cyy, b⁆ + 12 • ⁅cx, c⁆ - 16 • ⁅cy, c⁆)

/-- The coefficient of the Strang quintic `D₅` in the Suzuki logarithm. -/
def suzukiKappa (u : ℝ) : ℝ := (-6 + 52 * u - 123 * u ^ 2) / 75

/-- The coefficient of `[G,[G,C₃]]` in the Suzuki logarithm. -/
def suzukiLambda (u : ℝ) : ℝ := (-3 + 26 * u - 24 * u ^ 2) / 900

/-- The six displayed right-nested coefficients, in the paper's order. -/
def suzukiRightCoeff (u : ℝ) : Fin 6 → ℝ :=
  ![(-6 + 52 * u + 127 * u ^ 2) / 144000,
    (-36 + 312 * u + 12 * u ^ 2) / 144000,
    (-72 + 624 * u - 976 * u ^ 2) / 144000,
    (12 - 104 * u + 496 * u ^ 2) / 144000,
    (36 - 312 * u + 1488 * u ^ 2) / 144000,
    (-24 + 208 * u + 8 * u ^ 2) / 144000]

/-- Index translation from the paper's six words to the eight-element family. -/
def suzukiRightIndex : Fin 6 → Fin 8 := ![0, 1, 3, 4, 5, 7]

/-- The Hall elements `E₉` through `E₁₄`, with `E₃ = [b,a]`. -/
def suzukiHallElement {A : Type*} [Ring A] (a b : A) : Fin 6 → A :=
  let c := ⁅b, a⁆
  let cx := ⁅c, a⁆
  let cy := ⁅c, b⁆
  let cxx := ⁅cx, a⁆
  let cxy := ⁅cx, b⁆
  let cyy := ⁅cy, b⁆
  ![⁅cxx, a⁆, ⁅cxx, b⁆, ⁅cxy, b⁆, ⁅cyy, b⁆, ⁅cx, c⁆, ⁅cy, c⁆]

/-- The paper's six Hall coefficients, with common denominator `144000`. -/
def suzukiHallCoeff (u : ℝ) : Fin 6 → ℝ :=
  ![(6 - 52 * u - 127 * u ^ 2) / 144000,
    (24 - 208 * u - 508 * u ^ 2) / 144000,
    (36 - 312 * u - 512 * u ^ 2) / 144000,
    (24 - 208 * u - 8 * u ^ 2) / 144000,
    (36 - 312 * u - 12 * u ^ 2) / 144000,
    (72 - 624 * u + 976 * u ^ 2) / 144000]

/-- Every displayed right-nested coefficient agrees with the existing API. -/
theorem suzukiRightCoeff_eq (u : ℝ) (i : Fin 6) :
    suzukiRightCoeff u i = suzukiQuinticCoeff u (suzukiRightIndex i) := by
  fin_cases i <;> simp [suzukiRightCoeff, suzukiRightIndex, suzukiQuinticCoeff] <;> ring

/-- The two redundant family slots have exactly zero coefficient. -/
theorem suzukiQuinticCoeff_zero_slots (u : ℝ) :
    suzukiQuinticCoeff u 2 = 0 ∧ suzukiQuinticCoeff u 6 = 0 := by
  simp [suzukiQuinticCoeff]

/-- The paper's two-part Hall expression for the Suzuki quintic. -/
def suzukiHallQuinticTerm {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (u : ℝ) : A :=
  suzukiKappa u • suzukiStrangQuintic a b +
    suzukiLambda u • ⁅a + b, ⁅a + b, suzukiStrangCubic a b⁆⁆

/-- The two-part expression has exactly the six Hall coefficients from the paper. -/
theorem suzukiHallQuinticTerm_eq_hallSum {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (u : ℝ) :
    suzukiHallQuinticTerm a b u =
      ∑ i : Fin 6, suzukiHallCoeff u i • suzukiHallElement a b i := by
  simp only [suzukiHallQuinticTerm, suzukiHallCoeff, suzukiHallElement,
    suzukiKappa, suzukiLambda, suzukiStrangQuintic,
    suzukiStrangCubic, Fin.sum_univ_succ, Ring.lie_def,
    mul_sub, sub_mul, ← mul_assoc]
  norm_num
  noncomm_ring
  module

/-- The existing eight-commutator term is the paper's Hall quintic expression. -/
theorem suzukiQuinticTerm_eq_hall {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (u : ℝ) :
    suzukiQuinticTerm a b u = suzukiHallQuinticTerm a b u := by
  simp only [suzukiQuinticTerm, suzukiQuinticCoeff, suzukiHallQuinticTerm,
    suzukiKappa, suzukiLambda, suzukiStrangQuintic,
    suzukiStrangCubic, binaryQuinticCommutator,
    Fin.sum_univ_succ, Matrix.cons_val_zero,
    Ring.lie_def, mul_sub, sub_mul, ← mul_assoc]
  norm_num
  noncomm_ring
  module

/-- The existing quintic is the paper's six-element Hall sum. -/
theorem suzukiQuinticTerm_eq_hallSum {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (u : ℝ) :
    suzukiQuinticTerm a b u =
      ∑ i : Fin 6, suzukiHallCoeff u i • suzukiHallElement a b i := by
  rw [suzukiQuinticTerm_eq_hall, suzukiHallQuinticTerm_eq_hallSum]

/-- The existing eight-element sum equals the six displayed right-nested terms. -/
theorem suzukiQuinticTerm_eq_rightSum {A : Type*} [Ring A] [Algebra ℝ A]
    (a b : A) (u : ℝ) :
    suzukiQuinticTerm a b u =
      ∑ i : Fin 6, suzukiRightCoeff u i •
        binaryQuinticCommutator a b (suzukiRightIndex i) := by
  simp [suzukiQuinticTerm, suzukiRightCoeff, suzukiRightIndex,
    suzukiQuinticCoeff, Fin.sum_univ_succ]
  module

end FQFP.BCH
